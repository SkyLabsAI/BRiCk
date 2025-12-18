(*
 * Copyright (c) 2021-2025 BlueRock Security, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)
Require Import iris.bi.lib.fractional.
Require Import skylabs.iris.extra.proofmode.proofmode.
Require Import skylabs.iris.extra.bi.errors.
Require Import skylabs.lang.cpp.syntax.
Require Import skylabs.lang.cpp.semantics.
Require Import skylabs.iris.extra.bi.spec.frac_splittable.
Require Import skylabs.iris.extra.bi.spec.nary_classes.
Require Import skylabs.lang.cpp.logic.pred.
Require Import skylabs.lang.cpp.logic.path_pred.
Require Import skylabs.lang.cpp.logic.heap_pred.
Require Import skylabs.lang.cpp.logic.destroy.
Require Import skylabs.lang.cpp.logic.initializers.
Require Import skylabs.lang.cpp.logic.dispatch.
Require Import skylabs.lang.cpp.logic.wp.
Require Import skylabs.lang.cpp.logic.call.
Require Import skylabs.lang.cpp.logic.translation_unit.

Require Import skylabs.lang.cpp.logic.const.

Notation Talign_val_t := "enum std::align_val_t"%cpp_type.
Notation Tdestroying_delete_t := "std::destroying_delete_t"%cpp_type.

(* The type of the information in the AST about the default delete operator
 *)
#[local] Notation DEFAULT_DELETE := (name)%type (only parsing).

Import linearity.

(* TODO: upstream? *)
Section with_prop.
  Context {PROP : bi}.
  Lemma exists_frame {T} (P P' : T -> PROP) :
    (∀ x, P x -* P' x) |-- (∃ x, P x) -* (∃ x, P' x).
  Proof.
    iIntros "X Y"; iDestruct "Y" as (x) "Y"; iExists x; iApply "X"; eauto.
  Qed.
  Lemma forall_frame {T} (P P' : T -> PROP) :
    (∀ x, P x -* P' x) |-- (∀ x, P x) -* (∀ x, P' x).
  Proof.
    iIntros "X Y" (?); iApply "X"; iApply "Y".
  Qed.
  Lemma sep_frame (Q P P' : PROP) :
    (P -* P') |-- (Q ** P) -* (Q ** P').
  Proof.
    iIntros "X [$ Y]"; iApply "X"; eauto.
  Qed.
  Lemma wand_frame (Q P P' : PROP) :
    (P -* P') |-- (Q -* P) -* (Q -* P').
  Proof.
    iIntros "X Y Z"; iApply "X"; iApply "Y"; eauto.
  Qed.
End with_prop.
Ltac do_frame :=
  repeat match goal with
    | |- environments.envs_entails _ ?X =>
        match X with
        | _ => iIntros (?)
        | ((_ ** _) -* (_ ** _)) => iApply sep_frame
        | ((_ -* _) -* (_ -* _)) => iApply wand_frame
        | ((bi_forall _) -* (bi_forall _)) => iApply forall_frame; iIntros (?)
        | ((bi_exist _) -* (bi_exist _)) => iApply exists_frame; iIntros (?)
        | _ => iApply wp_fptr_frame; iIntros (?)
        | _ => iApply interp_frame
        | _ => iApply operand_receive_frame
        end; eauto
    end.
(* END: upstream *)


(* TODO: refactor this *)
Module delete_operator.
  (** A structured representation of the supported <<operator delete>> types.
      See [type_for] to see the way this type maps to types.
   *)
  Record t : Set := mk
    { destroying : option name (* [Some T] means <<operator delete(T*, std::destroying_delete_t)>> *)
    ; size_arg : bool
    ; align_arg : bool
    }.

  (** The encoding of <<operator delete(void* )>> *)
  Definition default : t := mk None false false.

  (** The type of the delete operator. *)
  Definition type_for (d : t) : type :=
    let args :=
      if d.(align_arg) is false then [] else [Talign_val_t]
    in
    let args :=
      if d.(size_arg) is false then args else Tsize_t :: args
    in
    let args :=
      if d.(destroying) is Some type_name then Tptr (Tnamed type_name) :: args
      else "void*"%cpp_type :: args
    in
    Tfunction (FunctionType Tvoid args).

  #[local]
  Definition get_destroying {T} (k : list type -> option T) (args : list type) : option (option name * T) :=
    match args with
    | Tptr (Tnamed nm) :: t :: rest =>
        let is_destroying_delete_t t := bool_decide (t = Tdestroying_delete_t) in
        if is_destroying_delete_t t then
          pair (Some nm) <$> k rest
        else None
    | Tptr Tvoid :: rest => pair None <$> k rest
    | _ => None
    end.
  #[local]
  Definition get_size_t {T} (k : list type -> option T) (args : list type) : option (bool * T) :=
    match args with
    | t :: rest =>
        let is_size_t t := bool_decide (t = Tsize_t) in
        if is_size_t t then pair true <$> k rest
        else pair false <$> k args
    | _ => pair false <$> k args
    end.
  #[local]
  Definition get_align_t {T} (k : list type -> option T) (args : list type) : option (bool * T) :=
    match args with
    | t :: rest =>
        let is_align_val t := bool_decide (t = Talign_val_t) in
        if is_align_val t then pair true <$> k rest
        else pair false <$> k args
    | _ => pair false <$> k args
    end.

  (** Given the type of an <<operator delete>> (or <<operator delete[]>>) type,
      determine the information that it needs to be invoked with *)
  Definition classify (ty : type) : option delete_operator.t :=
    match ty with
    | Tfunction ft =>
        if bool_decide (ft.(ft_return) = "void"%cpp_type) then
          match get_destroying (get_size_t (get_align_t Some)) ft.(ft_params) with
          | Some (destroy, (sz, (al, []))) => Some $ mk destroy sz al
          | _ => None
          end
        else None
    | _ => None
    end.

  #[local] Definition with_delete (tu : translation_unit) (nm : obj_name)
    : option (obj_name * delete_operator.t) :=
    pair nm <$> (tu.(symbols) !! nm >>= fun del_fn => delete_operator.classify (type_of_value del_fn)).

  #[local] Definition delete_for_named (tu : translation_unit) (default_delete : DEFAULT_DELETE)
    (cls : name) : option (obj_name * delete_operator.t) :=
    match tu.(types) !! cls with
    | Some (Gstruct s) =>
        with_delete tu $ stdpp.option.default default_delete s.(s_delete)
    | Some (Gunion u) =>
        with_delete tu $ stdpp.option.default default_delete u.(u_delete)
    | Some (Genum _ _) =>
        with_delete tu default_delete
    | _ => None
    end.

  (** The <<operator delete>> that is used when deleting a **complete object**
      of type <<ty>>. [default] is the default delete operator used to delete
      the object if there is no type-specific override, e.g.
      <<T::operator delete(...)>>.

      To delete an array of type <<ety>>, <<ty>> should be <<Tincomplete_array ety>>.
   *)
  Definition delete_for (tu : translation_unit) (default_delete : DEFAULT_DELETE) (ty : type)
    : option (obj_name * delete_operator.t) :=
    match erase_qualifiers ty with
    | Tnamed cls => delete_for_named tu default_delete cls
    | Tincomplete_array _
    | Tarray _ _ => with_delete tu default_delete
    | Tvariable_array _ _ => None
    | _ => with_delete tu default_delete
    end.

  #[local]
  Lemma with_delete_sub_module {tu1 tu2 nm result} :
    with_delete tu1 nm = Some result ->
    sub_module tu1 tu2 ->
    with_delete tu2 nm = Some result.
  Proof.
    rewrite /with_delete; intros.
    destruct (symbols tu1 !! nm) eqn:Heq; simpl in *; try congruence.
    destruct H0. edestruct syms_compat. eassumption.
    destruct H0 as [HH Hle]. rewrite HH /=.
    erewrite <-type_of_value_ObjValue_ler; eauto.
  Qed.

  #[local]
  Lemma delete_for_named_sub_module {tu1 tu2 def cls result} :
    delete_for_named tu1 def cls = Some result ->
    sub_module tu1 tu2 ->
    delete_for_named tu2 def cls = Some result.
  Proof.
    rewrite /delete_for_named; intros.
    destruct (types tu1 !! cls) eqn:Heq; simpl in *; try congruence.
    destruct g; try congruence.
    { erewrite sub_module_preserves_gunion; eauto using with_delete_sub_module. }
    { erewrite sub_module_preserves_gstruct; eauto using with_delete_sub_module. }
    { edestruct sub_module_preserves_genum; eauto.
      rewrite H1. eauto using with_delete_sub_module. }
  Qed.

  Lemma delete_for_submodule {tu1 tu2 op cls result} :
    delete_for tu1 op cls = Some result ->
    sub_module tu1 tu2 ->
    delete_for tu2 op cls = Some result.
  Proof.
    rewrite /delete_for.
    intros.
    repeat (case_match; eauto using with_delete_sub_module, delete_for_named_sub_module).
  Qed.

End delete_operator.
(* END: refactor this *)


Module Type Expr__newdelete.

  #[local] Open Scope free_scope.
  (* hide [genv] argument, it's a typeclass anyway *)
  #[local] Arguments size_of {_} _ : assert.

  (**
   * Weakest pre-condition for [new] and [delete] expressions
   *
   * The semantics of <<new>> and <<delete>> expressions (including their array forms)
   * are *very* complex in C++. This is due to a litany of corner cases such as:
   * - the need to pair allocation and de-allocation functions
   * - the existance of placement <<new>>
   * - the need to handle alignment as well as size.
   * - the potential for padding bytes.
   * - the potential to merge allocations. (BRiCk does not attempt to support this)
   *
   * NOTE It is important that these rules are sound, but less important that
   * they are complete. When in doubt, we err on the side of caution and under-specify
   * the behavior of various constructs.
   *
   * If you run into code that requires addditional semantic specification, please file
   * an issue.
   *)

  (** Dynamic Typing at <<delete>>-Time

      The C++ Standard ascribes undefined behavior to any <<delete>>-calls which
      have a Static Type which differs from the Dynamic Type that was associated
      with the pointer when it was initially created via <<new>>
      <https://eel.is/c++draft/expr.delete#3>:
      | (3) In a single-object delete expression, if the static type of the object to be
      |     deleted is not similar ([conv.qual]) to its dynamic type and the selected
      |     deallocation function (see below) is not a destroying operator delete, the
      |     static type shall be a base class of the dynamic type of the object to be
      |     deleted and the static type shall have a virtual destructor or the behavior is
      |     undefined. In an array delete expression, if the dynamic type of the object to
      |     be deleted is not similar to its static type, the behavior is undefined.
      [new_token.R q allocation_type] tracks this Dynamic Type information.

      Making this [Fractional] instead of [Exclusive] helps write representation
      predicates for classes like the following:
      <<
      class Foo {
        int* x;
        Foo() : x(new int) {}
      };
      >>

      [obj |-> new_token.R q (new_token.mk ty storage ptr offset)] is ownership that:
      - [obj] is the constructed object pointer
      - [ty] is the <<new>>d type, *including qualifiers*.
      - [storage_ptr] is the block storage pointer that underlies [obj],
        see [new_token_provides_storage].
      - [offset] is the size of the meta-data owned by the C++ abstract machine.
        This overhead lives at [storage_ptr .[ Tbyte ! -offset) |-> blockR 1 offset].
   *)

  #[global] Notation Tbyte := Tuchar (only parsing).

  Module new_token.
    Record t := mk
      { alloc_ty : type
      ; storage_ptr : ptr
      ; overhead : N
      }.

    Definition mkBase  `{σ : genv} ty storage_base (overhead : N)
      := mk ty (storage_base .[ Tbyte ! overhead ]) overhead.

    #[global] Notation storage_base d
      := (d.(storage_ptr) .[ Tuchar ! - d.(overhead) ]).

    Parameter R : forall `{Σ : cpp_logic} {σ : genv} (q : Qp) (data : t), Rep.
    #[global] Arguments R {_ _ _ σ} _%_Qp _%_N.

    Section with_cpp_logic.
      Context `{Σ : cpp_logic} {σ : genv}.

      #[global] Declare Instance Observe_provides_storage : forall obj q d,
          Observe (provides_storage d.(storage_ptr) obj d.(alloc_ty))
            (obj |-> R q d).

      #[global] Declare Instance Observe_type_size : forall q d,
          Observe [| exists sz, size_of d.(alloc_ty) = Some sz |]
            (R q d).

      #[global] Declare Instance R_frac :
        FracSplittable_1 R.
      #[global] Declare Instance R_agree :
        AgreeF1 R.

      (** This guarantees that non-array allocations have 0 overhead bytes.

          This is supported by <https://eel.is/c++draft/expr.new#17>.

          > When a new-expression calls an allocation function and that allocation
          > has not been extended, the new-expression passes the amount of space
          > requested to the allocation function as the first argument of type std​::​size_t.
          > That argument shall be no less than the size of the object being created;
          > it may be greater than the size of the object being created only if
          > the object is an array and the allocation function is not a non-allocating
          > form ([new.delete.placement]). For arrays of char, unsigned char, and std​::​byte,
          > the difference between the result of the new-expression and the address returned
          > by the allocation function shall be an integral multiple of the strictest
          > fundamental alignment requirement of any object type whose size is no greater
          > than the size of the array being created.
       *)
      #[global] Declare Instance new_token_non_array_0_overhead : forall ty q storage_p overhead,
          TCEq (is_array_type ty) false ->
          Observe [| overhead = 0%N |] (new_token.R q $ new_token.mk ty storage_p overhead).

    End with_cpp_logic.
  End new_token.

  Section with_cpp_logic.
    Context `{Σ : cpp_logic} {σ : genv}.

    Section with_region.

      Context (ρ : region).
      Variable (tu : translation_unit).

      #[local] Notation wp_init := (wp_init tu ρ).
      #[local] Notation wp_initialize := (wp_initialize tu ρ).
      #[local] Notation default_initialize := (default_initialize tu).
      #[local] Notation wp_operand := (wp_operand tu ρ).
      #[local] Notation wp_args := (wp_args tu ρ).

      #[local] Notation Tbyte := Tuchar (only parsing).

      Section new.
        (** [new (...) C(...)] <https://eel.is/c++draft/expr.new>
            - invokes a C++ new operator [new_fn], which returns a storage pointer [storage_ptr];
              [new_fn] _might_ allocate memory
              (<https://eel.is/c++draft/expr.new#10>), or return an argument
              address for some forms of placement new;
            - constructs an object pointer [obj_ptr], which shares the address of [storage_ptr];
            - invokes the constructor C over [obj_ptr].

            Furthermore <https://eel.is/c++draft/expr.new#22>:
            | (22) A new-expression that creates an object of type <<T>> initializes that
            |      object as follows:
            | (22.1) If the new-initializer is omitted, the object is default-initialized
            |        ([dcl.init]).
            |        [Note 12: If no initialization is performed, the object has an
            |         indeterminate value. — end note]
            | (22.2) Otherwise, the new-initializer is interpreted according to the
            |        initialization rules of [dcl.init] for direct-initialization.
            We use [default_initialize] for default ininitialization as it is defined in the
            C++ Standard and we use [wp_init] for direct-initialization as defined
            by the C++ Standard.

            ~~~ Implementation Details ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

            - This axiom assumes that [storage_ptr] points to a character array that will
              _provide storage_ for a new _complete object_ [o]
              (<http://eel.is/c++draft/intro.object#def:provides_storage>).

              In that case, the C++ abstract machine can choose to make [obj_ptr
              <> storage_ptr] (while keeping the same address), so that the old
              pointer [storage_ptr] cannot be used to access the new object.
              Inspired by Cerberus, we model this by _allowing_ [obj_ptr] to have
              a different allocation ID.

            - The created object might be a subobject of an existing object
              (pointed to by some pointer [p])
              (<https://eel.is/c++draft/basic.memobj#intro.object-2>).
              It is unclear whether that requires [storage_ptr = p] or just
              [provides_storage storage_ptr p].
              In that case, we plan to allow proving that [obj_ptr] = [p ., o]; we
              offer no such support at present; we account for this case by not specifying that
              [ptr_alloc_id obj_ptr <> ptr_alloc_id storage_ptr].
            - Currently, we do not model coalescing of multiple allocations
              (<https://eel.is/c++draft/expr.new#14>).
         *)
        Definition wp_opt_initialize (oinit : option Expr) aty obj_ptr :=
          match oinit with
          | None => (* default_initialize the memory *)
            default_initialize aty obj_ptr
          | Some init => (* Use [init] to initialize the memory *)
            wp_initialize aty obj_ptr init
          end.
        #[global] Arguments wp_opt_initialize !_ _ _ /.

        (* This function takes the size and alignment explicitly because
           the semantics of <<operator new[]>> can add an unspecified amount
           of overhead to the allocation.

           Question: Is it possible for the C++ abstract machine to pass an
           alignment that is different than the alignment of the object type?
         *)
        Definition new_implicits (pass_align : bool) (sz al : N) : list Expr :=
          (* the evaluation of these expressions implicitly check that the
             values are representable in their respective types *)
          [Eint sz Tsize_t] ++
            if pass_align
            then [Ecast (Cintegral Talign_val_t) (Eint al Tsize_t)]
            else [].

        (** Only the default allocation functions are required to provide
            alignment of <<__STDCPP_DEFAULT_NEW_ALIGNMENT__>>.
            See <https://eel.is/c++draft/cpp.predefined#1.8>.
         *)
        Definition requires_default_alignment (tu : translation_unit) (nm : name) : bool :=
          match nm with
          | Nglobal (Nop function_qualifiers.N (OONew _) [arg]) =>
              (* This assumes that names do not use aliases, which they do not *)
              if bool_decide (arg = Tsize_t) then true
              else false
          | _ => false
          end.

        Axiom wp_operand_new :
          forall (oinit : option Expr)
            new_fn (pass_align : bool) new_args aty Q targs
            (nfty := normalize_type new_fn.2)
            (_ : (args_for <$> as_function nfty) = Some targs)
            (alloc_sz alloc_al : N)
            (_ : size_of aty = Some alloc_sz) (_ : align_of aty = Some alloc_al),
            (let implicit_args := new_implicits pass_align alloc_sz alloc_al in
             letI* _, vs, ifree, free :=
               wp_args evaluation_order.nd [] targs (implicit_args ++ new_args) in
             |> letI* res := wp_fptr tu.(types) nfty (_global new_fn.1) vs in
                letI* := interp tu ifree in
                letI* storage_val := operand_receive (Tptr Tvoid) res in
                Exists storage_ptr : ptr,
                  [| storage_val = Vptr storage_ptr |] **
                  if bool_decide (storage_ptr = nullptr) then
                    [| can_throw <$> tu.(symbols) !! new_fn.1 = Some exception_spec.NoThrow |] **
                    Q (Vptr storage_ptr) free
                    (* ^^ only <<noexcept>> overloads for <<operator new>> are allowed to return <<nullptr>> *)
                  else
                    (* C++ requires the resulting pointer to be aligned to
                        <<__STDCPP_DEFAULT_NEW_ALIGNMENT__>> even in cases when the
                        required alignment is actually smaller. When the alignment is
                        smaller, [pass_align] will be [false]. *)
                    storage_ptr |-> alignedR (if pass_align && ~~requires_default_alignment tu new_fn.1
                                              then alloc_al else STDCPP_DEFAULT_NEW_ALIGNMENT) **
                    storage_ptr |-> blockR alloc_sz 1$m **
                    (Forall (obj_ptr : ptr),
                       provides_storage storage_ptr obj_ptr aty -*
                       letI* free' := wp_opt_initialize oinit aty obj_ptr in
                        (* This also ensures these pointers share their
                          address (see [provides_storage_same_address]) *)
                        (* Track the type we are allocating
                          so it can be checked at <<delete>>.
                          It is important that this preserves
                          `const`ness of the type.
                        *)
                        obj_ptr |-> new_token.R 1 (new_token.mk aty storage_ptr 0) -*
                        Q (Vptr obj_ptr) (free' >*> free)))
        |-- wp_operand (Enew new_fn new_args (new_form.Allocating pass_align) aty None oinit) Q.

        (** The C++ standard distinguishes placement/non-allocating forms in
         *  <https://eel.is/c++draft/new.delete.placement#1>.
         *
         *  NOTE: placement <new> is more subtle than the rule described here
         *  because it can be used to construct an object over an existing
         *  object.
         *)
        Axiom wp_operand_non_allocating_new :
          forall (oinit : option Expr)
            new_fn storage_expr aty Q
            (nfty := normalize_type new_fn.2)
            (_ : args_for <$> as_function nfty = Some ([Tsize_t; Tptr Tvoid], Ar_Definite)),
            (Exists alloc_sz alloc_al,
               [| size_of aty = Some alloc_sz |] **
               [| align_of aty = Some alloc_al |] ** (** <-- TODO FM-975 *)
             letI* _, vs, ifree, free :=
               wp_args evaluation_order.nd [] ([Tsize_t;Tptr Tvoid], Ar_Definite)
                 [Eint alloc_sz Tsize_t; storage_expr] in
             Exists storage_ptr,
               (Exists size_loc storage_loc,
                 [| vs = [size_loc; storage_loc] |] **
                 storage_loc |-> primR (Tptr Tvoid) 1$m (Vptr storage_ptr) ** True) //\\
               (|> letI* res := wp_fptr tu.(types) nfty (_global new_fn.1) vs in
                 letI* := interp tu ifree in
                 res |-> primR (Tptr Tvoid) 1$m (Vptr storage_ptr) **
                 (* ^^ this line requires the function to return the passed pointer.
                    This is mandated by the standard, see, e.g.
                    <https://eel.is/c++draft/new.delete.placement#2>
                  *)
                  [| storage_ptr <> nullptr |] **
                  (* ^^ mostly redundant with next line except for 0-sized objects *)
                  storage_ptr |-> blockR alloc_sz 1$m **
                  storage_ptr |-> alignedR alloc_al **
                  (Forall (obj_ptr : ptr),
                      (* This also ensures these pointers share their
                        address (see [provides_storage_same_address]) *)
                      provides_storage storage_ptr obj_ptr aty -*
                      letI* free' := wp_opt_initialize oinit aty obj_ptr in
                        (* Track the type we are allocating
                          so it can be checked at [delete].
                          It is important that this preserves
                          `const`ness of the type.
                        *)
                        obj_ptr |-> new_token.R 1 (new_token.mk aty storage_ptr 0) -*
                        Q (Vptr obj_ptr) (free' >*> free))))
        |-- wp_operand (Enew new_fn [storage_expr] new_form.NonAllocating aty None oinit) Q.

        (* A size such that if the requested allocation size is less than this, the C++
           abstract machine is guaranteed to be able to find a suitable overhead such
           that there is an allocation that can satisfy the requirements. See
           <https://eel.is/c++draft/implimits#2.17>

           The C++ standard recommends that this value be greater than <<262,144>>.
         *)
        Parameter SIZE_MAX : N.

        Axiom wp_operand_array_new :
          forall (array_size : Expr) (oinit : option Expr)
            new_fn (pass_align : bool) new_args aty Q targs
            (nfty := normalize_type new_fn.2)
            (_ : args_for <$> as_function nfty = Some targs),
            (* <https://eel.is/c++draft/expr.new#7>
               | (7) Every constant-expression in a noptr-new-declarator shall be a
               |     converted constant expression ([expr.const]) of type std​::​size_t
               |     and its value shall be greater than zero.
               |     [Example 4: Given the definition int n = 42, new float[n][5] is
               |      well-formed (because n is the expression of a noptr-new-declarator),
               |      but new float[5][n] is ill-formed (because n is not a constant
               |      expression). — end example]
               If we're allocating a new array, we know that the expression must reduce
               to a constant value of type [size_t] /and/ that it must be sequenced
               before we call the [new_fn].
             *)
            (letI* v, free := wp_operand array_size in
              (* Valid C++ programs require this value to be a [Vint] (see the quote from
                 <expr.new#7> above). *)
              Exists array_sizeN, [| v = Vn array_sizeN |] **
                (* The size must be non-negative. *)
                [| 0 <= array_sizeN |]%N **
                Exists alloc_sz alloc_al,
                let array_ty := Tarray aty array_sizeN in
                [| size_of array_ty = Some alloc_sz |] **
                [| align_of aty = Some alloc_al |] ** (** <-- TODO FM-975 *)
                (* NOTE: This is [Forall overhead_sz] because the C++ Abstract Machine can choose
                          however many bytes it wants to use for metadata when handling
                          dynamically allocated arrays; however, it can not be *completely*
                          unconstrained because the allocated size plus the overhead
                          must fit within <<size_t>>. If it does not, [nullptr] is returned
                          (or <<std::bad_array_new_length>> is thrown, but BRiCk does not
                          support exceptions).
                          See <https://eel.is/c++draft/expr.new#8.6>.
                  *)
                [| has_type_prop alloc_sz Tsize_t |] **
                (([| (SIZE_MAX < alloc_sz)%N |] -* Q (Vptr nullptr) free) //\\
                 (* ^^ handles when the overhead exceeds the size *)
                Forall overhead_sz : N,
                  [| has_type_prop (overhead_sz + alloc_sz)%N Tsize_t |] -*
                  let implicit_args :=
                      new_implicits pass_align (overhead_sz + alloc_sz) alloc_al in
                  letI* _, vs, ifree, free' :=
                      wp_args evaluation_order.nd [] targs (implicit_args ++ new_args) in
                  |> letI* res := wp_fptr tu.(types) nfty (_global new_fn.1) vs in
                     letI* := interp tu ifree in
                     letI* storage_val := operand_receive "void*" res in
                     Exists (storage_base : ptr),
                       [| storage_val = Vptr storage_base |] **
                       if bool_decide (storage_base = nullptr) then
                         [| can_throw <$> tu.(symbols) !! new_fn.1 = Some exception_spec.NoThrow |] **
                         Q (Vptr storage_base) (free' >*> free)
                         (* ^^ only <<noexcept>> overloads for <<operator new>> are allowed to return <<nullptr>> *)
                       else
                         (* [blockR alloc_sz -|- tblockR (Tarray aty array_size)] *)
                         storage_base |-> blockR (overhead_sz + alloc_sz) 1$m **
                         storage_base |-> alignedR (if pass_align && ~~requires_default_alignment tu new_fn.1
                                                    then alloc_al else STDCPP_DEFAULT_NEW_ALIGNMENT) **
                         (Forall (obj_ptr : ptr),
                           storage_base .[Tbyte ! overhead_sz] |-> alignedR alloc_al -*
                           (* This also ensures these pointers share their
                              address (see [provides_storage_same_address]) *)
                           provides_storage
                             (storage_base .[Tbyte ! overhead_sz])
                             obj_ptr array_ty -*
                           letI* free'' := wp_opt_initialize oinit array_ty obj_ptr in
                             (* Track the type we are allocating
                                so it can be checked at <<delete>>
                              *)
                           obj_ptr |-> new_token.R 1 (new_token.mkBase array_ty storage_base overhead_sz) -*
                           Q (Vptr obj_ptr) (free'' >*> (free' >*> free)))))
        |-- wp_operand (Enew new_fn new_args (new_form.Allocating pass_align) aty (Some array_size) oinit) Q.

        (* We deliberately avoid giving a reasoning principle for array-placement <<new>> since
           it is generally not used and compilers differ in the semantics.
         *)

      End new.
    End with_region.

  End with_cpp_logic.

  (** ** <<delete>> and <<delete[]>> *)

  (** [resolve_complete_obj ty obj_ptr' Q] resolves the destructor for the object
      <<obj_ptr'>> (of type <<ty>>). The continuation [Q] is passed the pointer to the
      most-derived-object of <<obj_ptr>> and its type.

      NOTE: This only resolves the complete object if the destructor is <<virtual>>.
            Otherwise, the class itself is returned.

      NOTE: The implementation does **not** take the current translation unit
            and instead looks up the class in the ambient (global) program. By the
            one-definition-rule (ODR), looking up the result in the whole program will
            yield an answer that is at least as informative as one that looks up
            in the current translation unit. So if the dispatch is <<virtual>> in
            the whole program, then the dispatch must also be <<virtual>> in the
            local translation unit (as long as the program is well-typed).

      NOTE: <<erase_qualifiers>> is probably not necessary here.
    *)
  mlock
  Definition resolve_complete_obj `{Σ : cpp_logic} {σ : genv} (ty : type)
    (obj_ptr' : ptr) (Q : ptr -> type -> mpred) : mpred :=
    match drop_qualifiers ty with
    | Tqualified _ ty => False (* unreachable *)
    | Tnamed cls      =>
      match (genv_tu σ).(types) !! cls with
      | Some (Gstruct s) =>
        if has_virtual_dtor s then
          (* NOTE [has_virtual_dtor] could be derived from the vtable... *)
          (* In this case, use virtual dispatch to invoke the destructor. *)
          letI* fimpl, impl_class, obj_ptr := resolve_virtual obj_ptr' cls s.(s_dtor) in
          let r_ty := Tnamed impl_class in
          Q obj_ptr r_ty
        else
          Q obj_ptr' (erase_qualifiers ty)
      | Some (Gunion u)  =>
        (* Unions cannot have [virtual] destructors: we directly invoke the destructor. *)
        Q obj_ptr' (erase_qualifiers ty)
      | Some (Genum _ _) =>
        Q obj_ptr' (erase_qualifiers ty)
      | _                => False
      end
    | Tarray _ _
    | Tincomplete_array _
    | Tvariable_array _ _ =>
      Q obj_ptr' (erase_qualifiers ty)
    | Tref r_ty
    | Trv_ref r_ty    =>
      False (* references can not be deleted, only destroyed *)
    | ty              =>
      Q obj_ptr' (erase_qualifiers ty)
    end%I.

  Section with_cpp.
    Context `{Σ : cpp_logic} {σ : genv}.
    Lemma resolve_complete_obj_frame : forall ty p Q Q',
        Forall p t, Q p t -* Q' p t |-- resolve_complete_obj ty p Q -* resolve_complete_obj ty p Q'.
    Proof.
      rewrite resolve_complete_obj.unlock; intros.
      iIntros "X"; repeat case_match; eauto; try solve [ iApply wp_fptr_frame; iIntros (?); eauto ].
      iApply resolve_virtual_frame. iIntros (???); iApply "X".
    Qed.

    (** [delete_compat dealloc alloc] holds when the allocation type <<alloc>>
        can be deleted by an expression representing the deallocation type
        <<dealloc>>.

        Normally, this means that <<dealloc = alloc>>, but we use
        [Tincomplete_array] to approximate any array type, therefore we can
        [delete_compat (Tincomplete_array ety) (Tarray ety _)] holds.

        Importantly, when we check this in the case of <<virtual>> dispatch,
        <<dealloc>> will be the type of the complete object, **not** the type
        of the pointer used to perform the <<delete>>. These types are guaranteed
        to be related because we compute the type of the complete object through
        [resolve_complete_obj] which uses [derivationR].
     *)
    Definition delete_compat (dealloc_type alloc_type : type) : Prop :=
      match erase_qualifiers dealloc_type , erase_qualifiers alloc_type with
      | Tincomplete_array ety , Tarray ety' _ => ety = ety'
      | dealloc , alloc => dealloc = alloc
      end.

    #[global] Instance delete_compat_dec {dealloc alloc}
      : Decision (delete_compat dealloc alloc) :=
      ltac:(rewrite /delete_compat; repeat case_match; apply _).

    Lemma delete_compat_refl ty : delete_compat ty ty.
    Proof. rewrite /delete_compat. destruct (erase_qualifiers ty); simpl; eauto. Qed.
  End with_cpp.

  (** Invoke the delete operator <<del_op.1>> on the pointer <<p>> for the type
      <<obj_type>>. The type <<obj_type>> is used to get the size and
      alignedness information if the <<operator delete>> requires them.

      NOTE: <<p>> should be the object pointer in the case of destroying delete
            and otherwise should be the storage pointer.

      NOTE: <<allocation_size>> must be the size of the entire allocation
            (including overhead). This is especially relevant when deleting
            an array.
   *)
  mlock
  Definition wp_invoke_delete `{Σ : cpp_logic} {σ : genv} (obj_type : type)
    (del_op : name * delete_operator.t) (allocation_size : N)
    (p : ptr) (Q : mpred) : mpred :=
    letI* args , free := fun (Q : list ptr -> FreeTemps.t -> mpred) =>
        (* Add the alignment, if required *)
        if del_op.2.(delete_operator.align_arg) then
          let ty := Talign_val_t in
          Exists al, [| align_of obj_type = Some al |] **
          Forall pp : ptr, pp |-> primR ty (cQp.m 1) (Vn al) -* Q (pp :: nil) (FreeTemps.delete ty pp)
        else Q nil FreeTemps.id
    in
    letI* args , free := fun (Q : list ptr -> FreeTemps.t -> mpred) =>
      (* Add the size, if required *)
      if del_op.2.(delete_operator.size_arg) then
         let ty := Tsize_t in
         Forall pp : ptr, pp |-> primR ty (cQp.m 1) (Vn allocation_size) -* Q (pp :: args) (FreeTemps.delete ty pp >*> free)
      else Q args free
    in
    letI* args , free := fun (Q : list ptr -> FreeTemps.t -> mpred) =>
      (* Add the pointer (and the <<std::destroying_delete_t>> flag if necessary) *)
      if del_op.2.(delete_operator.destroying) then
        (* In addition to the pointer, we must also pass the value of type
           <<std::destroying_delete_t>>. This value is passed by-value, which means
           that it is copied. Here we assume the following implementation:
           <<
           struct std::destroying_delete_t {};
           >>
           We capture the ownership using [anyR "std::destroying_delete_t" (cQp.m 1)]
           but we could also check that the structure exists.
         *)
        let ty := erase_qualifiers $ Tptr obj_type in
        Forall pp : ptr, pp |-> primR ty (cQp.m 1) (Vptr p) -*
        Forall dd : ptr, dd |-> anyR "std::destroying_delete_t" (cQp.m 1) -*
        Q (pp :: dd :: args) (FreeTemps.delete ty pp >*> FreeTemps.delete Tdestroying_delete_t dd >*> free)
      else
        let ty := "void*"%cpp_type in
        Forall pp : ptr, pp |-> primR ty (cQp.m 1) (Vptr p) -*
        Q (pp :: args) (FreeTemps.delete ty pp >*> free)
    in
    letI* p :=
      let del_ty := delete_operator.type_for del_op.2 in
      wp_fptr (genv_tu σ).(types) del_ty (_global del_op.1) args in
    letI* := interp (genv_tu σ) free in
    letI* _ := operand_receive "void" p in
    Q.

  Lemma wp_invoke_delete_frame `{Σ : cpp_logic} {σ : genv}
    obj_type operator_delete size obj_ptr Q Q' :
    Q -* Q'
    |-- wp_invoke_delete obj_type operator_delete size obj_ptr Q -*
        wp_invoke_delete obj_type operator_delete size obj_ptr Q'.
  Proof.
    rewrite wp_invoke_delete.unlock.
    iIntros "H";
    repeat case_match; simpl; do_frame.
  Qed.

  (** [wp_delete_null]
      The semantics of <<delete static_cast<destroyed_type*>(nullptr);>>

      The C++ standard allows <<delete nullptr>> to invoke the underlying
      <<operator delete>> or to do nothing. To support this, the semantics
      uses a classical conjunction to represent non-deterministic (demonic)
      choice.

      NOTE: As with [wp_delete_obj], to invoke <<delete[]>>, <<destroyed_type>>
      should be [Tincomplete_array element_type].
   *)
  mlock
  Definition wp_delete_null `{Σ : cpp_logic} {σ : genv}
    default_delete destroyed_type Q : mpred :=
    (match delete_operator.delete_for (genv_tu σ) default_delete destroyed_type with
     | Some del_op =>
         (* The use of <<0>> here is somewhat arbitrary. It is supposed to be
            the size of the allocation (including overhead). For deleting
            <<nullptr>>, there is no object, but the standard does say that
            it is legal to call this function. In practice, it seems
            like compilers do not do this.
          *)
         wp_invoke_delete destroyed_type del_op 0 nullptr Q
     | None => False
     end ∧ Q).

  Lemma wp_delete_null_frame `{Σ : cpp_logic} {σ : genv}
    default_delete destroyed_type Q Q' :
    Q -* Q'
    |-- wp_delete_null default_delete destroyed_type Q -*
        wp_delete_null default_delete destroyed_type Q'.
  Proof.
    rewrite wp_delete_null.unlock.
    case_match; do_frame.
    { iIntros "H"; do_frame.
      iIntros "H'"; iSplit.
      - by iDestruct "H'" as "[H' _]"; iRevert "H'"; iApply wp_invoke_delete_frame.
      - iDestruct "H'" as "[_ H']"; iApply "H"; eauto. }
    { iIntros "H"; do_frame; iIntros "X"; iSplit.
      iDestruct "X" as "[[] _]".
      iDestruct "X" as "[_ X]"; iApply "H"; eauto. }
  Qed.

  (** [wp_delete_obj tu obj_type d obj_ptr storage_ptr Q]
      Delete the object <<obj_ptr>> (of C++ type <<obj_type>>) that occupies the storage <<storage_ptr>>.
      <<obj_ptr>> should be the pointer to the complete object meaning that no virtual dispatch occurs
      here.

      This weakest pre-condition does **not** take a translation unit because object deletion is
      (effectively) handled by 0-argument closures. For example, suppose that you have the following
      program:
      <<
      // header.hpp
      struct C { virtual ~C() = 0; };

      void delete_it(C* p) { delete p; }

      // impl.cpp
      struct D : C { operator delete(D*, std::destroying_delete_t) { ... } };

      void test() { delete_it(new D()); }
      >>

      In this case, <<delete_it>> ultimately invokes <<D::operator delete(D*, std::destroying_delete_t)>>
      but the implementation of <<delete_it>> can not see that function statically.
   *)
  mlock
  Definition wp_delete_obj `{Σ : cpp_logic} {σ : genv}
    (default_delete : DEFAULT_DELETE) (obj_type : type)
    (obj_ptr : ptr) (Q : mpred) : mpred :=
    match delete_operator.delete_for (genv_tu σ) default_delete obj_type with
    | None => ERROR ("wp_delete_obj: failed to find <<operator delete>> for type"%pstring, obj_type)
    | Some del_op =>
      Exists alloc_type storage_ptr overhead sz,
        obj_ptr |-> new_token.R 1 (new_token.mk alloc_type storage_ptr overhead) **
        [| delete_compat obj_type alloc_type |] **
        [| size_of alloc_type = Some sz |] **
        if del_op.2.(delete_operator.destroying) is Some _ then
          UNSUPPORTED ("wp_delete_obj: destroying delete is not supported"%pstring, obj_type)
          (* Sketch implementation. Test cases needed.
          let '(cv, ty) := decompose_type alloc_type in
          letI* :=
            if q_const cv
            then wp_make_mutable (genv_tu σ) obj_ptr ty
            else (fun Q => Q)
          in
          (* This magic wand gives the destroying <<operator delete>> the ability
             to trade the deconstructed resources at <<obj_ptr>> for the resources
             at the storage pointer. The use of <<K>> requires (meta-theoretically)
             that the destruction of the object occurs within the implementation of
             the <<operator delete>>.

             Note that there is no destroying delete operator for arrays, so, in
             practice we know that <<overhead = 0>> here. In practice, a specification
             for a destroying delete operator would look like the following:
             [[
             \arg{p} "p" (Vptr p)
             \arg{delp} "" (Vptr delp)
             \pre p |-> R (cQp.m 1) ...
             \pre{storage_ptr K}
                (p |-> tblockR T (cQp.m 1) -* |={top}=>
                 storage_ptr |-> blockR (size_of T) (cQp.m 1) ** K)
             \persist provides_storage storage_ptr p
             \post K
             ]]
             Note that the implementation would be required to use <<std::launder>>
             in order to get <<storage_ptr>> from <<obj_ptr>>.
           *)
          Forall K,
           (obj_ptr |-> tblockR (erase_qualifiers obj_type) (cQp.m 1) -* |={top}=>
            storage_ptr .[ Tuchar ! -overhead ] |-> blockR (overhead + sz) (cQp.m 1) ** K) -*
           letI* := wp_invoke_delete ty del_op (overhead + sz) obj_ptr in
           K ** Q
           *)
        else
          letI* := interp (genv_tu σ) (FreeTemps.delete alloc_type obj_ptr) in
          (storage_ptr .[ Tuchar ! -overhead ] |-> blockR (overhead + sz) (cQp.m 1) -*
           (* the <<operator delete>> is invoked with the beginning of the storage pointer *)
           letI* := wp_invoke_delete obj_type del_op (overhead + sz) (storage_ptr .[ Tbyte ! -overhead ]) in
           Q)
    end%I.

  Lemma wp_delete_obj_frame `{Σ : cpp_logic} {σ : genv}
    default_delete destroyed_type p Q Q' :
    Q -* Q'
    |-- wp_delete_obj default_delete destroyed_type p Q -*
        wp_delete_obj default_delete destroyed_type p Q'.
  Proof.
    rewrite wp_delete_obj.unlock.
    iIntros "H";
      repeat first [ case_match | progress do_frame ].
    - iIntros "[]".
      (* iApply wp_const_frame; first reflexivity.
      do_frame. iApply wp_invoke_delete_frame. do_frame. *)
    - iApply wp_invoke_delete_frame; do_frame; eauto.
    - iIntros "[]".
  Qed.

  Section delete.
    Context `{Σ : cpp_logic} {σ : genv}.

    Section with_region.
      Variable (tu : translation_unit).
      Context (ρ : region).
      #[local] Notation wp_operand := (wp_operand tu ρ).

      (* <<delete>>

          https://eel.is/c++draft/expr.delete

          NOTE: https://eel.is/c++draft/expr.delete#7.1 says:
          > The value returned from the allocation call of the new-expression
          > shall be passed as the first argument to the deallocation function.

          Hence, the destructor is passed a pointer to the object, and the
          deallocation function <<delete>> is passed a pointer to the
          underlying storage (of type <<void *>>).

          On deleting null:
          From the C++ standard (<https://en.cppreference.com/w/cpp/language/delete>)

          > If expression evaluates to a null pointer value, no destructors are
          > called, and the deallocation function may or may not be called (it's
          > unspecified), but the default deallocation functions are guaranteed
          > to do nothing when passed a null pointer.

          NOTE: [Edelete]'s first argument is [true] iff the expression corresponds to
          an array-delete, i.e. <<delete[]>>.
        *)
      Axiom wp_operand_delete : forall default_delete e destroyed_type Q,
        (letI* v , free := wp_operand e in
         Exists obj_ptr, [| v = Vptr obj_ptr |] **
         if bool_decide (obj_ptr = nullptr) then
           wp_delete_null default_delete destroyed_type (Q Vvoid free)
         else
           letI* this', mdc_ty := resolve_complete_obj destroyed_type obj_ptr in
           wp_delete_obj default_delete mdc_ty this' (Q Vvoid free))
      |-- wp_operand (Edelete false default_delete e destroyed_type) Q.

      (** [wp_operand_delete_default] specializes [wp_operand_delete] for invocations of
        *  the form <<delete p;>> - where <<p>> is a non-null pointer to an object whose
        *  most-derived destructor is defined in the current translation unit.
        *)
      Lemma wp_operand_delete_default : forall default_delete e destroyed_type Q,
        (* call the destructor on the object, and then call delete_fn *)
        (letI* v, free := wp_operand e in
         Exists obj_ptr, [| v = Vptr obj_ptr |] ** [| obj_ptr <> nullptr |] **
           letI* this', mdc_ty := resolve_complete_obj destroyed_type obj_ptr in
           wp_delete_obj default_delete mdc_ty this' (Q Vvoid free))
      |-- wp_operand (Edelete false default_delete e destroyed_type) Q.
      Proof.
        intros **; iIntros "operand".
        iApply wp_operand_models; iIntros "#MOD".
        iApply wp_operand_delete; eauto; cbn.
        iApply (wp_operand_frame _ tu); [by reflexivity | | by iFrame].
        iIntros (v free) "H"; iDestruct "H" as (obj_ptr) "(-> & % & dtor_lookup)".
        iExists obj_ptr; iSplitR; first done.
        case_bool_decide; try congruence; eauto.
      Qed.

      (* NOTE: <<destroyed_type>> will refer to the /element/ of the array *)
      Axiom wp_operand_array_delete : forall default_delete e destroyed_type Q,
        (* call the destructor on the object, and then call delete_fn *)
        (letI* v, free := wp_operand e in
         Exists obj_ptr, [| v = Vptr obj_ptr |] **
         if bool_decide (obj_ptr = nullptr) then
           wp_delete_null default_delete (Tincomplete_array destroyed_type) (Q Vvoid free)
         else
           wp_delete_obj default_delete (Tincomplete_array destroyed_type) obj_ptr (Q Vvoid free))
      |-- wp_operand (Edelete true default_delete e destroyed_type) Q.

      Section NOTE_potentially_relaxing_array_delete.
        (* While (we currently think) it is UB to delete [auto p = new int[5][6]]
            using [delete[] &(p[0][0])], it seems like clang still does something
            sensible for this. If we want to relax our axioms in the future to
            allow for this sort of behavior, we could relate the "carrier type"
            and the "dynamic type" of the array which was allocated (which is stored
            in the [new_token]).

            In particular, so long as the [obj_ptr] [p'] we delete is syntactically
            identical to the [obj_ptr] [p] returned by our array-new call /and/
            the "carrier type" of the delete is _similar_
            <https://eel.is/c++draft/conv.qual> to the "carrier type" of
            the array, we can use [p'] to delete the object rooted at [p].

            NOTE: we might need to insert [erase_qualifiers]/[normalize_type] calls to
            reflect that the standard only calls for "similarity"
            (which has a more nuanced consideration of cv-qualifiers).
          *)

        (* If we have [Tarray ty sz], [array_carrier_type ty] strips all of the outermost
            [Tarray]s off and returns the "carrier type" of the array.
          *)
        Fixpoint array_carrier_type (ty : type) : type :=
          match ty with
          | Tarray ty' _ => array_carrier_type ty'
          | _ => ty
          end.
      End NOTE_potentially_relaxing_array_delete.
    End with_region.
  End delete.
End Expr__newdelete.

Declare Module E__newdelete : Expr__newdelete.

Export E__newdelete.
