(*
 * Copyright (c) 2026 SkyLabs AI, Inc.
 * This software is distributed under the terms of the BedRock Open-Source License.
 * See the LICENSE-BedRock file in the repository root for details.
 *)

(** * Lowering forward <<goto>>s to copies of terminal suffixes

Sketch for SkyLabsAI/BRiCk#515 ("option 3"): the algorithm of
SkyLabsAI/BRiCk#531 (terminal cleanup suffix duplication), run on the BRiCk
AST in Gallina instead of inside cpp2v.

[lower_goto rt body] either rejects [body] ([None]) or returns a body
without any [Sgoto]/[Slabeled], obtained by

- replacing each accepted <<goto L;>> by a block holding a copy of the
  terminal suffix of [L]: the statement labeled [L] and all its following
  siblings in the function body, through the terminal <<return>>
  (for a <<void>> function, through the closing brace followed by an
  inserted <<return;>>);
- erasing every label.

It is all-or-nothing: one unsupported goto or label rejects the whole body.
The trusted rule [wp_lower_goto] (../logic/goto_lowering.v) lets a proof run
the lowered body instead of the original one.

** Why substitution is sound for accepted jumps

The semantics resolves names through the region (`get_location`, innermost
binding first), and only [wp_block] extends it, at each [Sdecl], wrapping the
continuation in [Kfree] (see [wp_block_def] in ../logic/stmt.v). An accepted
jump goes from a point whose bindings are [P ++ X] (innermost last) to a
label at the top level of the body whose bindings are [P ++ S], where

- [P] is the shared prefix of top-level declarations, the same objects at
  both points;
- [X] ("extra") are the bindings of the scopes the jump leaves: nested blocks,
  loop and condition variables;
- [S] ("skipped") are top-level declarations between the jump and the label.

The copy runs with [P ++ X], the original suffix with [P ++ S]. The copy is
equivalent when

1. the suffix reads no name bound in [X] or [S], so every name it uses resolves
   to the same object of [P] (or a global);
2. leaving [X] early has no observable effect: in the original their lifetime
   ends at the jump, in the copy at the copy's <<return>>. We require scalar
   types (trivial destruction, so the only effect of [Kfree] is giving the
   storage back) and that their address never escapes (no syntactic use other
   than reads and discarded writes), so no pointer can observe the lifetime
   difference ([rejected.cpp]'s [escaped_scalar]);
3. [S] has no effect on the path through the jump: scalar declarations without
   initializer (vacuous initialization, so C++ allows jumping past them,
   https://eel.is/c++draft/stmt.dcl#2) or function-local statics ([Dinit],
   which do not extend the region, see [wp_decl]);
4. the copy never falls through into the code after the jump: the suffix ends
   in <<return>> (we append <<return;>> for <<void>> functions, where falling
   off the end is a <<return;>>, https://eel.is/c++draft/stmt.return#4);
5. the suffix contains only statements whose meaning depends on nothing but the
   region and the state: expression statements, <<return>>, and <<if>> without
   init/condition declarations. No declarations, labels, gotos, loops,
   <<break>>/<<continue>>/<<case>> (those would bind to a construct around the
   copy site), NRVO returns, or <<asm>>.

Moreover:

- targets must be labels at the top level of the body, after the jump
  (forward); a label anywhere else rejects the body. This excludes the cycles
  of [forward_in_loop] and jumps into nested scopes.
- the whole body must be free of statement expressions ([Estmt]),
  [Sunsupported], [Eunsupported], <<asm>> (which could hide jumps or label
  addresses), and template-dependent nodes.
- a suffix containing a goto is not a valid suffix: we do not expand
  recursively (this is what keeps the output size quadratic, not exponential).

** Cost

One pass computes the uses of every variable; one backward pass over the
top-level statements builds the label table and lowers each statement.
Lowering a goto costs a table lookup (number of labels) and a check of the
extra bindings against the suffix's free names; a declaration costs one update
of each label's [blocked] flag. Copies share their tails. The output has size
[O(N + sum of copied suffixes)], at most quadratic in the input.
*)

Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.core.
Require Import skylabs.lang.cpp.syntax.types.
Require Import skylabs.lang.cpp.syntax.stmt.

#[local] Open Scope bool_scope.

Module goto_lowering.

  (** ** Variable uses *)

  (** A use of a local name. [Uread x] is a read of [x] (lvalue-to-rvalue
      conversion) or a write to [x] whose result is discarded: neither lets
      the address of [x] escape. [Uaddr x] is any other occurrence of [x]
      (address taken, reference binding, call argument by reference, member
      access, ...). [Uopaque] marks syntax this pass does not analyze. *)
  Variant use : Set :=
  | Uread (x : localname)
  | Uaddr (x : localname)
  | Uopaque.

  Definition opt_uses {A} (f : A -> list use -> list use) (o : option A) (acc : list use) : list use :=
    match o with
    | Some a => f a acc
    | None => acc
    end.

  (** [usesE e acc] prepends the uses in [e] to [acc]. Types are skipped:
      they are not evaluated. *)
  Fixpoint usesE (e : Expr) (acc : list use) {struct e} : list use :=
    let all es acc := fold_right usesE acc es in
    match e with
    (* Template-dependent nodes do not occur in instantiated code. *)
    | Eparam _ | Eunresolved_global _ | Eunresolved_sizeof_pack _ _
    | Eunresolved_unop _ _ | Eunresolved_binop _ _ _ | Eunresolved_call _ _
    | Eunresolved_member_call _ _ _ | Eunresolved_parenlist _ _
    | Eunresolved_initlist _ _ | Eunresolved_member _ _
    | Eunresolved_string_literal _ => Uopaque :: acc
    | Evar x _ => Uaddr x :: acc
    | Eenum_const _ _ | Eglobal _ _ | Eglobal_member _ _
    | Echar _ _ | Estring _ _ | Eint _ _ | Ebool _ | Efloat _ _ => acc
    | Eunop _ e _ | Ederef e _ | Eaddrof e => usesE e acc
    | Ebinop _ e1 e2 _ | Eassign e1 e2 _ | Eassign_op _ e1 e2 _ => usesE e1 (usesE e2 acc)
    | Epostinc e _ | Epostdec e _ =>
        (* a postfix increment is a prvalue: it does not expose [x]'s address *)
        match e with
        | Evar x _ => Uread x :: acc
        | _ => usesE e acc
        end
    | Epreinc e _ | Epredec e _ => usesE e acc
    | Eseqand e1 e2 | Eseqor e1 e2 | Ecomma e1 e2 => usesE e1 (usesE e2 acc)
    | Ecall f es => usesE f (all es acc)
    | Eexplicit_cast _ _ e => usesE e acc
    | Ecast c e =>
        match c, e with
        | Cl2r, Evar x _ => Uread x :: acc
        | _, _ => usesE e acc
        end
    | Emember _ e _ _ _ | Ebitfield _ e _ _ | Ebf_glvalue e => usesE e acc
    | Ebf_comma e1 e2 | Ebf_assign e1 e2 _ | Ebf_assign_op _ e1 e2 _ => usesE e1 (usesE e2 acc)
    | Ebf_if e1 e2 e3 _ => usesE e1 (usesE e2 (usesE e3 acc))
    | Ebf_preinc e _ | Ebf_predec e _ | Ebf_postinc e _ | Ebf_postdec e _ => usesE e acc
    | Emember_ignore _ e1 e2 => usesE e1 (usesE e2 acc)
    | Emember_call _ m e es =>
        let acc := usesE e (all es acc) in
        match m with
        | inr f => usesE f acc
        | inl _ => acc
        end
    | Eoperator_call _ _ es => all es acc
    | Esubscript e1 e2 _ => usesE e1 (usesE e2 acc)
    | Esizeof te _ | Ealignof te _ =>
        match te with
        | inr e => usesE e acc
        | inl _ => acc
        end
    | Eoffsetof _ _ _ => acc
    | Econstructor _ es _ => all es acc
    (* names its arguments by identifier, outside of [Evar] *)
    | Einherited_constructor _ _ _ => Uopaque :: acc
    | Elambda _ es => all es acc
    | Eimplicit e => usesE e acc
    | Eimplicit_init _ => acc
    | Eif e1 e2 e3 _ => usesE e1 (usesE e2 (usesE e3 acc))
    | Eif2 _ e1 e2 e3 e4 _ => usesE e1 (usesE e2 (usesE e3 (usesE e4 acc)))
    | Ethis _ | Enull => acc
    | Einitlist es eo _ =>
        all es match eo with Some e => usesE e acc | None => acc end
    | Einitlist_union _ eo _ => match eo with Some e => usesE e acc | None => acc end
    | Einitlist_std e _ => usesE e acc
    | Enew _ es _ _ e1 e2 =>
        all es match e1 with
               | Some e => usesE e match e2 with Some e => usesE e acc | None => acc end
               | None => match e2 with Some e => usesE e acc | None => acc end
               end
    | Edelete _ _ e _ | Eandclean e | Ematerialize_temp e _ => usesE e acc
    | Eatomic _ es _ => all es acc
    (* may contain declarations, labels, gotos *)
    | Estmt _ _ => Uopaque :: acc
    | Eva_arg e _ | Epseudo_destructor _ _ e => usesE e acc
    | Earrayloop_init _ e1 _ _ e2 _ => usesE e1 (usesE e2 acc)
    | Earrayloop_index _ _ | Eopaque_ref _ _ => acc
    | Eunsupported _ _ => Uopaque :: acc
    end.

  (** Uses of an expression whose value is discarded (expression statements,
      <<for>> increments): a write to a variable there does not expose it. *)
  Fixpoint usesD (e : Expr) (acc : list use) : list use :=
    match e with
    | Epreinc (Evar x _) _ | Epredec (Evar x _) _
    | Epostinc (Evar x _) _ | Epostdec (Evar x _) _ => Uread x :: acc
    | Eassign (Evar x _) e2 _ | Eassign_op _ (Evar x _) e2 _ => Uread x :: usesE e2 acc
    | Ecomma e1 e2 => usesD e1 (usesD e2 acc)
    | _ => usesE e acc
    end.

  Definition usesBD (b : BindingDecl) (acc : list use) : list use :=
    match b with
    | Bvar _ _ e | Bbind _ _ e => usesE e acc
    end.

  Definition usesVD (d : VarDecl) (acc : list use) : list use :=
    match d with
    | Dvar _ _ oe => opt_uses usesE oe acc
    | Ddecompose e _ bs => usesE e (fold_right usesBD acc bs)
    | Dinit _ _ _ oe => opt_uses usesE oe acc
    end.

  Fixpoint usesS (s : Stmt) (acc : list use) {struct s} : list use :=
    match s with
    | Sseq ss => fold_right usesS acc ss
    | Sdecl ds => fold_right usesVD acc ds
    | Sif init decl e a b =>
        opt_uses usesS init (opt_uses usesVD decl (usesE e (usesS a (usesS b acc))))
    | Sif_consteval a b => usesS a (usesS b acc)
    | Swhile decl e b => opt_uses usesVD decl (usesE e (usesS b acc))
    | Sfor init decl test incr b =>
        opt_uses usesS init (opt_uses usesVD decl
          (opt_uses usesE test (opt_uses usesD incr (usesS b acc))))
    | Sdo b e => usesS b (usesE e acc)
    | Sswitch init decl e b =>
        opt_uses usesS init (opt_uses usesVD decl (usesE e (usesS b acc)))
    | Scase _ | Sdefault | Sbreak | Scontinue | Sgoto _ => acc
    | Sreturn oe => opt_uses usesE oe acc
    | Sreturn_nrvo x e => Uaddr x :: usesE e acc
    | Sexpr e => usesD e acc
    | Sattr _ s | Slabeled _ s => usesS s acc
    | Sasm _ _ _ _ _ | Sunsupported _ => Uopaque :: acc
    end.

  Definition is_opaque (u : use) : bool := if u is Uopaque then true else false.
  Definition use_name (u : use) : list localname :=
    match u with Uread x | Uaddr x => [x] | Uopaque => [] end.
  Definition addr_name (u : use) : list localname :=
    match u with Uaddr x => [x] | _ => [] end.

  (** Names used anywhere in [s]: a superset of its free names. *)
  Definition names (s : Stmt) : list localname := usesS s [] ≫= use_name.

  Definition mem (x : localname) (xs : list localname) : bool :=
    existsb (fun y => bool_decide (x = y)) xs.

  (** ** Configuration *)

  (** Which widenings of the SkyLabsAI/BRiCk#531 subset are enabled.
      [pr_subset] is that subset; [full] is what the trusted rule uses. *)
  Record config : Set := {
    (* (a) <<if>> (without init/condition declaration) inside a suffix *)
    cfg_cond_suffix : bool;
    (* (b) a <<void>> function whose suffix ends at the closing brace *)
    cfg_void_fallthrough : bool;
    (* (c) jumps from inside loops and <<switch>> bodies *)
    cfg_loops : bool;
    (* (c) jumps leaving scalar, non-escaping bindings ([X] above) *)
    cfg_scope_exit : bool;
    (* (d) jumps over scalar declarations without initializer ([S] above) *)
    cfg_skip_vacuous : bool;
  }.

  Definition pr_subset : config := Build_config false false false false false.
  Definition full : config := Build_config true true true true true.

  Section with_config.
    Context (cfg : config).

    (** ** Suffixes *)

    (** Statements that may occur in a copied suffix (condition 5). Top-level
        labels of the body are erased before this check, so any label here is
        nested and rejected. *)
    Fixpoint suffix_ok (s : Stmt) : bool :=
      match s with
      | Sseq ss => forallb suffix_ok ss
      | Sexpr _ | Sreturn _ => true
      | Sif None None _ a b => cfg.(cfg_cond_suffix) && suffix_ok a && suffix_ok b
      | Sattr _ s => suffix_ok s
      | _ => false
      end.

    Record label_info : Set := {
      li_copy : Stmt;              (* what replaces <<goto L;>> *)
      li_fv : list localname;      (* superset of the names the copy uses *)
      li_ok : bool;                (* the suffix is valid (conditions 4, 5) *)
      li_blocked : bool;           (* a non-skippable declaration lies between
                                      the current position and the label *)
    }.

    Definition table : Set := list (ident * label_info).

    Fixpoint lookup (L : ident) (t : table) : option label_info :=
      match t with
      | [] => None
      | (L', li) :: t => if bool_decide (L = L') then Some li else lookup L t
      end.

    (** Condition 3: can a jump to a label whose suffix uses [fv] skip [d]? *)
    Definition skippable (fv : list localname) (d : VarDecl) : bool :=
      match d with
      | Dvar x ty None => cfg.(cfg_skip_vacuous) && is_scalar_type ty && negb (mem x fv)
      | Dvar _ _ (Some _) | Ddecompose _ _ _ => false
      | Dinit _ _ _ _ => cfg.(cfg_skip_vacuous)
      end.

    (** Condition 2: a binding that a jump may leave early, if the suffix does
        not use it. [None] is a binding no jump may leave. *)
    Definition entry : Set := option localname.

    Definition decl_entries (esc : list localname) (d : VarDecl) : list entry :=
      match d with
      | Dvar x ty _ =>
          [if cfg.(cfg_scope_exit) && is_scalar_type ty && negb (mem x esc) then Some x else None]
      | Ddecompose _ _ _ => [None]
      (* a function-local static extends no region and is not destroyed at
         scope exit, see [wp_decl] *)
      | Dinit _ _ _ _ => []
      end.

    Definition opt_decl_entries (esc : list localname) (d : option VarDecl) : list entry :=
      match d with Some d => decl_entries esc d | None => [] end.

    (** The bindings an <<if>>/<<for>>/<<switch>> init-statement adds. *)
    Definition init_entries (esc : list localname) (s : option Stmt) : list entry :=
      match s with
      | Some (Sdecl ds) => ds ≫= decl_entries esc
      | _ => []
      end.

    Definition goto_ok (ex : list entry) (li : label_info) : bool :=
      li.(li_ok) && negb li.(li_blocked) &&
      forallb (fun en => match en with
                      | Some x => negb (mem x li.(li_fv))
                      | None => false
                      end) ex.

    Section lower.
      Context (esc : list localname) (tbl : table).

      (** [lower in_loop ex s] replaces the gotos in [s], a statement not at the
          top level of the body; [ex] are the extra bindings in scope. *)
      Fixpoint lower (in_loop : bool) (ex : list entry) (s : Stmt) {struct s} : option Stmt :=
        let lower_opt in_loop ex (o : option Stmt) : option (option Stmt) :=
          match o with
          | Some s => Some <$> lower in_loop ex s
          | None => Some None
          end
        in
        match s with
        | Sseq ss =>
            let fix lower_list ex ss : option (list Stmt) :=
              match ss with
              | [] => Some []
              | Sdecl ds :: ss =>
                  (* [wp_block] extends the region here, for the rest of [ss] *)
                  cons (Sdecl ds) <$> lower_list (ex ++ (ds ≫= decl_entries esc)) ss
              | s :: ss =>
                  s' ← lower in_loop ex s;
                  ss' ← lower_list ex ss;
                  Some (s' :: ss')
              end
            in Sseq <$> lower_list ex ss
        | Sdecl _ => Some s
        | Sif init decl e a b =>
            (* [wp_if] runs [Sseq (init ++ [Sdecl decl] ++ [Sif None None ...])] *)
            let ex' := ex ++ init_entries esc init ++ opt_decl_entries esc decl in
            init' ← lower_opt in_loop ex init;
            a' ← lower in_loop ex' a;
            b' ← lower in_loop ex' b;
            Some (Sif init' decl e a' b')
        | Sif_consteval a b =>
            a' ← lower in_loop ex a;
            b' ← lower in_loop ex b;
            Some (Sif_consteval a' b')
        | Swhile decl e b =>
            (* <<return>> passes through [Kloop] *)
            Swhile decl e <$> lower true (ex ++ opt_decl_entries esc decl) b
        | Sfor init decl test incr b =>
            (* [wp_for_init] runs [Sseq [init; Sfor None ...]] *)
            init' ← lower_opt in_loop ex init;
            b' ← lower true (ex ++ init_entries esc init ++ opt_decl_entries esc decl) b;
            Some (Sfor init' decl test incr b')
        | Sdo b e => (fun b => Sdo b e) <$> lower true ex b
        | Sswitch init decl e b =>
            (* <<return>> passes through [Kswitch]; the copies hold no
               [Scase]/[Sdefault], so [wp_switch_block] sees the same cases *)
            init' ← lower_opt in_loop ex init;
            b' ← lower true (ex ++ init_entries esc init ++ opt_decl_entries esc decl) b;
            Some (Sswitch init' decl e b')
        | Sattr attrs s => Sattr attrs <$> lower in_loop ex s
        | Sgoto L =>
            if in_loop && negb cfg.(cfg_loops) then None else
            li ← lookup L tbl;
            if goto_ok ex li then Some li.(li_copy) else None
        (* labels nested anywhere but the top level, and syntax that can hide
           jumps, reject the whole body *)
        | Slabeled _ _ | Sasm _ _ _ _ _ | Sunsupported _ => None
        | Scase _ | Sdefault | Sbreak | Scontinue
        | Sreturn _ | Sreturn_nrvo _ _ | Sexpr _ => Some s
        end.
    End lower.

    (** ** The backward pass over the top-level statements *)

    Fixpoint unlabel (s : Stmt) : list ident * Stmt :=
      match s with
      | Slabeled L s => let '(Ls, s) := unlabel s in (L :: Ls, s)
      | _ => ([], s)
      end.

    Record state : Set := {
      st_tail : list Stmt;            (* suffix from the current position, unlabeled *)
      st_tail_ok : bool;
      st_tail_fv : list localname;
      st_tbl : table;                 (* labels at or after the current position *)
      st_out : list Stmt;             (* lowered statements from the current position *)
    }.

    Definition add_label (st : state) (L : ident) : option state :=
      if lookup L st.(st_tbl) is Some _ then None (* duplicate label *) else
      let li := {| li_copy := Sseq st.(st_tail); li_fv := st.(st_tail_fv);
                   li_ok := st.(st_tail_ok); li_blocked := false |} in
      Some {| st_tail := st.(st_tail); st_tail_ok := st.(st_tail_ok);
              st_tail_fv := st.(st_tail_fv); st_tbl := (L, li) :: st.(st_tbl);
              st_out := st.(st_out) |}.

    Definition block (ds : list VarDecl) (Lli : ident * label_info) : ident * label_info :=
      let '(L, li) := Lli in
      (L, {| li_copy := li.(li_copy); li_fv := li.(li_fv); li_ok := li.(li_ok);
             li_blocked := li.(li_blocked) || negb (forallb (skippable li.(li_fv)) ds) |}).

    Definition step (esc : list localname) (s : Stmt) (st : state) : option state :=
      let '(Ls, s0) := unlabel s in
      st ← match s0 with
           | Sdecl ds =>
               (* top-level declarations form the shared prefix [P] of the
                  gotos before them, and the skipped part [S] of the labels
                  after them *)
               Some {| st_tail := s0 :: st.(st_tail); st_tail_ok := false;
                       st_tail_fv := st.(st_tail_fv);
                       st_tbl := block ds <$> st.(st_tbl);
                       st_out := s0 :: st.(st_out) |}
           | _ =>
               s0' ← lower esc st.(st_tbl) false [] s0;
               Some (if s0 is Sreturn _
                     then (* the rest is dead code: drop it from copies *)
                       {| st_tail := [s0]; st_tail_ok := true;
                          st_tail_fv := names s0;
                          st_tbl := st.(st_tbl); st_out := s0' :: st.(st_out) |}
                     else
                       {| st_tail := s0 :: st.(st_tail);
                          st_tail_ok := st.(st_tail_ok) && suffix_ok s0;
                          st_tail_fv := names s0 ++ st.(st_tail_fv);
                          st_tbl := st.(st_tbl); st_out := s0' :: st.(st_out) |})
           end;
      fold_left (fun ost L => ost ≫= fun st => add_label st L) Ls (Some st).

    Fixpoint has_goto_or_label (s : Stmt) : bool :=
      match s with
      | Sseq ss => existsb has_goto_or_label ss
      | Sif init _ _ a b =>
          (if init is Some i then has_goto_or_label i else false) ||
          has_goto_or_label a || has_goto_or_label b
      | Sif_consteval a b => has_goto_or_label a || has_goto_or_label b
      | Swhile _ _ b | Sdo b _ | Sattr _ b => has_goto_or_label b
      | Sfor init _ _ _ b | Sswitch init _ _ b =>
          (if init is Some i then has_goto_or_label i else false) || has_goto_or_label b
      | Slabeled _ _ | Sgoto _ => true
      | _ => false
      end.

    Definition is_void (rt : type) : bool := if drop_qualifiers rt is Tvoid then true else false.

    (** [lower_goto_cfg rt body]: [rt] is the declared return type. Returns
        [None] when [body] has neither gotos nor labels (nothing to do), so
        that proofs of goto-free functions never depend on the trusted rule. *)
    Definition lower_goto_cfg (rt : type) (body : Stmt) : option Stmt :=
      match body with
      | Sseq items =>
          if negb (has_goto_or_label body) then None else
          let us := usesS body [] in
          if existsb is_opaque us then None else
          let esc := us ≫= addr_name in
          let void := cfg.(cfg_void_fallthrough) && is_void rt in
          let init := {| st_tail := if void then [Sreturn None] else [];
                         st_tail_ok := void; st_tail_fv := [];
                         st_tbl := []; st_out := [] |} in
          st ← fold_right (fun s ost => ost ≫= step esc s) (Some init) items;
          let body' := Sseq st.(st_out) in
          (* by construction; checked so that the trusted rule never sees one *)
          if has_goto_or_label body' then None else Some body'
      | _ => None
      end.
  End with_config.

  Definition lower_goto : type -> Stmt -> option Stmt := lower_goto_cfg full.
End goto_lowering.
