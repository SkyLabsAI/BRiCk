Require Import skylabs.prelude.base.
Require Import skylabs.lang.cpp.syntax.
Require skylabs.lang.cpp.syntax.supported.
Require Import skylabs.lang.cpp.syntax.typed.

Require test.test_cpp.

(** * cpp2v's handling of clang's [CXXStdInitializerListExpr]

    [test.cpp] exercises the conversion of a braced-init-list to a
    <<std::initializer_list<E>>> (<https://eel.is/c++draft/dcl.init.list#5>),
    which cpp2v prints as [Einitlist_std].

    Two things shape this test.

    - It is scoped to the functions that [test.cpp] itself defines. A check over
      the whole translation unit — [supported.check.translation_unit], say —
      also reports every unsupported construct that <<<initializer_list>>>
      transitively drags in, so its expected output moves whenever the standard
      library or clang does.

    - It states where the [Einitlist_std] nodes are with [context] patterns
      naming only the constructors this feature is about. Nothing here depends
      on what *wraps* a node, so casts, [Eandclean], and the calls or
      constructors around it are free to change.

    It deliberately does not re-check that a node is well formed. <<--check-types>>
    (see the [Makefile]) runs [typed.decltype.check_tu] over the whole
    translation unit, and that already requires every [Einitlist_std backing t]
    to have [t] an instance of <<std::initializer_list>> whose template argument
    agrees with the element type of [backing]. The negative cases for that live
    beside it, in [lang/cpp/syntax/typed.v]. *)

#[local] Open Scope pstring_scope.

(** Every function of interest takes no arguments, so its identifier determines
    its name. *)
Definition lookup (fn : PrimString.string) : option ObjValue :=
  test_cpp.source.(symbols) !! Nglobal (Nfunction function_qualifiers.N fn []).

(** The body of [fn], or [None] if it is absent or not a definition. A [None]
    fails the [context] matches below rather than passing them, except for the
    one inverted match, which is paired with a positive one for that reason. *)
Definition body (fn : PrimString.string) : option Stmt :=
  match lookup fn with
  | Some (Ofunction f) =>
      match f.(f_body) with
      | Some (Impl s) => Some s
      | _ => None
      end
  | _ => None
  end.

(** ** Where the [Einitlist_std] nodes are

    NOTE: [lazymatch], not [match]. A [match] on a term backtracks into the next
    branch when the selected branch's tactic fails, which turns both the
    diagnostic [fail]s and the inverted match in [TEST_empty_list] into dead
    code that always succeeds. *)

(** <<sum({1, 2, 3})>>: an argument of class type. The backing array is a
    temporary <<const int[3]>>, so it dies with the full-expression. *)
Succeed Example TEST_pass_to_function : True :=
  ltac:(let b := eval vm_compute in (body "pass_to_function") in
        lazymatch b with
        | context [ Einitlist_std
                      (Ematerialize_temp (Einitlist [_;_;_] None (Tarray _ 3)) _) _ ] =>
            exact I
        | _ => fail 0 "no Einitlist_std over a temporary const int[3] in" b
        end).

(** <<Holder h = {1, 2, 3};>>, copy-initialization of a class with an
    <<initializer_list>> constructor. clang produces the same node here as for
    direct-initialization below; the two cases exist to pin that both C++ forms
    reach [Einitlist_std]. *)
Succeed Example TEST_copy_init_class : True :=
  ltac:(let b := eval vm_compute in (body "copy_init_class") in
        lazymatch b with
        | context [ Einitlist_std
                      (Ematerialize_temp (Einitlist [_;_;_] None (Tarray _ 3)) _) _ ] =>
            exact I
        | _ => fail 0 "no Einitlist_std over a temporary const int[3] in" b
        end).

(** <<Holder h{1, 2, 3};>>, direct-initialization. *)
Succeed Example TEST_direct_init_class : True :=
  ltac:(let b := eval vm_compute in (body "direct_init_class") in
        lazymatch b with
        | context [ Einitlist_std
                      (Ematerialize_temp (Einitlist [_;_;_] None (Tarray _ 3)) _) _ ] =>
            exact I
        | _ => fail 0 "no Einitlist_std over a temporary const int[3] in" b
        end).

(** <<sum({1, 2, 3}) + sum({})>>: two braced-init-lists in one full-expression,
    but only one backing array — clang default-constructs for <<{}>>. *)
Succeed Example TEST_nested_elements : True :=
  ltac:(let b := eval vm_compute in (body "nested_elements") in
        lazymatch b with
        | context [ Einitlist_std
                      (Ematerialize_temp (Einitlist [_;_;_] None (Tarray _ 3)) _) _ ] =>
            idtac
        | _ => fail 0 "no Einitlist_std over a temporary const int[3] in" b
        end;
        lazymatch b with
        | context [ Econstructor _ []
                      (Tnamed (Ninst std_initializer_list [Atype Tint])) ] => exact I
        | _ => fail 0 "no default-constructed std::initializer_list<int> in" b
        end).

(** <<return {{1, 2}, {3, 4}};>>: class elements, so each element of the backing
    <<const Widget[2]>> is itself a braced-init-list — an [Einitlist], not a
    nested [Einitlist_std]. *)
Succeed Example TEST_widgets : True :=
  ltac:(let b := eval vm_compute in (body "widgets") in
        lazymatch b with
        | context [ Einitlist_std
                      (Ematerialize_temp
                         (Einitlist [Einitlist [_;_] None _; Einitlist [_;_] None _] None
                            (Tarray _ 2)) _) _ ] => exact I
        | _ => fail 0 "no Einitlist_std over a temporary const Widget[2] in" b
        end).

(** <<std::initializer_list<int> l = {};>> is supported and needs no backing
    array at all, so there is no [CXXStdInitializerListExpr] to translate. *)
Succeed Example TEST_empty_list : True :=
  ltac:(let b := eval vm_compute in (body "empty_list") in
        lazymatch b with
        | context [ Einitlist_std _ _ ] => fail 0 "unexpected Einitlist_std in" b
        | _ => idtac
        end;
        lazymatch b with
        | context [ Econstructor _ []
                      (Tnamed (Ninst std_initializer_list [Atype Tint])) ] => exact I
        | _ => fail 0 "no default-constructed std::initializer_list<int> in" b
        end).

(** <<std::initializer_list<int> l = {1, 2, 3};>>: the backing array is
    lifetime-extended to match <<l>>. cpp2v still emits the [Einitlist_std]
    node; it is the scope-extruded temporary underneath that it cannot
    represent. *)
Succeed Example TEST_extended_temporary : True :=
  ltac:(let b := eval vm_compute in (body "extended_temporary") in
        lazymatch b with
        | context [ Einitlist_std (Eunsupported "MaterializeTemporaryExpr" _) _ ] =>
            exact I
        | _ => fail 0 "no Einitlist_std over a scope-extruded backing array in" b
        end).

(** ** Which of these functions BRiCk supports

    Per symbol, so that the answer does not depend on what <<<initializer_list>>>
    drags in. *)
Definition unsupported (fn : PrimString.string) : supported.check.M :=
  if lookup fn is Some o then supported.check.obj_value o else ["missing symbol"].

Succeed Example TEST_supported :
  List.concat
    (List.map unsupported
       ["pass_to_function"; "copy_init_class"; "direct_init_class";
        "nested_elements"; "widgets"; "empty_list"]) = []
  := ltac:(vm_compute; reflexivity).

Succeed Example TEST_extended_temporary_unsupported :
  unsupported "extended_temporary" = ["MaterializeTemporaryExpr"]
  := ltac:(vm_compute; reflexivity).
