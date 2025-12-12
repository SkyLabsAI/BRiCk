Require Import bluerock.lang.cpp.cpp.

Section with_cpp.
  Context `{Σ : cpp_logic}.

  #[local] Notation WPP := (WpSpec_cpp_val).

  Definition _1 : WPP :=
    \pre emp
    \post  emp.
  Print _1.

  Definition _2 : _ -> WPP :=
    \this this
    \pre emp
    \post  emp.
  Print _2.

  Definition _3 : WPP :=
    \with (I J : mpred) (p : ptr) (R : Qp -> Qp -> nat -> Rep)
    \prepost emp
    \require True
    \require{x} x = 1
    \arg{n (nn: nat)} "foo" (Vint n)
    \with (z : nat) (a : nat)
    \prepost emp
    \prepost{q1 q2} p |-> R q1 q2 0
    \pre{q3 q4} p |-> R q3 q4 0
    \pre emp ** Exists y : nat, [| a = 7 |] ** [| y = 3 |] ** I ** J
    \post{x}[ Vint x ] emp.
  Print _3.

  Definition _4 : WPP :=
   \with (I J : mpred)
   \with  (a : nat)
   \prepost emp
   \with (z : nat)
   \prepost emp
   \pre emp ** Exists y : nat, [| a = 7 |] ** [| y = 3 |] ** I ** J
   \post{r}[ r ] emp.
  Print _4.

  Definition _5 : WPP :=
   \with (I J : mpred) (n : nat)
   \with  (a : nat)
   \let x := 3%nat
   \with (lm : nat * nat)
   \let '(l,m) := lm
   \require l+m = 3
   \prepost emp
   \persist emp
   \persist{n1} [| n1 = 1 |]
   \persist{n2} [| n2 = 1 |]%N
   \persist{z} [| z = 1 |]%Z
   \with (z : nat)
   \arg{(zz : Z)} "foo" (Vint zz)
   \prepost emp
   \with (zzz : Type)
   \pre emp ** Exists y : nat, [| a = 7 |] ** [| y = 3 |] ** I ** J
   \post emp.
  Print _5.

  Definition _6 : WPP :=
    \pre emp ** Exists y : nat, [| y = 3 |]
    \post[Vptr nullptr] emp.
  Print _6.

  Definition _7 : WPP :=
    \pre |==> True ** |={∅,⊤}=> False
    \post[Vptr nullptr] emp.
  Print _7.

  Definition _8 : WPP :=
    \pre |==> True ** |={∅,⊤}=> False
    \post[Vvoid] emp.
  Print _8.

End with_cpp.
