  $ . ../setup-project.sh

Compiling the Coq test file.
  $ dune build
  _1 = \pre emp 
       \post    emp
       : WPP
  
  _1 uses section variables thread_info _Σ.
  _2 = λ _ : ptr, \pre emp 
                  \post    emp
       : ptr → WPP
  
  _2 uses section variables thread_info _Σ.
  _3 =
  \prepost{(I J : mpred) (p : ptr) (R : Qp → Qp → nat → Rep)} emp
  \require True
  \require{x : nat} x = 1
  \arg{(n : Z) (_ : nat)} "foo" n
  \prepost{_ a : nat} emp
  \prepost{q1 q2 : Qp} p |-> R q1 q2 0
  \pre{q3 q4 : Qp} p |-> R q3 q4 0
  \pre emp ∗ ∃ y : nat, [| a = 7 |] ∗ [| y = 3 |] ∗ I ∗ J 
  \post{x0 : Z}[x0]
           emp
       : WPP
  
  _3 uses section variables thread_info _Σ Σ.
  _4 =
  \prepost{(I J : mpred) (a : nat)} emp
  \prepost{_ : nat} emp
  \pre emp ∗ ∃ y : nat, [| a = 7 |] ∗ [| y = 3 |] ∗ I ∗ J 
  \post{r : val}[r]
           emp
       : WPP
  
  _4 uses section variables thread_info _Σ.
  _5 =
  \let{(I J : mpred) (_ a : nat)}     x := 3
  \with    (lm : nat * nat)
  let_pre_spec
    (let
     '(l, m) := lm in
      \require l + m = 3
      \prepost emp
      \persist emp
      \persist{n1 : nat} [| n1 = 1 |]
      \persist{n2 : N} [| n2 = 1%N |]
      \persist{z : Z} [| z = 1%Z |]
      \arg{(_ : nat) (zz : Z)} "foo" zz
      \prepost emp
      \pre{_ : Type} emp ∗ ∃ y : nat, [| a = 7 |] ∗ [| y = 3 |] ∗ I ∗ J
      \post    emp)
       : WPP
  
  _5 uses section variables thread_info _Σ.
  _6 =
  \pre emp ∗ ∃ y : nat, [| y = 3 |] 
  \post[Vptr nullptr]
           emp
       : WPP
  
  _6 uses section variables thread_info _Σ.
  _7 =
  \pre |==> True ∗ (|={∅,⊤}=> False) 
  \post[Vptr nullptr]
           emp
       : WPP
  
  _7 uses section variables thread_info _Σ Σ.
  _8 = \pre |==> True ∗ (|={∅,⊤}=> False) 
       \post[Vvoid]
                emp
       : WPP
  
  _8 uses section variables thread_info _Σ Σ.
