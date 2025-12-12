  $ . ../setup-project.sh

Compiling the Coq test file.
  $ dune build
  1 goal
    
    thread_info : biIndex
    _Σ : gFunctors
    Σ : cpp_logic thread_info _Σ
    σ : genv
    ============================
    ∀ this : ptr, this ,, o_field σ "C::foo" |-> anyR "int" 1$m ⊢ emp
  1 goal
    
    thread_info : biIndex
    _Σ : gFunctors
    Σ : cpp_logic thread_info _Σ
    σ : genv
    ============================
    ∀ this : ptr, this ,, o_field σ "C::foo" |-> anyR "int" 1$m ⊢ emp
  "foo"%cpp_name
       : name
  "foo::bar"%cpp_name
       : name
