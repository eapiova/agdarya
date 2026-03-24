The parsing of "(X:Set)->Y" is technically ambiguous: in addition to
a dependent function-type, it could be a non-dependent function type
with ascribed domain.  We always interpret it as a dependent
function-type, but to get the non-dependent version you can add extra
parentheses.

  $ agdarya -e 'A : Set' -e 'A = Set' -e 'postulate x : Set' -e 'postulate B : Set' -e 'echo (x:A) -> B'
  (x : Set) → B
    : Set
  

  $ agdarya -e 'A : Set' -e 'A = Set' -e 'postulate x : Set' -e 'postulate B : Set' -e 'echo ((x:A)) -> B'
  x → B
    : Set
  

  $ agdarya -e 'A : Set' -e 'A = Set' -e 'postulate x : Set' -e 'postulate B : Set' -e 'echo ((x):A) -> B'
  x → B
    : Set
  

There was once a bug with expressions like this, so we test for it.

  $ agdarya -e "echo (A:Set) → (A:Set) → A"
  (A : Set) (A′ : Set) → A′
    : Set
  
