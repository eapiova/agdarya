  $ agdarya asclam.ny -e "postulate C : Set echo ((x : A) ↦ ()) : C → unit"
  λ x → x
    : (x : A) → A
  
  λ x → g x (f x)
    : (x : A) → C x
  
  a
    : A
  
  g a (f a)
    : C a
  
  λ x → ()
    : A → unit
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | postulate C : Set echo ((x : A) ↦ ()) : C → unit
     ^ term synthesized type
         A
       but is being checked against type
         C
       unequal head constants:
         C
       does not equal
         A
  
  [1]
