  $ agdarya -e 'S1 : Set' -e 'S1 = data [ | base | .loop.e. : refl S1 base base ]' -e 'echo loop : refl S1 base base' -e 'echo base : S1'
  loop
    : S1⁽ᵉ⁾ base base
  
  base
    : S1
  

  $ agdarya -e 'I : Set' -e 'I = data [ | left | right | .seg.e. : refl I left right ]' -e 'echo seg : refl I left right' -e 'echo left : I' -e 'echo right : I'
  seg
    : I⁽ᵉ⁾ left right
  
  left
    : I
  
  right
    : I
  

  $ agdarya term-suffix.ny
   ￫ error[E0100]
   ￭ $TESTCASE_ROOT/term-suffix.ny
   1 | echo .loop.e. : refl S1 base base
     ^ unimplemented: higher constructors in terms
  
  [1]

  $ agdarya pattern-suffix.ny
   ￫ error[E0100]
   ￭ $TESTCASE_ROOT/pattern-suffix.ny
   3 | | .loop.e. ↦ loop
     ^ unimplemented: higher constructors in match patterns
  
  [1]
