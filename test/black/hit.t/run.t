  $ narya -e 'def S1 : Type ≔ data [ | base. | loop.e. : refl S1 base. base. ]' -e 'echo loop. : refl S1 base. base.' -e 'echo base. : S1'
  loop.
    : S1⁽ᵉ⁾ base. base.
  
  base.
    : S1
  

  $ narya -e 'def I : Type ≔ data [ | left. | right. | seg.e. : refl I left. right. ]' -e 'echo seg. : refl I left. right.' -e 'echo left. : I' -e 'echo right. : I'
  seg.
    : I⁽ᵉ⁾ left. right.
  
  left.
    : I
  
  right.
    : I
  

  $ narya term-suffix.ny
   ￫ error[E0100]
   ￭ $TESTCASE_ROOT/term-suffix.ny
   5 | echo loop.e. : refl S1 base. base.
     ^ unimplemented: higher constructors in terms
  
  [1]

  $ narya pattern-suffix.ny
   ￫ error[E0100]
   ￭ $TESTCASE_ROOT/pattern-suffix.ny
   7 | | loop.e. ↦ loop.
     ^ unimplemented: higher constructors in match patterns
  
  [1]
