  $ agdarya degconstr.ny
  left (refl a)
    : Sum⁽ᵉ⁾ (Id A) (Id B) (left a) (left a)
  
  left (refl a)
    : Sum⁽ᵉ⁾ (Id A) (Id B) (left a) (left a)
  
  nil
    : List⁽ᵉ⁾ (Id A) nil nil
  
   ￫ error[E0400]
   ￭ $TESTCASE_ROOT/degconstr.ny
   1 | echo refl (cons a (cons a nil))
     ^ non-synthesizing term in synthesizing position (argument of degeneracy)
  
  [1]

  $ agdarya -e 'import "degconstr" echo refl nil : List A'
  left (refl a)
    : Sum⁽ᵉ⁾ (Id A) (Id B) (left a) (left a)
  
  left (refl a)
    : Sum⁽ᵉ⁾ (Id A) (Id B) (left a) (left a)
  
  nil
    : List⁽ᵉ⁾ (Id A) nil nil
  
   ￫ error[E0400]
   ￭ $TESTCASE_ROOT/degconstr.ny
   1 | echo refl (cons a (cons a nil))
     ^ non-synthesizing term in synthesizing position (argument of degeneracy)
  
  [1]


  $ agdarya -e 'import "degconstr" postulate a1 : A echo refl (cons a nil) : Id (List A) (cons a nil) (cons a1 nil)'
  left (refl a)
    : Sum⁽ᵉ⁾ (Id A) (Id B) (left a) (left a)
  
  left (refl a)
    : Sum⁽ᵉ⁾ (Id A) (Id B) (left a) (left a)
  
  nil
    : List⁽ᵉ⁾ (Id A) nil nil
  
   ￫ error[E0400]
   ￭ $TESTCASE_ROOT/degconstr.ny
   1 | echo refl (cons a (cons a nil))
     ^ non-synthesizing term in synthesizing position (argument of degeneracy)
  
  [1]

  $ agdarya degnumeral.ny
  refl 3
    : ℕ⁽ᵉ⁾ 3 3
  
  3⁽ᵉᵉ⁾
    : ℕ⁽ᵉᵉ⁾ {3} {3} (refl 3) {3} {3} (refl 3) (refl 3) (refl 3)
  
  3⁽ᵉᵉ⁾
    : ℕ⁽ᵉᵉ⁾ {3} {3} (refl 3) {3} {3} (refl 3) (refl 3) (refl 3)
  

  $ agdarya -e 'ℕ : Set' -e 'ℕ = data [ zero | suc (_ : ℕ) ]' -e 'echo refl 3 : ℕ'
   ￫ error[E0602]
   ￭ command-line exec string
   1 | echo refl 3 : ℕ
     ^ insufficient dimension for expected type of degeneracy 'refl':
        0 does not factor through e
  
  [1]

  $ agdarya degtuple.ny
  (refl a, refl b)
    : Prod⁽ᵉ⁾ (Id A) (Id B) (a, b) (a, b)
  
  (fst ≔ refl a, snd ≔ refl b)
    : Prod⁽ᵉ⁾ (Id A) (Id B) (a, b) (a, b)
  
  (snd ≔ refl b, fst ≔ refl a)
    : Prod⁽ᵉ⁾ (Id A) (Id B) (a, b) (a, b)
  

  $ agdarya -v symabs.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate a00 assumed
  
   ￫ info[I0001]
   ￮ postulate a01 assumed
  
   ￫ info[I0001]
   ￮ postulate a02 assumed
  
   ￫ info[I0001]
   ￮ postulate a10 assumed
  
   ￫ info[I0001]
   ￮ postulate a11 assumed
  
   ￫ info[I0001]
   ￮ postulate a12 assumed
  
   ￫ info[I0001]
   ￮ postulate a20 assumed
  
   ￫ info[I0001]
   ￮ postulate a21 assumed
  
   ￫ info[I0001]
   ￮ postulate a22 assumed
  
   ￫ info[I0001]
   ￮ postulate B assumed
  
   ￫ info[I0001]
   ￮ postulate b00 assumed
  
   ￫ info[I0001]
   ￮ postulate b01 assumed
  
   ￫ info[I0001]
   ￮ postulate b02 assumed
  
   ￫ info[I0001]
   ￮ postulate b10 assumed
  
   ￫ info[I0001]
   ￮ postulate b11 assumed
  
   ￫ info[I0001]
   ￮ postulate b12 assumed
  
   ￫ info[I0001]
   ￮ postulate b20 assumed
  
   ￫ info[I0001]
   ￮ postulate b21 assumed
  
   ￫ info[I0001]
   ￮ postulate b22 assumed
  
   ￫ info[I0000]
   ￮ constant prod defined
  
   ￫ info[I0000]
   ￮ constant ab22 defined
  
   ￫ info[I0000]
   ￮ constant sym_ab22 defined
  
   ￫ info[I0000]
   ￮ constant sym_ab22' defined
  
   ￫ info[I0001]
   ￮ postulate f00 assumed
  
   ￫ info[I0001]
   ￮ postulate f01 assumed
  
   ￫ info[I0001]
   ￮ postulate f02 assumed
  
   ￫ info[I0001]
   ￮ postulate f10 assumed
  
   ￫ info[I0001]
   ￮ postulate f11 assumed
  
   ￫ info[I0001]
   ￮ postulate f12 assumed
  
   ￫ info[I0001]
   ￮ postulate f20 assumed
  
   ￫ info[I0001]
   ￮ postulate f21 assumed
  
   ￫ info[I0001]
   ￮ postulate f22 assumed
  
   ￫ info[I0000]
   ￮ constant etaf22 defined
  
   ￫ info[I0000]
   ￮ constant eta_symf22 defined
  
   ￫ info[I0000]
   ￮ constant eta_symf22' defined
  

  $ agdarya deglam.ny
  ap λ x → f x
    : {x₀ : A} {x₁ : A} (x₂ : Id A x₀ x₁) →⁽ᵉ⁾ Id B x₂ (f x₀) (f x₁)
  
  x ⤇ refl f x.2
    : {x₀ : A} {x₁ : A} (x₂ : Id A x₀ x₁) →⁽ᵉ⁾ Id B x₂ (f x₀) (f x₁)
  

  $ agdarya deglamtuple.ny
   ￫ error[E0400]
   ￭ $TESTCASE_ROOT/deglamtuple.ny
   1 | synth refl (x ↦ (f x, g x))
     ^ non-synthesizing term in synthesizing position (argument of degeneracy)
  
  [1]

  $ agdarya -e 'import "deglamtuple" synth refl (x ↦ (f x, g x)) : (x : A) → Prod (B x) (C x)'
   ￫ error[E0400]
   ￭ $TESTCASE_ROOT/deglamtuple.ny
   1 | synth refl (x ↦ (f x, g x))
     ^ non-synthesizing term in synthesizing position (argument of degeneracy)
  
  [1]

  $ agdarya degblank.ny
  refl a
    : Id A a a
  
  refl a
    : Id A a a
  
  (refl a)⁽¹ᵉ⁾
    : A⁽ᵉᵉ⁾ (refl a) (refl a) (refl a) (refl a)
  
  a⁽ᵉᵉ⁾
    : A⁽ᵉᵉ⁾ (refl a) (refl a) (refl a) (refl a)
  
   ￫ error[E0400]
   ￭ $TESTCASE_ROOT/degblank.ny
   1 | echo refl (refl _)
     ^ non-synthesizing term in synthesizing position (argument of degeneracy)
  
  [1]


  $ agdarya -e 'import "degblank" echo refl _ : Id A a0 a1'
  refl a
    : Id A a a
  
  refl a
    : Id A a a
  
  (refl a)⁽¹ᵉ⁾
    : A⁽ᵉᵉ⁾ (refl a) (refl a) (refl a) (refl a)
  
  a⁽ᵉᵉ⁾
    : A⁽ᵉᵉ⁾ (refl a) (refl a) (refl a) (refl a)
  
   ￫ error[E0400]
   ￭ $TESTCASE_ROOT/degblank.ny
   1 | echo refl (refl _)
     ^ non-synthesizing term in synthesizing position (argument of degeneracy)
  
  [1]


  $ agdarya -e 'import "degblank" echo sym _ : Id (Id A) a2 a2 (refl a0) (refl a1)'
  refl a
    : Id A a a
  
  refl a
    : Id A a a
  
  (refl a)⁽¹ᵉ⁾
    : A⁽ᵉᵉ⁾ (refl a) (refl a) (refl a) (refl a)
  
  a⁽ᵉᵉ⁾
    : A⁽ᵉᵉ⁾ (refl a) (refl a) (refl a) (refl a)
  
   ￫ error[E0400]
   ￭ $TESTCASE_ROOT/degblank.ny
   1 | echo refl (refl _)
     ^ non-synthesizing term in synthesizing position (argument of degeneracy)
  
  [1]
