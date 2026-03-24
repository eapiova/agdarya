  $ cat >test.ny <<EOF
  > postulate A:Set
  > postulate a0:A
  > postulate a1:A
  > postulate a2: Id A a0 a1
  > a2' = refl ((λ y → let id : A → A = λ x → x in id y) : A → A)
  > echo a2'
  > EOF

  $ agdarya -v test.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate a0 assumed
  
   ￫ info[I0001]
   ￮ postulate a1 assumed
  
   ￫ info[I0001]
   ￮ postulate a2 assumed
  
   ￫ info[I0000]
   ￮ constant a2' defined
  
  y ⤇ y.2
    : {𝑥₀ : A} {𝑥₁ : A} (𝑥₂ : Id A 𝑥₀ 𝑥₁) →⁽ᵉ⁾ Id A 𝑥₀ 𝑥₁
  
