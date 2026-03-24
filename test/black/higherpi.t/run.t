  $ agdarya -v higherpi.ny -e "echo Id ((x : A) → B x) f g" -e "echo ((x : A) → B x)⁽ᵉᵉ⁾ f02 f12 f20 f21" -e "echo Id ((x : A) → B x)"
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate B assumed
  
   ￫ info[I0001]
   ￮ postulate f assumed
  
   ￫ info[I0001]
   ￮ postulate g assumed
  
   ￫ info[I0000]
   ￮ constant idok defined
  
   ￫ info[I0001]
   ￮ postulate f00 assumed
  
   ￫ info[I0001]
   ￮ postulate f01 assumed
  
   ￫ info[I0001]
   ￮ postulate f10 assumed
  
   ￫ info[I0001]
   ￮ postulate f11 assumed
  
   ￫ info[I0001]
   ￮ postulate f02 assumed
  
   ￫ info[I0001]
   ￮ postulate f12 assumed
  
   ￫ info[I0001]
   ￮ postulate f20 assumed
  
   ￫ info[I0001]
   ￮ postulate f21 assumed
  
   ￫ info[I0000]
   ￮ constant id2ok defined
  
   ￫ info[I0000]
   ￮ constant nidok defined
  
  {x₀ : A} {x₁ : A} (x₂ : Id A x₀ x₁) →⁽ᵉ⁾ Id B x₂ (f x₀) (g x₁)
    : Set
  
  {x₀₀ : A} {x₀₁ : A} {x₀₂ : Id A x₀₀ x₀₁} {x₁₀ : A} {x₁₁ : A}
  {x₁₂ : Id A x₁₀ x₁₁} {x₂₀ : Id A x₀₀ x₁₀} {x₂₁ : Id A x₀₁ x₁₁}
  (x₂₂ : A⁽ᵉᵉ⁾ x₀₂ x₁₂ x₂₀ x₂₁)
  →⁽ᵉᵉ⁾ B⁽ᵉᵉ⁾ x₂₂ (f02 x₀₂) (f12 x₁₂) (f20 x₂₀) (f21 x₂₁)
    : Set
  
  (x : Id A) ⇒ Id B x.2
    : Set⁽ᵉ⁾ ((x : A) → B x) ((x : A) → B x)
  

  $ agdarya higherpi.ny -e "echo (x₂ : refl A x₀ x₁) →⁽ᵉ⁾ refl B x₂ (f x₀) (g x₁)"
   ￫ error[E0702]
   ￭ command-line exec string
   1 | echo (x₂ : refl A x₀ x₁) →⁽ᵉ⁾ refl B x₂ (f x₀) (g x₁)
     ^ unexpected explicit domain: all boundary domains must be implicit and primary domain explicit
  
  [1]

  $ agdarya higherpi.ny -e "echo {x₀ x₁ : A} (x₂ : refl A x₀ x₁) →⁽ᵉ⁾ refl B x₂ (f x₀) (g x₁)"
  {x₀ : A} {x₁ : A} (x₂ : Id A x₀ x₁) →⁽ᵉ⁾ Id B x₂ (f x₀) (g x₁)
    : Set
  

  $ agdarya higherpi.ny -e "echo {x₀ x₁ : A} {x₂ : refl A x₀ x₁} →⁽ᵉ⁾ refl B x₂ (f x₀) (g x₁)"
   ￫ error[E0702]
   ￭ command-line exec string
   1 | echo {x₀ x₁ : A} {x₂ : refl A x₀ x₁} →⁽ᵉ⁾ refl B x₂ (f x₀) (g x₁)
     ^ unexpected implicit domain: all boundary domains must be implicit and primary domain explicit
  
  [1]

  $ agdarya higherpi.ny -e "echo {x₀ x₁ : A} (x₂ : refl (B x₀) (f x₀) (f x₀)) →⁽ᵉ⁾ refl B x₂ (f x₀) (g x₁)"
   ￫ error[E0706]
   ￭ command-line exec string
   1 | echo {x₀ x₁ : A} (x₂ : refl (B x₀) (f x₀) (f x₀)) →⁽ᵉ⁾ refl B x₂ (f x₀) (g x₁)
     ^ invalid higher function-type: invalid domain scope
  
  [1]

  $ agdarya higherpi.ny -e "echo {x₀ x₁ : A} (x₂ : A) →⁽ᵉ⁾ refl B x₂ (f x₀) (g x₁)"
   ￫ error[E0706]
   ￭ command-line exec string
   1 | echo {x₀ x₁ : A} (x₂ : A) →⁽ᵉ⁾ refl B x₂ (f x₀) (g x₁)
     ^ invalid higher function-type: invalid domain
  
  [1]

  $ agdarya higherpi.ny -e "echo {x₀ x₁ : A} (x₂ : Id A x₀ x₀) →⁽ᵉ⁾ refl B x₂ (f x₀) (g x₁)"
   ￫ error[E0706]
   ￭ command-line exec string
   1 | echo {x₀ x₁ : A} (x₂ : Id A x₀ x₀) →⁽ᵉ⁾ refl B x₂ (f x₀) (g x₁)
     ^ invalid higher function-type: invalid domain boundary
  
  [1]

  $ agdarya higherpi.ny -e "echo {x₀ x₁ : A} (x₂ : refl A x₀ x₁) →⁽ᵉ⁾ refl (B x₀) (f x₀) (g x₀)"
   ￫ error[E0706]
   ￭ command-line exec string
   1 | echo {x₀ x₁ : A} (x₂ : refl A x₀ x₁) →⁽ᵉ⁾ refl (B x₀) (f x₀) (g x₀)
     ^ invalid higher function-type: invalid codomain scope
  
  [1]

  $ agdarya higherpi.ny -e "echo {x₀ x₁ : A} (x₂ : refl A x₀ x₁) →⁽ᵉ⁾ A"
   ￫ error[E0706]
   ￭ command-line exec string
   1 | echo {x₀ x₁ : A} (x₂ : refl A x₀ x₁) →⁽ᵉ⁾ A
     ^ invalid higher function-type: invalid codomain
  
  [1]

  $ agdarya higherpi.ny -e "echo (x : Id A) ⇒ A"
   ￫ error[E0706]
   ￭ command-line exec string
   1 | echo (x : Id A) ⇒ A
     ^ invalid higher function-type: invalid single codomain dimension
  
  [1]

  $ agdarya -e "echo refl ((X Y ↦ X → Y → Set) : Set → Set → Set)"
  X Y ⤇ X.2 ⇒ Y.2 ⇒ Set⁽ᵉ⁾
    : {𝑥₀ : Set} {𝑥₁ : Set} (𝑥₂ : Set⁽ᵉ⁾ 𝑥₀ 𝑥₁) {𝑦₀ : Set} {𝑦₁ : Set}
      (𝑦₂ : Set⁽ᵉ⁾ 𝑦₀ 𝑦₁)
      →⁽ᵉ⁾ Set⁽ᵉ⁾ (𝑥₀ → 𝑦₀ → Set) (𝑥₁ → 𝑦₁ → Set)
  
  $ agdarya -variables 𝑎,𝑏 -e "postulate A : Set postulate B : Set postulate f : A → B postulate g : A → B echo Id (A → B) f g"
  {𝑎₀ : A} {𝑎₁ : A} (𝑎₂ : Id A 𝑎₀ 𝑎₁) →⁽ᵉ⁾ Id B (f 𝑎₀) (g 𝑎₁)
    : Set
  

