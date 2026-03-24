{- -*- agdarya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br") -*- -}

import "isfibrant"
import "bookhott"
import "hott_bookhott"

section single ≔

  {- In the simplest higher coinductive type √, the type we take a √ of has to be global, not a parameter, since then it would get degenerated when defining the type of the destructor.  This is the syntactic analogue of the fact that √ is not a fibered functor. -}

  postulate A : Set
  postulate 𝕗A : isFibrant A

  {- We can, however, include another non-higher destructor that depends on parameters. -}
  √A× : (B : Set) → Set
  √A× B = codata [ root⟨p⟩ x : A | else x : B ]

  {- The Id-types of a √ are another √.  Unfortunately, since the higher output A has to be global, we can't define a sufficiently general form of √ for this to be simply an instance of it.  So we define it as its own type. -}
  √IdA× : (B0 B1 : Set) → (B2 : Br Set B0 B1) → (x0 : √A× B0) → (x1 : √A× B1) → Set
  √IdA× B0 B1 B2 x0 x1 = codata [
  | root⟨p⟩ z : Br A (x0.2 root) (x1.2 root)
  | root1 z : A
  | else z : B2 (x0 else) (x1 else) ]

  {- We can at least prove both directions of the isomorphism. -}
  id√_iso : (B0 B1 : Set) → (B2 : Br Set B0 B1) → (x0 : √A× B0) → (x1 : √A× B1) → √IdA× B0 B1 B2 x0 x1 ≅ Br √A× B2 x0 x1
  id√_iso B0 B1 B2 x0 x1 = adjointify (√IdA× B0 B1 B2 x0 x1) (Br √A× B2 x0 x1)
        (y2 ↦
         record { root⟨p⟩ = y2⟨2⟩ root; root⟨1⟩ = y2 root1; else = y2 else })
        (x2 ↦
         record { root⟨p⟩ = x2⟨2⟩ root⟨2⟩; root1 = x2 root; else = x2 else })
        {- Proving the roundtrip equalities would require some kind of coinductive extensionality for √s.  However, it's not immediately clear how to even formulate this as an postulate, since for the clause dealing with the higher case it would have to degenerate the context. -}
        (y2 ↦ ?) (x2 ↦ ?)

  {- Now we can prove fibrancy of √A×, except for the recursive case that would be fibrancy of Id√A×, since the latter can't be an instance of the former. -}
  𝕗√A× : (B : Set) → (𝕗B : isFibrant B) → isFibrant (√A× B)
  𝕗√A× B 𝕗B = record {
    trr⟨p⟩ = λ x0 → record { root⟨p⟩ = x0⟨2⟩ root; else = 𝕗B.2 trr (x0 else) };
    trl⟨p⟩ = λ x1 → record { root⟨p⟩ = x1⟨2⟩ root; else = 𝕗B.2 trl (x1 else) };
    liftr⟨p⟩ = λ x0 → record {
      root⟨p⟩ = rel x0⟨2⟩ root⟨1⟩;
      root⟨1⟩ = rel x0 root;
      else = 𝕗B.2 liftr (x0 else) };
    liftl⟨p⟩ = λ x1 → record {
      root⟨p⟩ = rel x1⟨2⟩ root⟨1⟩;
      root⟨1⟩ = rel x1 root;
      else = 𝕗B.2 liftl (x1 else) };
    id⟨p⟩ = λ x0 x1 →
      𝕗eqv (√IdA× B.0 B.1 B.2 x0 x1) (Br √A× B.2 x0 x1)
        (id√_iso B.0 B.1 B.2 x0 x1) ? }

end

section parametrized ≔

  {- We can also consider higher destructors whose typse depend on the parameters, but they have to depend on a degenerated version of the parameters.  In this case, however, it seems that we require the *parameter* to be fibrant as well. -}
  postulate Γ : Set
  postulate 𝕗Γ : isFibrant Γ
  postulate A (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) : Set
  postulate 𝕗A (x₀ x₁ : Γ) (x₂ : Br Γ x₀ x₁) : isFibrant (A x₀ x₁ x₂)

  {- For simplicity, we leave off any lower destructors. -}
  √A : (x : Γ) → Set
  √A x = codata [ root⟨p⟩ a : A x⟨0⟩ x⟨1⟩ x⟨2⟩ ]

  𝕗√A : (x : Γ) → isFibrant (√A x)
  𝕗√A x = record {
    trr⟨p⟩ = λ a₀ → record {
      root⟨p⟩ = rel 𝕗A x⟨20⟩ x⟨21⟩ (sym x⟨22⟩) trr (a₀.2 root) };
    trl⟨p⟩ = λ a₁ → record {
      root⟨p⟩ = rel 𝕗A x⟨20⟩ x⟨21⟩ (sym x⟨22⟩) trl (a₁.2 root) };
    liftr⟨p⟩ = λ a₀ → record {
      root⟨p⟩ = rel 𝕗A x⟨20⟩ x⟨21⟩ (sym x⟨22⟩) liftr (a₀.2 root);
      root⟨1⟩ =
        rel 𝕗A (rel x⟨0⟩) x⟨2⟩ (coconn (Γ, 𝕗Γ) x⟨0⟩ x⟨1⟩ x⟨2⟩) trr
          (rel a₀ root) };
    liftl⟨p⟩ = λ a₁ → record {
      root⟨p⟩ = rel 𝕗A x⟨20⟩ x⟨21⟩ (sym x⟨22⟩) liftl (a₁.2 root);
      root⟨1⟩ =
        rel 𝕗A x⟨2⟩ (rel x⟨1⟩) (conn (Γ, 𝕗Γ) x⟨0⟩ x⟨1⟩ x⟨2⟩) trl
          (rel a₁ root) };
    id⟨p⟩ = λ a₀ a₁ → ? }

end
