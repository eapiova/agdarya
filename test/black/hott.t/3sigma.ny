 {- Transport and lifting compute on ternary Σ-types -}

Σ3 : (A : Set) → (B : A → Set) → (C : (x : A) → B x → Set) → Set

Σ3 A B C = sig ( fst : A, snd : B fst, thd : C fst snd )

postulate A₀ : Set

postulate A₁ : Set

postulate A₂ : Id Set A₀ A₁

postulate B₀ : A₀ → Set

postulate B₁ : A₁ → Set

postulate B₂ : Id ((X ↦ X → Set) : Set → Set) A₂ B₀ B₁

postulate C₀ : (x₀ : A₀) → B₀ x₀ → Set

postulate C₁ : (x₁ : A₁) → B₁ x₁ → Set

postulate C₂
  : Id ((λ X Y → (x : X) → Y x → Set) : (X : Set) → (X → Set) → Set) A₂ B₂
      C₀ C₁

postulate u₀ : Σ3 A₀ B₀ C₀

echo refl Σ3 A₂ B₂ C₂ trr u₀

echo refl Σ3 A₂ B₂ C₂ trr u₀ fst

echo refl Σ3 A₂ B₂ C₂ trr u₀ snd

echo refl Σ3 A₂ B₂ C₂ trr u₀ thd

echo refl Σ3 A₂ B₂ C₂ liftr u₀

echo refl Σ3 A₂ B₂ C₂ liftr u₀ fst

echo refl Σ3 A₂ B₂ C₂ liftr u₀ snd

echo refl Σ3 A₂ B₂ C₂ liftr u₀ thd
