

isFibrant : Set → Set

isFibrant A
=
  codata [
| trr⟨e⟩ x : A.0 → A.1
| liftr⟨e⟩ x : (x₀ : A.0) → A.2 x₀ (x.2 trr x₀)
| trl⟨e⟩ x : A.1 → A.0
| liftl⟨e⟩ x : (x₁ : A.1) → A.2 (x.2 trl x₁) x₁
| id⟨e⟩ x : (x₀ : A.0) (x₁ : A.1) → isFibrant (A.2 x₀ x₁) ]
