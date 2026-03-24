{- Transport and lifting compute on M-types -}

M : (A : Set) → (B : A → Set) → Set
M A B = codata [
| recv x : A
| send x : B (x recv) → M A B ]

postulate A₀ : Set
postulate A₁ : Set
postulate A₂ : Id Set A₀ A₁
postulate B₀ : A₀ → Set
postulate B₁ : A₁ → Set
postulate B₂ : Id ((X ↦ X → Set) : Set → Set) A₂ B₀ B₁

postulate u₀ : M A₀ B₀

echo refl M A₂ B₂ trr u₀
echo refl M A₂ B₂ trr u₀ recv
postulate b₁ : B₁ (A₂ trr (u₀ recv))
echo refl M A₂ B₂ trr u₀ send b₁

echo refl M A₂ B₂ liftr u₀
echo refl M A₂ B₂ liftr u₀ recv
postulate b₀ : B₀ (u₀ recv)
postulate b₂ : B₂ (A₂ liftr (u₀ recv)) b₀ b₁
echo refl M A₂ B₂ liftr u₀ send b₂

synth M⁽ᵉᵉ⁾ A₂⁽¹ᵉ⁾ B₂⁽¹ᵉ⁾
          (refl u₀
           send
             (B₂⁽ᵉ¹⁾ (sym (refl A₂ liftr⟨1⟩ (refl u₀ recv))) b₂
                  (B₂ (A₂ liftr⟨1⟩ (u₀ recv)) liftl⟨1⟩ b₁)
              trl⟨1⟩ (refl b₁)))
          (M⁽ᵉᵉ⁾ A₂⁽¹ᵉ⁾ B₂⁽¹ᵉ⁾
           trr⟨1⟩
             (refl u₀
              send
                (B₂⁽¹ᵉ⁾ (refl A₂ liftr⟨1⟩ (refl u₀ recv)) trl⟨1⟩ (refl b₁))))
  trl⟨1⟩
    (refl M A₂ B₂
     liftr⟨1⟩ (u₀ send (B₂ (A₂ liftr⟨1⟩ (u₀ recv)) trl⟨1⟩ b₁)))
