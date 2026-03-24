{- Transport and lifting compute on Σ-types -}

Σ : (A : Set) → (B : A → Set) → Set
Σ A B = sig ( fst : A, snd : B fst )

postulate A₀ : Set
postulate A₁ : Set
postulate A₂ : Id Set A₀ A₁
postulate B₀ : A₀ → Set
postulate B₁ : A₁ → Set
postulate B₂ : Id ((X ↦ X → Set) : Set → Set) A₂ B₀ B₁

postulate u₀ : Σ A₀ B₀

echo refl Σ A₂ B₂ trr u₀
echo refl Σ A₂ B₂ trr u₀ fst
echo A₂ trr⟨1⟩ (u₀ fst)

Σtrrfst : Id A₁ (refl Σ A₂ B₂ trr u₀ fst) (A₂ trr⟨1⟩ (u₀ fst))
Σtrrfst = refl _

echo refl Σ A₂ B₂ trr u₀ snd
echo B₂ (A₂ liftr⟨1⟩ (u₀ fst)) trr⟨1⟩ (u₀ snd)

Σtrrsnd : Id (B₁ (A₂ trr⟨1⟩ (u₀ fst))) (refl Σ A₂ B₂ trr u₀ snd)
      (B₂ (A₂ liftr⟨1⟩ (u₀ fst)) trr⟨1⟩ (u₀ snd))
Σtrrsnd = refl _

Σtrr : Id (Σ A₁ B₁) (refl Σ A₂ B₂ trr u₀)
      (A₂ trr⟨1⟩ (u₀ fst), B₂ (A₂ liftr⟨1⟩ (u₀ fst)) trr⟨1⟩ (u₀ snd))
Σtrr = refl _

echo refl Σ A₂ B₂ liftr u₀
echo refl Σ A₂ B₂ liftr u₀ fst
echo A₂ liftr⟨1⟩ (u₀ fst)
echo refl Σ A₂ B₂ liftr u₀ snd

echo B₂ (A₂ liftr⟨1⟩ (u₀ fst)) liftr⟨1⟩ (u₀ snd)

Σliftr : Id (refl Σ A₂ B₂ u₀ (refl Σ A₂ B₂ trr⟨1⟩ u₀)) (refl Σ A₂ B₂ liftr u₀)
      (A₂ liftr⟨1⟩ (u₀ fst),
       B₂ (A₂ liftr⟨1⟩ (u₀ fst)) liftr⟨1⟩ (u₀ snd))
Σliftr = refl _

postulate u₁ : Σ A₁ B₁

echo refl Σ A₂ B₂ trl u₁
echo refl Σ A₂ B₂ trl u₁ fst
echo refl Σ A₂ B₂ trl u₁ snd

Σtrl : Id (Σ A₀ B₀) (refl Σ A₂ B₂ trl u₁)
      (A₂ trl⟨1⟩ (u₁ fst), B₂ (A₂ liftl⟨1⟩ (u₁ fst)) trl⟨1⟩ (u₁ snd))
Σtrl = refl _

echo refl Σ A₂ B₂ liftl u₁
echo refl Σ A₂ B₂ liftl u₁ fst
echo refl Σ A₂ B₂ liftl u₁ snd

Σliftl : Id (refl Σ A₂ B₂ (refl Σ A₂ B₂ trl⟨1⟩ u₁) u₁) (refl Σ A₂ B₂ liftl u₁)
      (A₂ liftl⟨1⟩ (u₁ fst),
       B₂ (A₂ liftl⟨1⟩ (u₁ fst)) liftl⟨1⟩ (u₁ snd))
Σliftl = refl _
