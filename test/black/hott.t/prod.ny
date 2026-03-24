{- Transport and lifting compute on product types -}

prod : (A : Set) → (B : Set) → Set
prod A B = sig ( fst : A, snd : B )

postulate A₀ : Set
postulate A₁ : Set
postulate A₂ : Id Set A₀ A₁
postulate B₀ : Set
postulate B₁ : Set
postulate B₂ : Id Set B₀ B₁

postulate u₀ : prod A₀ B₀

echo refl prod A₂ B₂ trr u₀
echo refl prod A₂ B₂ trr u₀ fst
echo refl prod A₂ B₂ trr u₀ snd

echo refl prod A₂ B₂ liftr u₀
echo refl prod A₂ B₂ liftr u₀ fst
echo refl prod A₂ B₂ liftr u₀ snd
