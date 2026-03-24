{- Transport and liftnig compute in 2-dimensional Σ-types -}

postulate A00 : Set

postulate A01 : Set

postulate A02 : Id Set A00 A01

postulate A10 : Set

postulate A11 : Set

postulate A12 : Id Set A10 A11

postulate A20 : Id Set A00 A10

postulate A21 : Id Set A01 A11

postulate A22 : Set⁽ᵉᵉ⁾ A02 A12 A20 A21

postulate B00 : A00 → Set

postulate B01 : A01 → Set

postulate B02 : Id ((X ↦ X → Set) : Set → Set) (A02) B00 B01

postulate B10 : A10 → Set

postulate B11 : A11 → Set

postulate B12 : Id ((X ↦ X → Set) : Set → Set) (A12) B10 B11

postulate B20 : Id ((X ↦ X → Set) : Set → Set) (A20) B00 B10

postulate B21 : Id ((X ↦ X → Set) : Set → Set) (A21) B01 B11

postulate B22 : ((X ↦ X → Set) : Set → Set)⁽ᵉᵉ⁾ (A22) B02 B12 B20 B21

Σ : (A : Set) → (B : A → Set) → Set
Σ A B = sig ( fst : A, snd : B fst )

postulate u00 : Σ A00 B00

postulate u01 : Σ A01 B01

postulate u02 : Id Σ A02 B02 u00 u01

postulate u10 : Σ A10 B10

postulate u11 : Σ A11 B11

postulate u12 : Id Σ A12 B12 u10 u11

postulate u20 : Id Σ A20 B20 u00 u10

postulate u21 : Id Σ A21 B21 u01 u11

{- Uniform operations -}
echo Σ⁽ᵉᵉ⁾ A22 B22 trr⟨1⟩ u02 fst

echo Σ⁽ᵉᵉ⁾ A22 B22 trr⟨2⟩ u20 fst

{- Non-uniform operations, box-filling -}
synth Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 trr u20

echo Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 trr u20 fst

echo Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 trr u20 snd

Σtrr : Id (refl Σ A21 B21 u01 u11) (Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 trr u20)
      (A22 (u02 fst) (u12 fst) trr⟨1⟩ (u20 fst),
       B22 (A22 (u02 fst) (u12 fst) liftr⟨1⟩ (u20 fst)) (u02 snd)
           (u12 snd)
         trr⟨1⟩ (u20 snd))
Σtrr = refl _

synth Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 liftr u20

echo Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 liftr u20 fst

echo Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 liftr u20 snd

Σliftr : Id (Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 u20 (Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 trr⟨1⟩ u20))
      (Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 liftr u20)
      (A22 (u02 fst) (u12 fst) liftr⟨1⟩ (u20 fst),
       B22 (A22 (u02 fst) (u12 fst) liftr⟨1⟩ (u20 fst)) (u02 snd)
           (u12 snd)
         liftr⟨1⟩ (u20 snd))
Σliftr = refl _

synth Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 trl u21

echo Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 trl u21 fst

echo Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 trl u21 snd

Σtrl : Id (refl Σ A20 B20 u00 u10) (Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 trl u21)
      (A22 (u02 fst) (u12 fst) trl⟨1⟩ (u21 fst),
       B22 (A22 (u02 fst) (u12 fst) liftl⟨1⟩ (u21 fst)) (u02 snd)
           (u12 snd)
         trl⟨1⟩ (u21 snd))
Σtrl = refl _

synth Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 liftl u21

echo Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 liftl u21 fst

echo Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 liftl u21 snd

Σliftl : Id (Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 (Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 trl⟨1⟩ u21) u21)
      (Σ⁽ᵉᵉ⁾ A22 B22 u02 u12 liftl u21)
      (A22 (u02 fst) (u12 fst) liftl⟨1⟩ (u21 fst),
       B22 (A22 (u02 fst) (u12 fst) liftl⟨1⟩ (u21 fst)) (u02 snd)
           (u12 snd)
         liftl⟨1⟩ (u21 snd))
Σliftl = refl _
