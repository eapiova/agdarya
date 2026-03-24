Σ : (A : Set) → (B : A → Set) → Set
Σ A B = sig ( fst : A, snd : B fst )

pair : (A : Set) → (B : A → Set) → (a : A) → (b : B a) → Σ A B
pair A B a b = (a, b)

postulate A : Set
postulate B : A → Set
{-Pairs and tuples have the correct type and are equal to each other-}
postulate a : A
postulate b : B a
ab : Σ A B
ab = (a, b)
ab' : Σ A B
ab' = pair A B a b
ab_equals_ab' : Id (Σ A B) ab ab'
ab_equals_ab' = refl ab
{-Projections have the correct type -}
postulate x : Σ A B
x1 : A
x1 = x fst
x2 : B x1
x2 = x snd

{-Projections of pairs and tuples compute-}
ab_fst_equals_a : Id A (ab fst) a
ab_fst_equals_a = refl a
ab_snd_equals_b : Id (B a) (ab snd) b
ab_snd_equals_b = refl b
ab'_fst_equals_a : Id A (ab' fst) a
ab'_fst_equals_a = refl a
ab'_snd_equals_b : Id (B a) (ab' snd) b
ab'_snd_equals_b = refl b

{-Projections satisfy eta-conversion for both pairs and tuples-}
x' : Σ A B
x' = pair A B (x fst) (x snd)
x_equals_x' : Id (Σ A B) x x'
x_equals_x' = refl x
x'' : Σ A B
x'' = (x fst, x snd)
x_equals_x'' : Id (Σ A B) x x''
x_equals_x'' = refl x

{-Identifications can be paired to give an identification of pairs-}
postulate a0 : A
postulate b0 : B a0
postulate a1 : A
postulate b1 : B a1
postulate a2 : Id A a0 a1
postulate b2 : Id B a2 b0 b1
ab2 : Id (Σ A B) (a0, b0) (a1, b1)
ab2 = (a2, b2)

{-As for function-types, identity types of sigma-types are invariant under eta-conversion-}
invariance1 : Id Set (Id (Σ A B) (a0, b0) (a1, b1))
      (Id (Σ A B) (pair A B a0 b0) (a1, b1))
invariance1 = refl (Id (Σ A B) (a0, b0) (a1, b1))

invariance2 : Id (Id (Σ A B) (a0, b0) (a1, b1)) (a2, b2)
      (refl pair (refl A) (refl B) a2 b2)
invariance2 = refl (refl pair (refl A) (refl B) a2 b2)

{-And can be projected back out again to the inputs-}
ab2_fst_equals_a2 : Id (Id A a0 a1) (ab2 fst) a2
ab2_fst_equals_a2 = refl a2
ab2_snd_equals_b2 : Id (Id B a2 b0 b1) (ab2 snd) b2
ab2_snd_equals_b2 = refl b2

{-Refl commutes with pairing-}
refl_comm1 : Id (Id (Σ A B) ab ab) (refl (pair A B a b)) (refl a, refl b)
refl_comm1 = refl (refl (pair A B a b))
refl_comm2 : Id (Id (Σ A B) ab ab) (refl ((a, b) : Σ A B)) (refl a, refl b)
refl_comm2 = refl (refl ((a, b) : Σ A B))

{-Sigmas can store identities and squares, and symmetry can act on them-}
postulate X : Set
postulate x00 : X
postulate x01 : X
postulate x02 : Id X x00 x01
postulate x10 : X
postulate x11 : X
postulate x12 : Id X x10 x11
postulate x20 : Id X x00 x10
postulate x21 : Id X x01 x11
postulate x22 : Id ((x y ↦ Id X x y) : X → X → Set) x02 x12 x20 x21
postulate Y : Set
postulate y : Y
postulate s : Σ (Id ((x y ↦ Id X x y) : X → X → Set) x02 x12 x20 x21) (_ ↦ Y)

s1s : Id ((x y ↦ Id X x y) : X → X → Set) x20 x21 x02 x12
s1s = sym (s fst)
