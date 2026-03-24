postulate A : Set
postulate x : A
postulate y : A
postulate z : A
postulate w : A

postulate p : Id A x y
postulate q : Id A y z
postulate r : Id A z w

xx : Id A x x
xx = calc
  x ∎

xy : Id A x y
xy = calc
  x
  = y
      by p ∎

xydef : Id (Id A x y) xy (A⁽ᵉᵉ⁾ (refl x) p trr (refl x))
xydef = refl xy

xyz : Id A x z
xyz = calc
  x
  = y
      by p
  = y
  = z
      by q ∎

xyzdef : Id (Id A x z) xyz
      (A⁽ᵉᵉ⁾ (refl x) q trr (A⁽ᵉᵉ⁾ (refl x) p trr (refl x)))
xyzdef = refl xyz

xyzw : Id A x w
xyzw = calc
  x
  = x
  = y
      by p
  = z
      by q
  = w
      by r
  = w ∎

xyzwdef : Id (Id A x w) xyzw
      (A⁽ᵉᵉ⁾ (refl x) r
       trr (A⁽ᵉᵉ⁾ (refl x) q trr (A⁽ᵉᵉ⁾ (refl x) p trr (refl x))))
xyzwdef = refl xyzw

postulate s : Id A z y

xz' : Id A x z
xz' = calc
  x
  = y
      by p
  = z
      by s ∎

xz'def : Id (Id A x z) xz'
      (A⁽ᵉᵉ⁾ (refl x) s trl (A⁽ᵉᵉ⁾ (refl x) p trr (refl x)))
xz'def = refl xz'

ℕ : Set
ℕ = data [ zero : ℕ | suc : ℕ → ℕ ]
plus : (m n : ℕ) → ℕ
plus m n = match m [ zero ↦ n | suc m' ↦ suc (plus m' n) ]

notation(0) … m "+" n ≔ plus m n

2plus3 : Id ℕ (2 + 3) 5
2plus3 = calc
  2 + 3
  = suc (1 + 3)
  = suc (suc (0 + 3))
  = suc (suc 3)
  = 5 ∎

ℕ.plus_assoc : (m n p : ℕ) → Id ℕ ((m + n) + p) (m + (n + p))
ℕ.plus_assoc m n p = match m [
| zero ↦ calc
    (zero + n) + p
    = n + p
    = zero + (n + p) ∎
| suc m ↦ calc
    (suc m + n) + p
    = suc (m + n) + p
    = suc ((m + n) + p)
    = suc (m + (n + p))
        by suc (ℕ.plus_assoc m n p)
    = suc m + (n + p) ∎]
