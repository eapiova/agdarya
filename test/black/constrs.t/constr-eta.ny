ℕ : Set
ℕ = data [ zero | suc (_ : ℕ) ]

suc : ℕ → ℕ
suc = ℕ.suc

echo suc (ℕ.suc (ℕ.suc 0))

kinetic_suc : ℕ → ℕ
kinetic_suc = ((x : ℕ → ℕ) ↦ x : ℕ → ℕ) suc

{- TODO: Get a generic variable name for this. -}
echo kinetic_suc

refl_suc : {n₀ n₁ : ℕ} (n₂ : Id ℕ n₀ n₁) →⁽ᵉ⁾ Id ℕ (suc n₀) (suc n₁)
refl_suc = ℕ.suc

Vec : (A : Set) → ℕ → Set
Vec A = data [
| nil : Vec A 0
| cons (n : ℕ) (x : A) (xs : Vec A n) : Vec A (suc n) ]

cons3 : (A : Set) → (n : ℕ) (x : A) (xs : Vec A n) → Vec A (suc n)
cons3 A = Vec.cons

cons2 : (A : Set) → (n : ℕ) → (x : A) (xs : Vec A n) → Vec A (suc n)
cons2 A n = Vec.cons n

cons1 : (A : Set) → (n : ℕ) → (x : A) → (xs : Vec A n) → Vec A (suc n)
cons1 A n x = Vec.cons n x

postulate A : Set

postulate a : A

echo cons3 A 2 a (cons2 A 1 a (cons1 A 0 a nil))
