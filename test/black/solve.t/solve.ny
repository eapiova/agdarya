data ℕ : Set where { zero : ℕ; suc : ℕ → ℕ }

Nat : Set
Nat = ?

solve 0 ≔ ℕ

plus : (x y : ℕ) → ℕ
plus x y = ?

solve 1 ≔ match y [ zero ↦ ? | suc z ↦ ? ]

solve 2 ≔ x

solve 3 ≔ suc (plus x z)

echo plus 4 5

{- holes can refer to global metas and depend on the value of previously filled holes -}

Σ : (A : Set) → (B : A → Set) → Set
Σ A B = sig ( fst : A, snd : B fst )

data 𝔹 : Set where { false : 𝔹; true : 𝔹 }

data Jd (A : Set) (a : A) : A → Set where { rfl : Jd A a a }

invol1 : Σ (𝔹 → 𝔹) (f ↦ (x : 𝔹) → Jd 𝔹 x (f (f x)))
invol1 = let not : 𝔹 → 𝔹 = λ { false → true; true → false } in
  (?, ?)

solve 4 ≔ not

solve 5 ≔ λ { true → rfl; false → rfl }

{- holes can create global metas -}

invol2 : Σ (𝔹 → 𝔹) (f ↦ (x : 𝔹) → Jd 𝔹 x (f (f x)))
invol2 = ?

solve 6 ≔ let not : 𝔹 → 𝔹 = λ { false → true; true → false } in (not, ?)

solve 7 ≔ λ { true → rfl; false → rfl }
