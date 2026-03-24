 {- This version of even_odd_sig uses mutual-induction syntax. -}

data ℕ : Set where { zero : ℕ ; suc : ℕ → ℕ }

even : ℕ → Set

even
=
  data [
| even_zero : even zero
| even_suc : (n : ℕ) → odd n → even (suc n) ]

odd : ℕ → Set

odd = data [ odd_suc : (n : ℕ) → even n → odd (suc n) ]

data sum (A B : Set) : Set where { inl : A → sum A B ; inr : B → sum A B }

even_or_odd_suc : (n : ℕ) → sum (even n) (odd n)
                  → sum (even (suc n)) (odd (suc n))

even_or_odd_suc n
=
  λ { inl e → inr (odd_suc n e); inr o → inl (even_suc n o) }

all_even_or_odd : (n : ℕ) → sum (even n) (odd n)

all_even_or_odd n
=
  case n of λ {
zero → inl even_zero;
suc n → even_or_odd_suc n (all_even_or_odd n)}
