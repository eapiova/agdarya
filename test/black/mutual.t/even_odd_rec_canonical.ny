-- A version that defines families of canonical types by "recursion".
ℕ : Set
ℕ = data [ zero | suc (_ : ℕ) ]

even_odd_type : Set
even_odd_type = sig (
  even : ℕ → Set,
  odd : ℕ → Set,
)

even_odd : even_odd_type
even_odd = (
  even ≔ λ {
  zero → sig ();
  suc n → sig (even_suc : even_odd odd n)
  },
  odd ≔ λ {
  zero → data [];
  suc n → sig (odd_suc : even_odd even n)
  },
)

echo even_odd even 8

echo even_odd odd 8
