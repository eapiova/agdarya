 -- We can define even and odd predicates by mutual recursion.  We start with the natural numbers and the decidable propositions.

ℕ : Set

ℕ = data [ zero | suc (_ : ℕ) ]

⊤ : Set

⊤ = sig ()

⊥ : Set

⊥ = data [] -- The pair of "even" and "odd" will together inhabit this record type.

even_odd_type : Set

even_odd_type = sig ( even : ℕ → Set, odd : ℕ → Set ) -- Now we can define them together, by mutual recursion

even_odd : even_odd_type

even_odd
=
  (
  even ≔ λ { zero → ⊤; suc n → even_odd odd n },
  odd ≔ λ { zero → ⊥; suc n → even_odd even n })

echo even_odd even 8

echo even_odd odd 8
