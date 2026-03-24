-- We can define even and odd predicates by mutual *induction*.  We start with the natural numbers.
ℕ : Set
ℕ = data [ zero | suc (_ : ℕ) ]

-- The pair of "even" and "odd" will together inhabit this record type.
even_odd_type : Set
even_odd_type = sig ( even : ℕ → Set, odd : ℕ → Set )

-- Now we can define them together, by mutual induction.
even_odd : even_odd_type
even_odd = (
  even ≔ data [
  | even_zero : even_odd even zero
  | even_suc : (n : ℕ) → even_odd odd n → even_odd even (suc n) ],
  odd ≔ data [
  | odd_suc : (n : ℕ) → even_odd even n → even_odd odd (suc n) ])

-- Then we pick out the two components and give them separate names.

even = even_odd even

odd = even_odd odd

-- As a test, we prove that every natural number is either even or odd.  First we define "or".

sum : (A B : Set) → Set
sum A B = data [ inl (a : A) | inr (b : B) ]

-- Now we need a helper lemma, since we can't pattern-match on an intermediate value inside a definition.
even_or_odd_suc : (n : ℕ) → sum (even n) (odd n) → sum (even (suc n)) (odd (suc n))
even_or_odd_suc n = λ { inl e → inr (odd_suc n e); inr o → inl (even_suc n o) }

-- Finally we can prove the theorem.
all_even_or_odd : (n : ℕ) → sum (even n) (odd n)
all_even_or_odd n = match n [
| zero ↦ inl even_zero
| suc n ↦ even_or_odd_suc n (all_even_or_odd n)]
