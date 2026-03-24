

Stream : Set → Set

Stream A = codata [ head _ : A | tail _ : Stream A ]

postulate A : Set

postulate s : Stream A

s0 : A

s0 = s head

s0t : Stream A

s0t = s tail

s1 : A

s1 = s tail head

s2 : A

s2 = s tail tail head

s' : Stream A

s' = record { head = s head; tail = s tail }

s_is_s' : Id (Stream A) s s'

s_is_s' = record { head = refl (s head); tail = refl (s tail) }

corec : (A X : Set) → (X → A) → (X → X) → X → Stream A

corec A X h t x = record { head = h x; tail = corec A X h t (t x) }

s'' : Stream A

s'' = corec A (Stream A) (x ↦ x head) (x ↦ x tail) s

∞eta : Stream A → Stream A

∞eta s = record { head = s head; tail = ∞eta (s tail) }

∞eta_bisim : (s : Stream A) → Id (Stream A) s (∞eta s)

∞eta_bisim s = record { head = refl (s head); tail = ∞eta_bisim (s tail) }

ℕ : Set

ℕ = data [ zero | suc (_ : ℕ) ]

nats : Stream ℕ

nats = corec ℕ ℕ (x ↦ x) (x ↦ suc x) 0

nats0_eq_0 : Id ℕ (nats head) 0

nats0_eq_0 = refl (0 : ℕ)

nats1_eq_1 : Id ℕ (nats tail head) 1

nats1_eq_1 = refl (1 : ℕ)

nats2_eq_2 : Id ℕ (nats tail tail head) 2

nats2_eq_2 = refl (2 : ℕ)

nats3_eq_3 : Id ℕ (nats tail tail tail head) 3

nats3_eq_3 = refl (3 : ℕ)

plus : ℕ → ℕ → ℕ

plus m n = case n of λ { zero → m; suc n → suc (plus m n)}

prod : Set → Set → Set

prod A B = sig ( fst : A, snd : B )

fib : Stream ℕ

fib
=
  corec ℕ (prod ℕ ℕ) (x ↦ x fst)
    (x ↦ (fst ≔ x snd, snd ≔ plus (x fst) (x snd))) (fst ≔ 1, snd ≔ 1)

fib0_eq_1 : Id ℕ (fib head) 1

fib0_eq_1 = refl (1 : ℕ)

fib1_eq_1 : Id ℕ (fib tail head) 1

fib1_eq_1 = refl (1 : ℕ)

fib2_eq_2 : Id ℕ (fib tail tail head) 2

fib2_eq_2 = refl (2 : ℕ)

fib3_eq_3 : Id ℕ (fib tail tail tail head) 3

fib3_eq_3 = refl (3 : ℕ)

fib4_eq_5 : Id ℕ (fib tail tail tail tail head) 5

fib4_eq_5 = refl (5 : ℕ)

fib5_eq_8 : Id ℕ (fib tail tail tail tail tail head) 8

fib5_eq_8 = refl (8 : ℕ)
