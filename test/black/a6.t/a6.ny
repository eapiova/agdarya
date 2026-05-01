data ℕ : Set where
  zero : ℕ
  suc : ℕ → ℕ

twice : ℕ → ℕ
twice n = go n where
  go zero = zero
  go (suc m) = suc (suc (go m))

parityWitness : ℕ → ℕ
parityWitness n = even n where
  even zero = zero
  even (suc m) = odd m
  odd zero = suc zero
  odd (suc m) = even m

Stream : Set → Set
Stream A = codata [ head _ : A | tail _ : Stream A ]

zerosLocal : Stream ℕ
zerosLocal = s where
  s : Stream ℕ
  head s = zero
  tail s = s

postulate
  A : Set
  B : Set
  M : Set → Set
  _>>=_ : M A → (A → M B) → M B
  ma : M A
  mb : M B
  n : M A

useDo1 : M B
useDo1 =
  do
    x ← ma
    _ ← n
    mb

useDo2 : M B
useDo2 =
  do
    x ← ma
    y ← n
    mb

echo (twice (suc (suc zero)) : ℕ)
echo (parityWitness zero : ℕ)
echo (zerosLocal tail head : ℕ)
echo (useDo1 : M B)
echo (useDo2 : M B)
