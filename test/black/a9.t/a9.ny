

data ℕ : Set  where
  zero : ℕ


  suc : ℕ → ℕ





one : ℕ

one = suc zero

two : ℕ

two = suc one

pred : ℕ → ℕ

pred n with n
  … | zero = zero
  … | suc m = m

predPred : ℕ → ℕ

predPred n with n
  … | zero = zero
  … | suc m with m
    … | zero = zero
    … | suc k = k

sameNat : ℕ → ℕ → ℕ

sameNat m n with m | n
  … | zero | zero = zero
  … | zero | suc k = one
  … | suc k | zero = one
  … | suc k | suc l = zero

plus : ℕ → ℕ → ℕ

plus zero m = m

plus (suc n) m = suc (plus n m)

postulate
  plusZeroR : (n : ℕ) → Id ℕ n (plus n zero)


fromPlusZero : (n : ℕ) → Id ℕ (plus n zero) n

fromPlusZero n rewrite plusZeroR n = refl n

fromPlusZero2 : (n : ℕ) → Id ℕ (plus n zero) n

fromPlusZero2 n rewrite plusZeroR n | refl n = refl n

fromPlusZeroWith : (n : ℕ) → Id ℕ (plus n zero) n

fromPlusZeroWith n with n
  … | zero rewrite plusZeroR zero = refl zero
  … | suc m rewrite plusZeroR (suc m) = refl (suc m)

echo (pred two : ℕ)

echo (predPred two : ℕ)

echo (sameNat two two : ℕ)

echo (sameNat zero two : ℕ)

echo (fromPlusZero two : Id ℕ (plus two zero) two)

echo (fromPlusZero2 two : Id ℕ (plus two zero) two)

echo (fromPlusZeroWith two : Id ℕ (plus two zero) two)
