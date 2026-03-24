ℕ : Set
ℕ = data [ zero | suc (_ : ℕ) ]

ℕ.plus : (a b : ℕ) → ℕ
ℕ.plus a b = match b [ zero ↦ a | suc b ↦ suc (ℕ.plus a b) ]

ℤ : Set
ℤ = data [ zero | suc (_ : ℕ) | negsuc (_ : ℕ) ]

zero : ℤ
zero = ℤ.zero

one : ℤ
one = ℤ.suc ℕ.zero

two : ℤ
two = ℤ.suc (ℕ.suc ℕ.zero)

three : ℤ
three = ℤ.suc (ℕ.suc (ℕ.suc ℕ.zero))

minus_one : ℤ
minus_one = ℤ.negsuc ℕ.zero

minus_two : ℤ
minus_two = ℤ.negsuc (ℕ.suc ℕ.zero)

minus_three : ℤ
minus_three = ℤ.negsuc (ℕ.suc (ℕ.suc ℕ.zero))

ℤ.minus : ℤ → ℤ
ℤ.minus = λ { zero → zero; suc n → negsuc n; negsuc n → suc n }

ℕ.sub : (a b : ℕ) → ℤ
ℕ.sub a b = match a, b [
| ℕ.zero, ℕ.zero ↦ ℤ.zero
| ℕ.suc a, ℕ.zero ↦ ℤ.suc a
| ℕ.zero, ℕ.suc b ↦ ℤ.negsuc b
| ℕ.suc a, ℕ.suc b ↦ ℕ.sub a b]

ℤ.sub : (a b : ℤ) → ℤ
ℤ.sub a b = match b [
| zero ↦ a
| suc b ↦ match a [
  | zero ↦ negsuc b
  | suc a ↦ ℕ.sub a b
  | negsuc a ↦ negsuc (suc (ℕ.plus a b))]
| negsuc b ↦ match a [
  | zero ↦ suc b
  | suc a ↦ suc (suc (ℕ.plus a b))
  | negsuc a ↦ ℕ.sub b a]]

echo ℤ.sub three one

echo ℤ.sub one three

echo ℤ.sub two zero

echo ℤ.sub zero two

echo ℤ.sub minus_three minus_one

echo ℤ.sub minus_one minus_three

echo ℤ.sub minus_two zero

echo ℤ.sub zero minus_two

echo ℤ.sub two minus_two

echo ℤ.sub minus_two two

echo ℤ.sub two two

echo ℤ.sub minus_two minus_two
