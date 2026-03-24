

data ℕ : Set where { zero : ℕ ; suc : ℕ → ℕ }

data ℕ₊ : Set where { one : ℕ₊ ; suc : ℕ₊ → ℕ₊ }

data ℚ₀₊ : Set where { zero : ℚ₀₊ ; suc : ℕ → ℚ₀₊ ; quot : ℕ → ℕ₊ → ℚ₀₊ }

notation(0) x "/" y ≔ quot x y

section ℕ ≔

  zero : ℕ

  zero = 0

  one : ℕ

  one = 1

  echo one

  one' : ℕ

  one' = 1.0

  echo one'

  two : ℕ

  two = 2

end

section ℕ₊ ≔

  one : ℕ₊

  one = 1

  echo one

  two : ℕ₊

  two = 2

  echo two

end

section ℚ ≔

  zero : ℚ₀₊

  zero = 0

  one : ℚ₀₊

  one = 1

  two : ℚ₀₊

  two = 2.0

  echo two

  half : ℚ₀₊

  half = 0.5

  echo half

  quart : ℚ₀₊

  quart = 0.25

  echo quart

  half' : ℚ₀₊

  half' = 1 / 2

  echo half'

  third : ℚ₀₊

  third = 1 / 3

  echo third

end
