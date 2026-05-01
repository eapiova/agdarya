  $ cat >nat.ny <<EOF
  > data Nat : Set where { zero : Nat; suc : Nat → Nat }
  > myzero : Nat
  > myzero = zero
  > myone : Nat
  > myone = suc zero
  > nums.two : Nat
  > nums.two = suc (suc zero)
  > nums.three : Nat
  > nums.three = suc (suc (suc zero))
  > plus : (x y : Nat) → Nat
  > plus x y = case y of λ { zero → x; suc y → suc (plus x y) }
  > notation(5) x "+" y := plus x y
  > EOF

Renaming imported names

  $ agdarya -e 'open import nat renaming (myone to yourone)' -e 'echo yourone'
  1
    : Nat
  

Using a subset of imported names

  $ agdarya -e 'open import nat using (myzero; nums.two)' -e 'echo myzero' -e 'echo nums.two'
  0
    : _OUT_OF_SCOPE.Nat
  
  2
    : _OUT_OF_SCOPE.Nat
  

Hiding a subtree

  $ agdarya -e 'open import nat hiding (nums)' -e 'echo myone' -e 'echo nums.two'
  1
    : Nat
  
   ￫ error[E0300]
   ￭ command-line exec string
   1 | echo nums.two
     ^ unbound variable: nums.two
  
  [1]

We can import only the notation subtree

  $ agdarya -e 'open import nat using (notations)' -e 'echo 1 + 1'
  2
    : _OUT_OF_SCOPE.Nat
  

Or hide the notation subtree and keep the ordinary names

  $ agdarya -e 'open import nat hiding (notations)' -e 'echo myzero' -e 'echo 1 + 1'
  0
    : Nat
  
   ￫ error[E0200]
   ￭ command-line exec string
   1 | echo 1 + 1
     ^ parse error
  
  [1]

Using and renaming also work on already visible modules

  $ agdarya -e 'module A where { postulate B : Set; postulate C : Set }' -e 'open A using (B)' -e 'echo B' -e 'echo C'
  A.B
    : Set
  
   ￫ error[E0300]
   ￭ command-line exec string
   1 | echo C
     ^ unbound variable: C
  
  [1]

  $ agdarya -e 'module A where { postulate B : Set; postulate C : Set }' -e 'open A renaming (B to D)' -e 'echo D'
  A.B
    : Set
  

`public` re-exports opened module contents

  $ cat >reexp.ny <<EOF
  > module A where { postulate B : Set }
  > open A public
  > echo B
  > EOF

  $ agdarya reexp.ny -e 'echo B' -e 'echo A.B'
  A.B
    : Set
  
  A.B
    : Set
  
  A.B
    : Set
  
