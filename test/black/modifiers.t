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
  > plus x y = match y [ zero ↦ x | suc y ↦ suc (plus x y) ]
  > times : (x y : Nat) → Nat
  > times x y = match y [ zero ↦ zero | suc y ↦ plus (times x y) x ]
  > minus : (x y : Nat) → Nat
  > minus x y = match y, x [ zero, x ↦ x | suc y, suc x ↦ minus x y | suc _, zero ↦ y ]
  > notation(5) x "+" y ≔ plus x y
  > notation(6) x "*" y ≔ times x y
  > notation(5) x "-" y ≔ minus x y
  > EOF

Renaming individual imports

  $ agdarya -e 'import "nat" | renaming myone yourone echo yourone'
  1
    : Nat
  

Renaming a whole subtree, clobbering the rest

  $ agdarya -e 'import "nat" | renaming nums . echo two'
  2
    : _OUT_OF_SCOPE.Nat
  
Renaming a subtree while preserving the rest

  $ agdarya -e 'import "nat" | union (id, renaming nums .) echo two'
  2
    : Nat
  
Excluding a subtree

  $ agdarya -e 'import "nat" | except nums echo myone echo two'
  1
    : Nat
  
   ￫ error[E0300]
   ￭ command-line exec string
   1 | import "nat" | except nums echo myone echo two
     ^ unbound variable: two
  
  [1]

Renaming everything (i.e. import qualified)

  $ agdarya -e 'import "nat" | renaming . nat echo nat.myzero echo nat.nums.three'
  0
    : nat.Nat
  
  3
    : nat.Nat
  
We get notations if we keep the main subtree

  $ agdarya -e 'import "nat" | renaming myone yourone echo 1 + 1'
  2
    : Nat
  
We can get only the notations by keeping only that subtree

  $ agdarya -e 'import "nat" | only notations echo 1 + 1'
  2
    : _OUT_OF_SCOPE.Nat
  

Or exclude the notations but get everything else

  $ agdarya -e 'import "nat" | except notations echo myzero echo 1 + 1'
  0
    : Nat
  
   ￫ error[E0400]
   ￮ non-synthesizing term in synthesizing position (argument of echo)
  
  [1]

Or import some of the notations but not others

  $ agdarya -e 'import "nat" | in notations union (only «_ + _», only «_ * _») echo 1+1 echo 1*1 echo (1-1 : Nat)'
  2
    : Nat
  
  1
    : Nat
  
   ￫ error[E0200]
   ￭ command-line exec string
   1 | import "nat" | in notations union (only «_ + _», only «_ * _») echo 1+1 echo 1*1 echo (1-1 : Nat)
     ^ parse error
  
  [1]

We can also import from a namespace rather than a file.

  $ agdarya -e 'postulate a.b : Set postulate a.c : Set import a echo b'
  a.b
    : Set
  

  $ agdarya -e 'postulate a.b : Set postulate a.c : Set import a | renaming b d echo d'
  a.b
    : Set
  

But this doesn't affect the export namespace:

  $ cat >importns.ny <<EOF
  > postulate a.b : Set
  > postulate a.c : Set
  > import a
  > echo b
  > EOF

  $ agdarya importns.ny -e 'echo a.b echo b'
  a.b
    : Set
  
  a.b
    : Set
  
   ￫ error[E0300]
   ￭ command-line exec string
   1 | echo a.b echo b
     ^ unbound variable: b
  
  [1]

Unless we tell it to:

  $ cat >exportns.ny <<EOF
  > postulate a.b : Set
  > postulate a.c : Set
  > export a
  > echo b
  > EOF

  $ agdarya exportns.ny -e 'echo a.b echo b'
  a.b
    : Set
  
  a.b
    : Set
  
  a.b
    : Set
  
