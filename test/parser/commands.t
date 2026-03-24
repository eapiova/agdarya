Testing parsing of commands, on the command line:

  $ agdarya -e 'postulate A : Set'

  $ agdarya -e 'postulate A : Set postulate a : A'

  $ agdarya -e 'def A : Set := Set'
   ￫ error[E0216]
   ￮ def syntax removed; use a top-level signature followed by one or more clauses
  
  [1]

  $ agdarya -e 'postulate A : Set' -e 'postulate a : A'

  $ agdarya -e 'postulate A : Set' -e 'def B : Set := A'
   ￫ error[E0216]
   ￮ def syntax removed; use a top-level signature followed by one or more clauses
  
  [1]

  $ agdarya -e 'postulate A : Set' -e 'echo A'
  A
    : Set
  

  $ agdarya -e 'postulate A : Set' -e 'echo ((λ x → x) : A → A)'
  λ x → x
    : A → A
  
  $ agdarya -e 'data ℕ : Set where { zero : ℕ; suc : ℕ → ℕ }' -e 'echo (suc zero : ℕ)'
  1
    : ℕ
  
  $ agdarya -e 'data even : Set where { zero : even } and odd : Set where { suc : even → odd }' -e 'echo (suc zero : odd)'
  1
    : odd
  
  $ agdarya -e 'record Pair (A B : Set) : Set where { field fst : A; snd : B }' -e 'postulate A : Set' -e 'postulate B : Set' -e 'postulate p : Pair A B' -e 'echo (p fst : A)'
  p fst
    : A
  
  $ agdarya -e 'data ℕ : Set where { zero : ℕ; suc : ℕ → ℕ }' -e 'plus1 : ℕ → ℕ' -e 'plus1 n = case n of λ { zero → suc zero ; suc m → suc (suc m) }' -e 'echo (plus1 zero : ℕ)'
  1
    : ℕ
  
  $ agdarya -e 'record Bad : Set where { constructor _,_ }'
   ￫ error[E0215]
   ￮ record constructor clauses are not supported in A4; use field declarations only
  
  [1]

  $ agdarya -e 'postulate A : Set' -e 'echo (let id = ((λ x → x) : A → A) in id)'
  λ x → x
    : A → A
  

And in files:

  $ cat >test.ny <<EOF
  > postulate A:Set
  > postulate a:A
  > B : Set
  > B = A
  > echo B
  > EOF

Now we run it:

  $ agdarya test.ny
  A
    : Set
  

Can we parse empty things?

  $ agdarya -e ''

  $ cat >test.ny <<EOF
  > EOF
  $ agdarya test.ny
