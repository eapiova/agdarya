Testing binder notation commands

  $ agdarya -e 'postulate A : Set' -e 'postulate B : A → Set' -e 'postulate All : (X : Set) → (X → Set) → Set' -e 'postulate Exists : (X : Set) → (X → Set) → Set' -e 'notation(0) "∀" [x] ":" A "," B := All A B' -e 'notation(0) "∑" [x] ":" A "," B := Exists A B' -e 'echo (∀ x y : A, A)' -e 'echo (All A (x ↦ All (B x) (y ↦ A)))' -e 'echo (∑ x : A, A)'
  ∀ x y : A, A
    : Set
  
  ∀ x : A, y : B x, A
    : Set
  
  ∑ x : A, A
    : Set
  
  $ agdarya -e 'postulate A : Set' -e 'postulate All : (X : Set) → (X → Set) → Set' -e 'def(0) ("∀" [x] ":" X "," B) : (X : Set) → (X → Set) → Set := X B ↦ All X B' -e 'synth (∀ x : A, A)'
   ￫ error[E0216]
   ￮ def syntax removed; use a top-level signature followed by one or more clauses
  
  [1]
  $ agdarya -e 'postulate A : Set' -e 'postulate B : A → Set' -e 'postulate C : (x : A) → B x → Set' -e 'postulate Sigma2 : (X : Set) → (Y : X → Set) → ((x : X) → Y x → Set) → Set' -e 'notation(0) "Σ" [x] ":" X "," [y] ":" Y "," Z := Sigma2 X Y Z' -e 'echo (Σ x : A, y : B x, C x y)'
  Σ x : A, y : B x, C x y
    : Set
  
  $ agdarya -e 'postulate A : Set' -e 'postulate B : A → Set' -e 'postulate C : (x : A) → B x → Set' -e 'postulate Sigma2 : (X : Set) → (Y : X → Set) → ((x : X) → Y x → Set) → Set' -e 'def(0) ("Σ" [x] ":" X "," [y] ":" Y "," Z) : (X : Set) → (Y : X → Set) → ((x : X) → Y x → Set) → Set := X Y Z ↦ Sigma2 X Y Z' -e 'synth (Σ x : A, y : B x, C x y)'
   ￫ error[E0216]
   ￮ def syntax removed; use a top-level signature followed by one or more clauses
  
  [1]
  $ agdarya -e 'postulate A : Set' -e 'postulate B : A → Set' -e 'postulate D : A → A → Set' -e 'postulate E : (x : A) → (y : A) → D x y → Set' -e 'postulate F : (x : A) → B x → B x → Set' -e 'postulate Duo : Set → ((x : A) → (y : A) → Set) → ((x : A) → (y : A) → D x y → Set) → Set' -e 'postulate Later : Set → (A → Set) → ((x : A) → B x → B x → Set) → Set' -e 'notation(0) "Ξ" [x] ":" X "," [z] ":" Y "," Z := Duo X Y Z' -e 'notation(0) "Λ" [x] ":" X "," [y] ":" Y "," Z := Later X Y Z' -e 'echo (Ξ x y : A, z : D x y, E x y z)' -e 'echo (Λ x : A, y z : B x, F x y z)'
  Ξ x y : A, z : D x y, E x y z
    : Set
  
  Λ x : A, y z : B x, F x y z
    : Set
  
  $ agdarya -e 'postulate K : Set → Set' -e 'notation(0) "∀" [x] ":" A "," [y] := K A'
   ￫ error[E2202]
   ￮ invalid notation pattern: binder notations must be prefix patterns with one or more bracketed slots of the form "op" [x] ":" A "," ... B
  
  [1]

  $ agdarya -e 'postulate A : Set' -e 'postulate All : (X : Set) → (X → Set) → Set' -e 'notation(0) "∀" [x] ":" A "," B := All A x'
   ￫ error[E2206]
   ￮ unused notation variable: 'B'
  
  [1]

  $ agdarya -e 'postulate A : Set' -e 'postulate All : (X : Set) → (X → Set) → Set' -e 'notation(0) [x] "∀" ":" A "," B := All A B'
   ￫ error[E2202]
   ￮ invalid notation pattern: binder notations must be prefix patterns
  
  [1]

  $ agdarya -e 'postulate A : Set' -e 'postulate Bad : Set → Set → Set' -e 'notation(0) "Σ" [x] ":" A "," [y] "," Z := Bad A Z'
   ￫ error[E2202]
   ￮ invalid notation pattern: binder notations must be prefix patterns with one or more bracketed slots of the form "op" [x] ":" A "," ... B
  
  [1]

  $ agdarya -e 'postulate A : Set' -e 'postulate B : A → Set' -e 'postulate Pair : Set → (A → Set) → Set' -e 'notation(0) "Σ" [x] ":" A "," [y] ":" B := Pair A B'
   ￫ error[E2202]
   ￮ invalid notation pattern: binder notations must be prefix patterns with one or more bracketed slots of the form "op" [x] ":" A "," ... B
  
  [1]

  $ agdarya -e 'data Q : Set where { all : (X : Set) → (X → Set) → Q }' -e 'notation(0) "∀" [x] ":" A "," B := all A B'
   ￫ error[E2205]
   ￮ invalid notation head: all
  
  [1]

  $ agdarya -e 'postulate A : Set' -e 'postulate B : A → Set' -e 'postulate C : (x : A) → B x → Set' -e 'postulate Sigma2 : (X : Set) → (Y : X → Set) → ((x : X) → Y x → Set) → Set' -e 'notation(0) "Σ" [x] ":" X "," [y] ":" Y "," Z := Sigma2 X Y Z' -e 'bad : Set' -e 'bad = match (Σ x : A, y : B x, C x y) [ | Σ x : A, y : B x, C x y ↦ A ]'
   ￫ error[E2202]
   ￭ command-line exec string
   1 | bad = match (Σ x : A, y : B x, C x y) [ | Σ x : A, y : B x, C x y ↦ A ]
     ^ invalid notation pattern: binder-aware notations are not available in patterns
  
  [1]
