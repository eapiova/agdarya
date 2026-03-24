bool : Set
bool = data [ true | false ]
ℕ : Set
ℕ = data [ zero | suc (_ : ℕ) ]

bool.and : (x y : bool) → bool
bool.and x y = match x, y [
| true, true ↦ true
| true, false ↦ false
| false, true ↦ false
| false, false ↦ false]

echo bool.and true true

echo bool.and false true

plus : (m n : ℕ) → ℕ
plus m n = match n [ zero ↦ m | suc n ↦ suc (plus m n) ]

notation(5) x "+" y ≔ plus x y

fib : (n : ℕ) → ℕ
fib n = match n [
| zero ↦ 1
| suc zero ↦ 1
| suc (suc n) ↦ fib n + fib (suc n)]

echo fib 6
echo fib 7

{- Explicit matches can also be deep -}
fib' : (n : ℕ) → ℕ
fib' n = match n return _ ↦ ℕ [
| zero ↦ 1
| suc zero ↦ 1
| suc (suc n) ↦ fib' n + fib' (suc n)]

{- Nondep matches can also be deep -}
fib'' : (n : ℕ) → ℕ
fib'' n = match n return _ ↦ _ [
| zero ↦ 1
| suc zero ↦ 1
| suc (suc n) ↦ fib'' n + fib'' (suc n)]

even : (n : ℕ) → Set
even n = match n [
| zero ↦ data [
  | even_zero ]
| suc zero ↦ data []
| suc (suc n) ↦ data [
  | even_plus2 (_ : even n) ]]

{- Matching lambdas can be deep -}
minus2 : ℕ → ℕ
minus2 = λ {
zero → zero
; suc zero → zero
; suc (suc n) → n}

echo minus2 4

{- Matching lambdas can be multiple -}
bothzero : ℕ → ℕ → bool
bothzero = λ {
zero, zero → true
; zero, suc _ → false
; suc _, _ → false}

echo bothzero 0 2

echo bothzero 2 0

echo bothzero 0 0

⊥ : Set
⊥ = data []

{- Empty matching lambdas can also be multiple -}
abort1 : ⊥ → Set → ⊥
abort1 = λ { }
abort2 : Set → ⊥ → ⊥
abort2 = λ { }

{- Matching lambdas can be higher-dimensional -}
Gel : (A B : Set) → (R : A → B → Set) → Id Set A B
Gel A B R = sig a b ↦ (
  ungel : R a b )
⊤ : Set
⊤ = sig ()
⊤eq⊥ : Id Set ⊤ ⊥
⊤eq⊥ = Gel ⊤ ⊥ (λ { })

foo : (⊤eq⊥ ⇒ ⊤eq⊥) (x ↦ x) (x ↦ x)
foo = λ { }

{- Later variables can be empty -}
one_not_even : even 1 → ⊥
one_not_even = λ { }

suc_even_not_even : (n : ℕ) → (e : even n) → (e1 : even (suc n)) → ⊥
suc_even_not_even n e e1 = match n, e, e1 [
| zero, even_zero, _ ↦ .
| suc zero, _, _ ↦ .
| suc (suc n), even_plus2 e, even_plus2 e1 ↦ suc_even_not_even n e e1]

{- We can omit the refutation cases -}
suc_even_not_even' : (n : ℕ) → (e : even n) → (e1 : even (suc n)) → ⊥
suc_even_not_even' n e e1 = match n, e, e1 [
| suc (suc n), even_plus2 e, even_plus2 e1 ↦ suc_even_not_even n e e1]

sum : (A B : Set) → Set
sum A B = data [ inl (_ : A) | inr (_ : B) ]

{- We can refute a new pattern variable -}
sum⊥ : (A : Set) → (a : sum A ⊥) → A
sum⊥ A a = match a [ inl a ↦ a | inr _ ↦ . ]

{- And we can omit the refutation case if at least one constructor is given -}
sum⊥' : (A : Set) → (a : sum A ⊥) → A
sum⊥' A a = match a [ inl a ↦ a ]

{- We check that omission of a branch doesn't break normalization -}
postulate oops : ⊥

echo sum⊥' Set (inr oops)

{- We can do a non-dependent or explicit match too -}
sum⊥'' : (A : Set) → (a : sum A ⊥) → A
sum⊥'' A a = match a return _ ↦ A [ inl a ↦ a ]

sum⊥''' : (A : Set) → (a : sum A ⊥) → A
sum⊥''' A a = match a return _ ↦ _ [
| inl a ↦ a]

is_zero : ℕ → Set
is_zero = λ { zero → ⊤; suc _ → ⊥ }

{- We can refute a later argument -}
is_zero_eq_zero : (n : ℕ) → (z : is_zero n) → Id ℕ n 0
is_zero_eq_zero n z = match n, z [
| zero, _ ↦ refl (0 : ℕ)
| suc _, _ ↦ .]

{- And we can omit the refutation case if at least one constructor of the necessary split is given. -}
is_zero_eq_zero' : (n : ℕ) → (z : is_zero n) → Id ℕ n 0
is_zero_eq_zero' n z = match n, z [
| zero, _ ↦ refl (0 : ℕ)]

{- We can also refute an *earlier* argument. -}
is_zero_eq_zero_rev : (n : ℕ) → (z : is_zero n) → Id ℕ n 0
is_zero_eq_zero_rev n z = match z, n [
| _, zero ↦ refl (0 : ℕ)
| _, suc _ ↦ .]

{- And we can similarly omit its case -}
is_zero_eq_zero_rev' : (n : ℕ) → (z : is_zero n) → Id ℕ n 0
is_zero_eq_zero_rev' n z = match z, n [
| _, zero ↦ refl (0 : ℕ)]

{- Higher-dimensional matches use ⤇ -}
bar : (y0 y1 : ℕ) → (y2 : Id ℕ y0 y1) → Set
bar y0 y1 y2 = match y2 [
| zero ⤇ ℕ
| suc n ⤇ bar n⟨0⟩ n⟨1⟩ n⟨2⟩ ]

{- Multiple matches use ⤇ if any of them are higher-dimensional -}
bar' : (x : ℕ) → (y0 y1 : ℕ) → (y2 : Id ℕ y0 y1) → Set
bar' x y0 y1 y2 = match x, y2 [
| zero, zero ⤇ ℕ
| zero, suc n ⤇ bar' x n⟨0⟩ n⟨1⟩ n⟨2⟩
| suc _, zero ⤇ ℕ
| suc _, suc n ⤇ bar' x n⟨0⟩ n⟨1⟩ n⟨2⟩ ]

{- But it's only required in the branches that include any higher-dimensional matches. -}
bar'' : (x : ℕ) → (y0 y1 : ℕ) → (y2 : Id ℕ y0 y1) → Set
bar'' x y0 y1 y2 = match x, y2 [
| zero, _ ↦ ℕ
| suc _, zero ⤇ ℕ
| suc _, suc n ⤇ bar'' x n⟨0⟩ n⟨1⟩ n⟨2⟩ ]

{- Same for deep matches -}
baz : Set
baz = data [ baz (y0 y1 : ℕ) (y2 : Id ℕ y0 y1) ]

bazzz : (x : baz) → Set
bazzz x = match x [
| baz _ _ zero ⤇ ℕ
| baz _ _ (suc n) ⤇ bazzz (baz.baz n⟨0⟩ n⟨1⟩ n⟨2⟩)]
