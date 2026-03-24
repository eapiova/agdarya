ℕ : Set
ℕ = data [ zero | suc (_:ℕ) ]
plus : (m n : ℕ) → ℕ
plus m n = match n [ zero ↦ m | suc n ↦ suc (plus m n) ]
bool : Set
bool = data [ false | true ]
plus_is_1 : (m n : ℕ) → bool
plus_is_1 m n = match (plus m n) [ zero ↦ false | suc k ↦ match k [ zero ↦ true | suc _ ↦ false ]]
echo plus_is_1 0 1
echo plus_is_1 0 0
echo plus_is_1 1 0
echo plus_is_1 1 1
echo plus_is_1 0 2
⊥ : Set
⊥ = data [ ]
contra : (A C : Set) → (a : A) → (na : A → ⊥) → C
contra A C a na = match na a [ ]
doublematch : (n : ℕ) → bool
doublematch n = match n [ zero ↦ false | suc k ↦ match n [ zero ↦ true | suc _ ↦ false ]]
{- We can quiet the hint this way: -}
doublematch' : (n : ℕ) → bool
doublematch' n = match n [ zero ↦ false | suc k ↦ match n return _ ↦ _ [ zero ↦ true | suc _ ↦ false ]]

⊤ : Set
⊤ = sig ()
zero_or_suc : ℕ → Set
zero_or_suc = λ { zero → ⊤; suc _ → ⊤ }
{- To prove this, we have to specialize the type in the branches, requiring a "return" annotation on the match: -}
plus_zero_or_suc : (m n : ℕ) → zero_or_suc (plus m n)
plus_zero_or_suc m n = match (plus m n) return x ↦ zero_or_suc x [ zero ↦ () | suc _ ↦ () ]

{- We try an indexed inductive type -}
Vec : (A : Set) → ℕ → Set
Vec A = data [ nil : Vec A zero | cons (n:ℕ) (_:A) (_:Vec A n) : Vec A (suc n) ]
idvec : (A : Set) → (n:ℕ) → Vec A n → Vec A n
idvec A n = λ { nil → nil; cons n x xs → cons n x (idvec A n xs) }
nil_or_cons : (n:ℕ) → (A:Set) → Vec A n → Set
nil_or_cons n A = λ { nil → ⊤; cons _ _ _ → ⊤ }
idvec_nil_or_cons : (n:ℕ) → (A:Set) → (v : Vec A n) → nil_or_cons n A (idvec A n v)
idvec_nil_or_cons n A v = match (idvec A n v) return m w ↦ nil_or_cons m A w [ nil ↦ () | cons _ _ _ ↦ () ]
