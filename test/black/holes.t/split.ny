{- This file is NOT executed by run.t.  It's for manual testing of the PG split function C-c C-y -}

ℕ : Set
ℕ = data [ zero | suc (n : ℕ) ]

plus : (m n : ℕ) → ℕ
plus m n = match m, n [
| zero, zero ↦ ¿ʔ
| zero, suc n ↦ ¿ʔ
| suc m, zero ↦ ¿ʔ
| suc m, suc n ↦ ¿ʔ]

⊥ : Set
⊥ = data []

foo : (x : ℕ) → (y : ⊥) → Set
foo x y = ¿ʔ

bar : (x : ℕ) → (y0 y1 : ℕ) → (y2 : Id ℕ y0 y1) → Set
bar x y0 y1 y2 = ¿ʔ

baz : Set
baz = data [ baz (y0 y1 : ℕ) (y2 : Id ℕ y0 y1) ]

bazzz : (x : baz) → Set
bazzz x = match x [
| baz _ _ zero ⤇ ℕ
| baz _ _ (suc n) ⤇ bazzz (baz n⟨0⟩ n⟨1⟩ n⟨2⟩)]

f : (a : ℕ) (b : ℕ) → Set
f = ¿ʔ

postulate g : ℕ → ℕ
ge : Id ((x : ℕ) → ℕ) g g
ge = ¿ʔ

ℕ×ℕ : Set
ℕ×ℕ = sig ( fst : ℕ, snd : ℕ )

nn : ℕ×ℕ
nn = ¿ʔ

postulate mm : ℕ×ℕ
mme : Id ℕ×ℕ mm mm
mme = ¿ʔ

Sℕ : Set
Sℕ = codata [ head s : ℕ | tail s : Sℕ ]

sn : Sℕ
sn = ¿ʔ
postulate sm : Sℕ
sme : Id Sℕ sm sm
sme = ¿ʔ

√ℕ : Set
√ℕ = codata [ root⟨e⟩ x : ℕ ]

qn : √ℕ
qn = ¿ʔ
postulate qm : √ℕ
qme : Id √ℕ qm qm
qme = ¿ʔ
