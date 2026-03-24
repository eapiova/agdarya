postulate A : Set
postulate a : A
postulate f : A → A

postulate x : A
postulate y : A
postulate xy : Id A x y

{-Records and datatypes-}
Σ : (A : Set) → (A → Set) → Set
Σ A B = sig ( fst : A, snd : B fst )
ℕ : Set
ℕ = data [ zero | suc (_ : ℕ) ]
Nat : Set
Nat = ℕ

postulate B : A → Set
postulate s : Σ A B

{-To test degeneracies on records we have to set up a bunch of stuff, since the simplest case this happens is with Id Gel and squares in the universe.-}
Gel : (A B : Set) → (R : A → B → Set) → Id Set A B
Gel A B R = sig a b ↦ (
  ungel : R a b )

postulate A0 : Set
postulate B0 : Set
postulate R0 : A0 → B0 → Set
postulate A1 : Set
postulate B1 : Set
postulate R1 : A1 → B1 → Set
postulate A2 : Id Set A0 A1
postulate B2 : Id Set B0 B1
postulate R2 : refl ((X ↦ Y ↦ (X → Y → Set)) : Set → Set → Set) A2 B2 R0 R1
postulate a0 : A0
postulate a1 : A1
postulate a2 : A2 a0 a1
postulate b0 : B0
postulate b1 : B1
postulate b2 : B2 b0 b1
postulate r0 : R0 a0 b0
postulate r1 : R1 a1 b1
postulate r2 : R2 a2 b2 r0 r1


r2ty = refl Gel A2 B2 R2 a2 b2 (ungel ≔ r0) (ungel ≔ r1)

symr2ty = sym (refl Gel A2 B2 R2) {a0} {b0} (ungel ≔ r0) {a1} {b1} (ungel ≔ r1) a2
      b2

postulate gg : r2ty

postulate gg' : symr2ty

{-Cube variables-}
postulate af : A → Id (A → A) f f

{-Stream-}
Stream : (A : Set) → Set
Stream A = codata [
| head _ : A
| tail _ : Stream A ]
zeros : Stream ℕ
zeros = record { head = 0; tail = zeros }
postulate idz : Id (Stream ℕ) zeros zeros
