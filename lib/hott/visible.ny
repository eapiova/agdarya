isBisim : (A : Set) → (B : Set) → (R : A → B → Set) → Set
isBisim A B R = codata [
| trr x : A → B
| liftr x : (a : A) → R a (x trr a)
| trl x : B → A
| liftl x : (b : B) → R (x trl b) b
| id⟨e⟩ x
  : (a0 : A.0) (b0 : B.0) (r0 : R.0 a0 b0) (a1 : A.1) (b1 : B.1)
    (r1 : R.1 a1 b1)
    → isBisim (A.2 a0 a1) (B.2 b0 b1) (a2 b2 ↦ R.2 a2 b2 r0 r1) ]

glue : (A : Set) → (B : Set) → (R : A → B → Set) → (Rb : isBisim A B R) → Id Set A B
glue A B R Rb = sig x y ↦ (
  unglue : R x y )
