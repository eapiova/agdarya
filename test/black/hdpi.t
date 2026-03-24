Printing higher-dimensional pi-types

  $ cat >hdpi.ny <<EOF
  > postulate A : Set
  > postulate B : Set
  > postulate E : Id Set A B
  > postulate A' : A → Set
  > postulate B' : B → Set
  > postulate E' : refl ((X ↦ X → Set) : Set → Set) E A' B'
  > echo refl ((A B ↦ (x:A) → B x) : (X:Set) → (X → Set) → Set) E E'
  > EOF

  $ agdarya hdpi.ny
  (x : E) ⇒ E' x.2
    : Set⁽ᵉ⁾ ((x : A) → A' x) ((x : B) → B' x)
  
