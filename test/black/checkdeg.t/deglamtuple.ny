Prod : (A B : Set) → Set
Prod A B = sig ( fst : A, snd : B )
postulate A : Set
postulate B : A → Set
postulate C : A → Set
postulate f : (x : A) → B x
postulate g : (x : A) → C x

synth refl (x ↦ (f x, g x))
      : Id ((x : A) → Prod (B x) (C x)) (x ↦ (f x, g x)) (x ↦ (f x, g x))
echo refl (x ↦ (f x, g x))
     : Id ((x : A) → Prod (B x) (C x)) (x ↦ (f x, g x)) (x ↦ (f x, g x))

synth refl (x ↦ f x, x ↦ g x)
      : Id (Prod ((x : A) → (B x)) ((x : A) → (C x))) (f, g) (f, g)
echo refl (x ↦ f x, x ↦ g x)
     : Id (Prod ((x : A) → (B x)) ((x : A) → (C x))) (f, g) (f, g)
