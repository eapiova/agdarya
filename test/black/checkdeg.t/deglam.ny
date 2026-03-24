postulate A : Set
postulate B : A → Set
postulate f : (x : A) → B x

synth refl (x ↦ f x) : Id ((x : A) → B x) f f
echo refl (x ↦ f x) : Id ((x : A) → B x) f f
