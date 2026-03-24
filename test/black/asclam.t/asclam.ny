postulate A : Set

synth (x : A) ↦ x

postulate B : A → Set

postulate C : A → Set

postulate f : (x : A) → B x

postulate g : (x : A) → B x → C x

synth (x : A) ↦ g x (f x)

postulate a : A

echo ((x : A) ↦ x) a
echo ((x : A) ↦ g x (f x)) a

unit : Set
unit = sig ()

echo ((x : A) ↦ ()) : A → unit
