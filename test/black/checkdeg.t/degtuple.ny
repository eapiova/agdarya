Prod : (A B : Set) → Set
Prod A B = sig ( fst : A, snd : B )

postulate A : Set
postulate B : Set
postulate a : A
postulate b : B

echo refl (a, b) : Id (Prod A B) (a, b) (a, b)
echo refl (fst ≔ a, snd ≔ b) : Id (Prod A B) (a, b) (a, b)
echo refl (snd ≔ b, fst ≔ a) : Id (Prod A B) (a, b) (a, b)
