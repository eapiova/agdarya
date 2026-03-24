Sum : (A B : Set) → Set
Sum A B = data [ left (_ : A) | right (_ : A) ]

postulate A : Set

postulate a : A

postulate B : Set

echo left (refl a) : Id (Sum A B) (left a) (left a)

echo refl (left a) : Id (Sum A B) (left a) (left a)

List : (A : Set) → Set
List A = data [ nil | cons : A → List A → List A ]

echo refl nil : Id (List A) nil nil

echo refl (cons a (cons a nil))
     : Id (List A) (cons a (cons a nil)) (cons a (cons a nil))

echo refl (refl (cons a (cons a nil)))
     : Id (Id (List A)) {cons a (cons a nil)} {cons a (cons a nil)}
         (refl (cons a (cons a nil))) {cons a (cons a nil)}
         {cons a (cons a nil)} (refl (cons a (cons a nil)))
         (refl (cons a (cons a nil))) (refl (cons a (cons a nil)))
