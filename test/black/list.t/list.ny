List : Set → Set
List A = data [ nil | cons (x : A) (xs : List A) ]

postulate A : Set

postulate a : A

id00 : Id (List A) nil nil
id00 = nil

id11 : Id (List A) (cons a nil) (cons a nil)
id11 = cons (refl a) nil

id22 : Id (List A) (cons a (cons a nil)) (cons a (cons a nil))
id22 = cons (refl a) (cons (refl a) nil)

{-Check that the induction principle has the right type-}
List_ind : (A : Set) (P : List A → Set) (pn : P nil)
    (pc : (a : A) (l : List A) → P l → P (cons a l)) (l : List A)
    → P l
List_ind A P pn pc l = match l [
| nil ↦ pn
| cons a l ↦ pc a l (List_ind A P pn pc l)]

indty = (A : Set) (P : List A → Set) (pn : P nil)
    (pc : (a : A) (l : List A) → P l → P (cons a l)) (l : List A)
    → P l

indty' = (A : Set) (C : List A → Set) → C nil →
    ((x : A) (xs : List A) → C xs → C (cons x xs)) → (xs : List A)
    → C xs

indty_eq_indty' : Id Set indty indty'
indty_eq_indty' = refl indty

{-We can define concatenation by induction-}
concat : (A : Set) → List A → List A → List A
concat A xs ys = List_ind A (_ ↦ List A) ys (x _ xs_ys ↦ cons x xs_ys) xs

postulate a0 : A

postulate a1 : A

postulate a2 : A

postulate a3 : A

postulate a4 : A

ra01 : List A
ra01 = cons a0 (cons a1 nil)

ra234 : List A
ra234 = cons a2 (cons a3 (cons a4 nil))

a01_234 : List A
a01_234 = concat A ra01 ra234

a01234 : List A
a01234 = cons a0 (cons a1 (cons a2 (cons a3 (cons a4 nil))))

a01_234_eq_a01234 : Id (List A) a01_234 a01234
a01_234_eq_a01234 = refl a01234

{-And prove that it is unital and associative-}
concatlu : (A : Set) (xs : List A) → Id (List A) (concat A nil xs) xs
concatlu A xs = refl xs

concatru : (A : Set) (xs : List A) → Id (List A) (concat A xs nil) xs
concatru A xs =
    List_ind A (ys ↦ Id (List A) (concat A ys nil) ys)
      (refl (nil : List A)) (y ys ysnil ↦ cons (refl y) ysnil) xs

concatassoc : (A : Set) (xs ys zs : List A)
    → Id (List A) (concat A (concat A xs ys) zs)
        (concat A xs (concat A ys zs))
concatassoc A xs ys zs =
    List_ind A
      (xs ↦
       Id (List A) (concat A (concat A xs ys) zs)
         (concat A xs (concat A ys zs))) (refl (concat A ys zs))
      (x xs IH ↦ cons (refl x) IH) xs
