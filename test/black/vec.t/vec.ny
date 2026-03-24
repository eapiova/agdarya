ℕ : Set
ℕ = data [ zero | suc (_ : ℕ) ]

Vec : Set → ℕ → Set
Vec A = data [
| nil : Vec A 0
| cons : (n : ℕ) → A → Vec A n → Vec A (suc n) ]

ℕ_ind : (P : ℕ → Set) (z : P zero) (s : (n : ℕ) → P n → P (suc n)) (n : ℕ)
    → P n
ℕ_ind P z s n = match n [ zero ↦ z | suc n ↦ s n (ℕ_ind P z s n) ]

Vec_ind : (A : Set) (P : (n : ℕ) → Vec A n → Set) (pn : P zero nil)
    (pc : (n : ℕ) (a : A) (v : Vec A n) → P n v → P (suc n) (cons n a v))
    (n : ℕ) (v : Vec A n)
    → P n v
Vec_ind A P pn pc n v = match v [
| nil ↦ pn
| cons n a v ↦ pc n a v (Vec_ind A P pn pc n v)]

postulate A : Set

postulate a : A

{-Identity types-}
id00 : Id (Vec A 0) nil nil
id00 = nil

id11 : Id (Vec A 1) (cons 0 a nil) (cons 0 a nil)
id11 = cons 0 (refl a) nil

id22 : Id (Vec A 2) (cons 1 a (cons 0 a nil)) (cons 1 a (cons 0 a nil))
id22 = cons 1 (refl a) (cons 0 (refl a) nil)

{-Check that the induction principle has the right type-}
indty = (A : Set) (P : (n : ℕ) → Vec A n → Set) (pn : P zero nil)
    (pc : (n : ℕ) (a : A) (v : Vec A n) → P n v → P (suc n) (cons n a v))
    (n : ℕ) (v : Vec A n)
    → P n v

indty' = (A : Set) (C : (n : ℕ) (xs : Vec A n) → Set) → C 0 nil →
    ((n : ℕ) (x : A) (xs : Vec A n) → C n xs → C (suc n) (cons n x xs)) →
    (n : ℕ) (xs : Vec A n)
    → C n xs

indty_eq_indty' : Id Set indty indty'
indty_eq_indty' = refl indty

{-We can define concatenation by induction.  But it works better with a left-recursive version of nat addition.-}
lplus : ℕ → ℕ → ℕ
lplus m n = ℕ_ind (_ ↦ ℕ) n (_ IH ↦ suc IH) m

{-And we prove that addition is associative-}
lplusassoc : (m n k : ℕ) → Id ℕ (lplus (lplus m n) k) (lplus m (lplus n k))
lplusassoc m n k =
    ℕ_ind (m ↦ Id ℕ (lplus (lplus m n) k) (lplus m (lplus n k)))
      (refl (lplus n k)) (_ IH ↦ suc IH) m

{-And right unital-}
lplusru : (m : ℕ) → Id ℕ (lplus m 0) m
lplusru m = ℕ_ind (m ↦ Id ℕ (lplus m 0) m) (refl (0 : ℕ)) (_ IH ↦ suc IH) m

{-Now we can define concatenation-}
concat : (A : Set) (m n : ℕ) → Vec A m → Vec A n → Vec A (lplus m n)
concat A m n xs ys =
    Vec_ind A (m _ ↦ Vec A (lplus m n)) ys
      (m x xs IH ↦ cons (lplus m n) x IH) m xs

postulate a0 : A

postulate a1 : A

postulate a2 : A

postulate a3 : A

postulate a4 : A

ra01 : Vec A 2
ra01 = cons 1 a0 (cons 0 a1 nil)

ra234 : Vec A 3
ra234 = cons 2 a2 (cons 1 a3 (cons 0 a4 nil))

a01_234 : Vec A 5
a01_234 = concat A 2 3 ra01 ra234

a01234 : Vec A 5
a01234 = cons 4 a0 (cons 3 a1 (cons 2 a2 (cons 1 a3 (cons 0 a4 nil))))

a01_234_eq_a01234 : Id (Vec A 5) a01_234 a01234
a01_234_eq_a01234 = refl a01234

{-We can prove that concatenation is associative, "over" associativity of addition.-}
concatassoc : (A : Set) (m n k : ℕ) (xs : Vec A m) (ys : Vec A n) (zs : Vec A k)
    → Id (Vec A) {lplus (lplus m n) k} {lplus m (lplus n k)}
        (lplusassoc m n k) (concat A (lplus m n) k (concat A m n xs ys) zs)
        (concat A m (lplus n k) xs (concat A n k ys zs))
concatassoc A m n k xs ys zs =
    Vec_ind A
      (m xs ↦
       Id (Vec A) {lplus (lplus m n) k} {lplus m (lplus n k)}
         (lplusassoc m n k)
         (concat A (lplus m n) k (concat A m n xs ys) zs)
         (concat A m (lplus n k) xs (concat A n k ys zs)))
      (refl (concat A n k ys zs))
      (m x xs IH ↦ cons (lplusassoc m n k) (refl x) IH) m xs

{-And similarly right unital.-}
concatru : (A : Set) (m : ℕ) (xs : Vec A m)
    → Id (Vec A) {lplus m 0} {m} (lplusru m) (concat A m 0 xs nil) xs
concatru A m xs =
    Vec_ind A
      (m xs ↦
       Id (Vec A) {lplus m 0} {m} (lplusru m) (concat A m 0 xs nil) xs) nil
      (m x xs IH ↦ cons (lplusru m) (refl x) IH) m xs
