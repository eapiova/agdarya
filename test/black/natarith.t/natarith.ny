ℕ : Set
ℕ = data [ zero | suc (_ : ℕ) ]

O : ℕ
O = 0

S : ℕ → ℕ
S n = suc n

plus : ℕ → ℕ → ℕ
plus m n = match n [ zero ↦ m | suc n ↦ suc (plus m n) ]

times : ℕ → ℕ → ℕ
times m n = match n [
| zero ↦ zero
| suc n ↦ plus (times m n) m]

ℕ_ind : (P : ℕ → Set) (z : P zero) (s : (n : ℕ) → P n → P (suc n)) (n : ℕ)
    → P n
ℕ_ind P z s n = match n [ zero ↦ z | suc n ↦ s n (ℕ_ind P z s n) ]

zero : ℕ
zero = 0

one : ℕ
one = 1

two : ℕ
two = 2

three : ℕ
three = 3

four : ℕ
four = 4

{-Identity types -}
id00 : Id ℕ zero zero
id00 = ℕ.zero

id00' : Id ℕ zero zero
id00' = refl (zero : ℕ)

id00'' : Id ℕ zero zero
id00'' = refl zero

id11 : Id ℕ one one
id11 = refl one

congsuc : (x : ℕ) (y : ℕ) → Id ℕ x y → Id ℕ (suc x) (suc y)
congsuc x y p = suc p

cong2suc : (x00 : ℕ) (x01 : ℕ) (x02 : Id ℕ x00 x01) (x10 : ℕ) (x11 : ℕ)
    (x12 : Id ℕ x10 x11) (x20 : Id ℕ x00 x10) (x21 : Id ℕ x01 x11)
    (x22 : Id (Id ℕ) x02 x12 x20 x21)
    → (Id (Id ℕ) {suc x00} {suc x01} (suc x02) {suc x10} {suc x11}
         (suc x12) (suc x20) (suc x21))
cong2suc x00 x01 x02 x10 x11 x12 x20 x21 x22 = suc x22

{-Addition-}
one_plus_one_eq_two : Id ℕ (plus one one) two
one_plus_one_eq_two = refl two

one_plus_two_eq_three : Id ℕ (plus one two) three
one_plus_two_eq_three = refl three

two_plus_zero_eq_two : Id ℕ (plus two zero) two
two_plus_zero_eq_two = refl two

zero_plus_zero_eq_zero : Id ℕ (plus zero zero) zero
zero_plus_zero_eq_zero = refl zero

zero_plus_one_eq_one : Id ℕ (plus zero one) one
zero_plus_one_eq_one = refl one

zero_plus_two_eq_two : Id ℕ (plus zero two) two
zero_plus_two_eq_two = refl two

{-Refl of a constant still computes-}
r000 : Id (Id ℕ zero zero) (refl (plus zero zero)) (refl zero)
r000 = refl (refl zero)

r112 : Id (Id ℕ two two) (refl (plus one one)) (refl two)
r112 = refl (refl two)

{-We can also define addition with the general recursor/inductor-}
rplus : ℕ → ℕ → ℕ
rplus m n = ℕ_ind (_ ↦ ℕ) m (_ IH ↦ suc IH) n

one_plus_one_eq_two' : Id ℕ (rplus one one) two
one_plus_one_eq_two' = refl two

one_plus_two_eq_three' : Id ℕ (rplus one two) three
one_plus_two_eq_three' = refl three

two_plus_zero_eq_two' : Id ℕ (rplus two zero) two
two_plus_zero_eq_two' = refl two

zero_plus_zero_eq_zero' : Id ℕ (rplus zero zero) zero
zero_plus_zero_eq_zero' = refl zero

zero_plus_one_eq_one' : Id ℕ (rplus zero one) one
zero_plus_one_eq_one' = refl one

zero_plus_two_eq_two' : Id ℕ (rplus zero two) two
zero_plus_two_eq_two' = refl two

{-And prove by induction that it equals the other one  Note that this uses ap on suc-}
plus_is_rplus : (x : ℕ) (y : ℕ) → Id ℕ (plus x y) (rplus x y)
plus_is_rplus x y = ℕ_ind (u ↦ Id ℕ (plus x u) (rplus x u)) (refl x) (u q ↦ suc q) y

{-We also have multiplication-}

one_times_zero_eq_zero : Id ℕ (times one zero) zero
one_times_zero_eq_zero = refl zero

zero_times_one_eq_zero : Id ℕ (times zero one) zero
zero_times_one_eq_zero = refl zero

one_times_one_eq_one : Id ℕ (times one one) one
one_times_one_eq_one = refl one

two_times_two_eq_four : Id ℕ (times two two) four
two_times_two_eq_four = refl four
