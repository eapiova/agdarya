 {-Church numerals-}

CN : Set

CN = (A : Set) → (A → A) → (A → A)

zero : CN

zero A f x = x

one : CN

one A f x = f x

two : CN

two A f x = f (f x)

three : CN

three A f x = f (f (f x))

four : CN

four A f x = f (f (f (f x)))

one_eq : Id CN one one

one_eq = refl one

cplus : CN → CN → CN

cplus m n A f x = m A f (n A f x)

cplus_one_one_eq_two : Id CN (cplus one one) (two)

cplus_one_one_eq_two = refl two

ctimes : CN → CN → CN

ctimes m n A f x = m A (n A f) x

ctimes_two_two_eq_four : Id CN (ctimes two two) (four)

ctimes_two_two_eq_four = refl four {-Sigma-types-}

Σ : (A : Set) → (B : A → Set) → Set

Σ A B = sig ( fst : A, snd : B fst )

zero_zero : Σ CN (_ ↦ CN)

zero_zero = (zero, zero)

zero_zero_fst_eq_zero : Id CN (zero_zero fst) zero

zero_zero_fst_eq_zero = refl zero

zero_zero_snd_eq_zero : Id CN (zero_zero snd) zero

zero_zero_snd_eq_zero = refl zero

postulate A : Set

postulate B : A → Set

postulate a : A

postulate b : B a

ab : Σ A B

ab = (fst ≔ a, snd ≔ b)

ab_fst_eq_a : Id A (ab fst) a

ab_fst_eq_a = refl a

ab_snd_eq_b : Id (B a) (ab snd) b

ab_snd_eq_b = refl b

ab_fst_eq_a' : Id A (ab .0) a

ab_fst_eq_a' = refl a

ab_snd_eq_b' : Id (B a) (ab .1) b

ab_snd_eq_b' = refl b

zero_zero' : Σ CN (_ ↦ CN)

zero_zero' = (fst ≔ zero, snd ≔ zero)

zero_zero_eq_zero_zero' : Id (Σ CN (_ ↦ CN)) zero_zero zero_zero'

zero_zero_eq_zero_zero' = refl zero_zero {-Coinductive streams-}

Stream : Set → Set

Stream A = codata [ head _ : A | tail _ : Stream A ]

zeros : Stream CN

zeros = record { head = zero; tail = zeros }

zeros_first_term_eq_zero : Id CN (zeros head) (zero)

zeros_first_term_eq_zero = refl zero

zeros_second_term_eq_zero : Id CN (zeros tail head) (zero)

zeros_second_term_eq_zero = refl zero

zeros_third_term_eq_zero : Id CN (zeros tail tail head) (zero)

zeros_third_term_eq_zero = refl zero

zeros_fourth_term_eq_zero : Id CN (zeros tail tail tail head) (zero)

zeros_fourth_term_eq_zero = refl zero

nats : CN → Stream CN

nats n = record { head = n; tail = nats (cplus n one) }

nats_zero_third_term_eq_two : Id CN (nats zero tail tail head) two

nats_zero_third_term_eq_two = refl two

nats_zero_fifth_term_eq_four : Id CN (nats zero tail tail tail tail head)
                                 four

nats_zero_fifth_term_eq_four = refl four {-Bisimulation-}

∞eta : Stream A → Stream A

∞eta s = record { head = s head; tail = ∞eta (s tail) }

∞eta_bisim : (s : Stream A) → Id (Stream A) s (∞eta s)

∞eta_bisim s = record { head = refl (s head); tail = ∞eta_bisim (s tail) } {-Natural numbers-}

ℕ : Set

ℕ = data [ zero | suc (_ : ℕ) ]

Nat : Set

Nat = ℕ

plus : ℕ → ℕ → ℕ

plus m n = case n of λ { ℕ.zero → m; suc n → suc (plus m n)}

times : ℕ → ℕ → ℕ

times m n = case n of λ { ℕ.zero → ℕ.zero; suc n → plus (times m n) m} {-Lists-}

List : Set → Set

List A = data [ nil | cons (x : A) (xs : List A) ]

append : (A : Set) → List A → List A → List A

append A xs ys
=
  case xs of λ { nil → ys; cons x xs → cons x (append A xs ys)}

append_eq_sample : Id (List ℕ)
                     (append ℕ (cons 0 nil) (cons 1 (cons 2 nil)))
                     (cons 0 (cons 1 (cons 2 nil)))

append_eq_sample = refl (append ℕ (cons 0 nil) (cons 1 (cons 2 nil))) {-Vectors-}

Vec : Set → ℕ → Set

Vec A
=
  data [
| nil : Vec A 0
| cons : (n : ℕ) → A → Vec A n → Vec A (suc n) ]

lplus : ℕ → ℕ → ℕ

lplus m n = case m of λ { ℕ.zero → n; suc m → suc (lplus m n)}

vappend : (A : Set) (m n : ℕ) → Vec A m → Vec A n → Vec A (lplus m n)

vappend A m n xs ys
=
  case xs of λ {
nil → ys;
cons k z zs → cons (lplus k n) z (vappend A k n zs ys)}

vappend_eq_sample : Id (Vec ℕ 3)
                      (vappend ℕ 1 2 (cons 0 0 nil)
                         (cons 1 1 (cons 0 2 nil)))
                      (cons 2 0 (cons 1 1 (cons 0 2 nil)))

vappend_eq_sample
=
  refl (vappend ℕ 1 2 (cons 0 0 nil) (cons 1 1 (cons 0 2 nil))) {-Matching lambda-}

exp : ℕ → ℕ → ℕ

exp m = λ { ℕ.zero → suc ℕ.zero; suc n → times (exp m n) m }

exp_eq_sample : Id ℕ (exp 3 2) 9

exp_eq_sample = refl (9 : ℕ)

exp2 : ℕ → ℕ → ℕ

exp2 m = λ { ℕ.zero → suc ℕ.zero; suc n → times (exp m n) m }

exp_eq_sample' : Id ℕ (exp2 2 3) 8

exp_eq_sample' = refl (8 : ℕ) {-Empty Set-}

∅ : Set

∅ = data []

abort1 : (A : Set) → ∅ → A

abort1 A = λ { }

abort2 : (A : Set) → ∅ → A

abort2 A x = case x of λ { } {-Higher-dimensional lambdas in case trees.  This simple version doesn't actually need them, as it could be just an ordinary higher-dimensional lambda term at a leaf-}

postulate f : (x : A) → B x

reflf : Id ((x : A) → B x) f f

reflf {x₀} {x₁} x₂ = refl f x₂

reflf_eq_reflf : Id (Id ((x : A) → B x) f f) reflf (refl f)

reflf_eq_reflf = refl (refl f) {-To test that we actually allow higher-dimensional lambdas in case trees, we need to do some case-tree-only thing inside the lambda, like a match.-}

refl_abort_f : ∅ → Id ((x : A) → B x) f f

refl_abort_f e {x₀} {x₁} x₂ = case e of λ { }

refl_nat_f : ℕ → Id ((x : A) → B x) f f

refl_nat_f n {x₀} {x₁} x₂
=
  case n of λ { ℕ.zero → refl f x₂; suc _ → refl f x₂}

refl_nat_f_eq_reflf : Id (Id ((x : A) → B x) f f) (refl_nat_f ℕ.zero)
                        (refl f)

refl_nat_f_eq_reflf = refl (refl f) {-We also test cube variable abstraction syntax -}

refl_abort_f_cube : ∅ → Id ((x : A) → B x) f f

refl_abort_f_cube e = x ⤇ case e of λ { }

refl_nat_f_cube : ℕ → Id ((x : A) → B x) f f

refl_nat_f_cube n
=
  x ⤇ case n of λ { ℕ.zero → refl f x⟨2⟩; suc _ → refl f x⟨2⟩} {-These are actually *unequal* because definition by case trees is generative. But they become equal when evaluated at concrete numbers so that the case trees compute away.-}

evaluated_eq_sample : Id (Id ((x : A) → B x) f f) (refl_nat_f 3)
                        (refl_nat_f_cube 3)

evaluated_eq_sample = refl (refl_nat_f 3) {-Higher-dimensional matches-}

foo : (x y : ℕ) → Id ℕ x y → ℕ

foo x y p = case p of λ { ℕ.zero ⤇ 0; suc n ⤇ 1}

bar : (x y : ℕ) → Id ℕ x y → ℕ

bar x y = λ { ℕ.zero ⤇ ℕ.zero; suc p ⤇ p⟨0⟩ }

bar_eq_sample : Id ℕ (bar 1 1 (refl (1 : ℕ))) 0

bar_eq_sample = refl (0 : ℕ)

bar_eq_sample' : Id ℕ (bar 2 2 (refl (2 : ℕ))) 1

bar_eq_sample' = refl (1 : ℕ)

prec : ℕ → ℕ

prec = λ { ℕ.zero → ℕ.zero; suc n → n }

idnat : (x y : ℕ) → Id ℕ x y → Id ℕ x y

idnat x y = λ { ℕ.zero ⤇ ℕ.zero; suc p ⤇ suc p⟨2⟩ }

apprec : (x y : ℕ) → Id ℕ x y → Id ℕ (prec x) (prec y)

apprec x y p = case p of λ { ℕ.zero ⤇ ℕ.zero; suc p ⤇ p⟨2⟩}

⊤ : Set

⊤ = sig ()

code : ℕ → ℕ → Set

code
=
  λ {
  ℕ.zero → λ { ℕ.zero → ⊤; suc _ → ∅ };
  suc m → λ { ℕ.zero → ∅; suc n → code m n } }

rcode : (x : ℕ) → code x x

rcode = λ { ℕ.zero → (); suc n → rcode n }

encode : (x y : ℕ) → Id ℕ x y → code x y

encode x y = λ { ℕ.zero ⤇ (); suc p ⤇ encode p⟨0⟩ p⟨1⟩ p⟨2⟩ }

decode : (x y : ℕ) → code x y → Id ℕ x y

decode x y c
=
  case x of λ {
ℕ.zero → case y of λ { ℕ.zero → ℕ.zero; suc _ → case c of λ { }};
suc x → case y of λ { ℕ.zero → case c of λ { }; suc y → suc (decode x y c)}}

encode_decode : (x y : ℕ) (c : code x y)
                → Id (code x y) (encode x y (decode x y c)) c

encode_decode
=
  λ {
  ℕ.zero → λ { ℕ.zero → λ { _ → () }; suc _ → λ { } };
  suc x → λ { ℕ.zero → λ { }; suc y → λ { c → encode_decode x y c } } }

decode_encode : (x y : ℕ) (p : Id ℕ x y)
                → Id (Id ℕ x y) (decode x y (encode x y p)) p

decode_encode x y
=
  λ { ℕ.zero ⤇ ℕ.zero; suc p ⤇ suc (decode_encode p⟨0⟩ p⟨1⟩ p⟨2⟩) } {-Matching on a boundary of a cube variable.-}

mtchbd0 : (e : ∅) (f : ℕ → ℕ) → Id (ℕ → ℕ) f f

mtchbd0 e f
=
  n ⤇ case n⟨0⟩ of λ { ℕ.zero → case e of λ { }; suc _ → case e of λ { }}

mtchbd0' : (e : ∅) (f : ℕ → ℕ) → Id (ℕ → ℕ) f f

mtchbd0' e f
=
  n ⤇ case n⟨0⟩ of λ { ℕ.zero → case e of λ { }; suc _ → refl f n⟨2⟩}

mtchbd0'' : (e : ∅) (f : ℕ → ℕ) → Id (ℕ → ℕ) f f

mtchbd0'' e f {n0} {n1} n2
=
  case n0 of λ { ℕ.zero → case e of λ { }; suc _ → refl f n2} {-Matching inside a tuple -}

mtchtup : ℕ → Σ Set (X ↦ (X → X))

mtchtup n = (case n of λ { ℕ.zero → ℕ; suc _ → ℕ}, x ↦ x)

mtchtup2 : ℕ → Σ ℕ (x ↦ Id ℕ x 0)

mtchtup2 n
=
  (
  fst ≔ case n of λ { ℕ.zero → 0; suc _ → 0},
  snd ≔ case n of λ { ℕ.zero → refl (0 : Nat); suc _ → refl (0 : Nat)}) {-Covectors (canonical types defined inside a match)-}

Covec : Set → ℕ → Set

Covec A n
=
  case n of λ { ℕ.zero → sig (); suc n → sig ( car : A, cdr : Covec A n )}

nil : Covec ℕ 0

nil = ()

onetwo : Covec ℕ 2

onetwo = (1, (2, ()))

covec_eq_sample : Id ℕ (onetwo .0) 1

covec_eq_sample = refl (1 : ℕ)

covec_eq_sample' : Id ℕ (onetwo .1 .0) 2

covec_eq_sample' = refl (2 : ℕ)

covec_eq_sample'' : Id (Covec ℕ 0) (onetwo .1 .1) ()

covec_eq_sample'' = refl (onetwo .1 .1)

coconcat : (A : Set) (m n : ℕ) → Covec A m → Covec A n
           → Covec A (lplus m n)

coconcat A m n v w
=
  case m of λ { ℕ.zero → w; suc m → (v .0, coconcat A m n (v .1) w)}
