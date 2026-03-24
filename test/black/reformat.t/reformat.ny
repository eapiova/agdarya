postulate A : Set

postulate B : Set

postulate C : Set {- block 1 -} -- line comment

{- block 2 -}
postulate D : Set -- line comment

postulate E : Set --line comment

postulate {- block
  comment -} F : Set

postulate G {- block
  comment -} : Set

postulate H : {- block
  comment -} Set

postulate I : Set {- block 1 -} {- block 2 -} {- block 3 -}

echo A

echo -- line comment
  A

echo A -- line comment

echo {- block
  comment-} A

ℕ : Set
ℕ = data [ zero | suc (_ : ℕ) ]

ℕ1 : Set
ℕ1 = data [ -- line comment
| zero
| suc (_ : ℕ) ]

ℕ2 : Set
ℕ2 = data [ {- block
comment -}
| zero
| suc (_ : ℕ) ]

ℕ3 : Set
ℕ3 = data [
| zero
| suc (_ : ℕ) --line comment
]

ℕ4 : Set
ℕ4 = data [
| zero
| suc
    (_
     : --line comment
     ℕ) ]

ℕ5 : Set
ℕ5 = data [
| zero
| suc
    (_ --line comment
     : ℕ) ]

ℕ6 : Set
ℕ6 = data [
| zero
| suc --line comment
    (_ : ℕ) ]

Vec : (A : Set) → ℕ → Set
Vec A = data [
| nil : Vec A 0
| cons (n : ℕ) (x : A) (xs : Vec A n) : Vec A (suc n) ]

Vec1 : (A : Set) → ℕ → Set
Vec1 A = data [
| nil : Vec1 A 0
| cons (n : ℕ) {- block
    comment -}
    (x : A) (xs : Vec1 A n)
  : Vec1 A (suc n) ]

lots : Set
lots = data [
| boo (_ : A) (_ : A) (_ : A) (_ : A) (_ : A) (_ : A) (_ : A) (_ : A)
    (_ : A) (_ : A) (_ : A) (_ : A) (_ : A) (_ : A) ]

lots2 : Set
lots2 = (data [
| boo (_ : A) (_ : A) (_ : A) (_ : A) (_ : A) (_ : A) (_ : A) (_ : A)
    (_ : A) (_ : A) (_ : A) (_ : A) (_ : A) (_ : A) ])

prod : (A B : Set) → Set
prod A B = sig ( fst : A, snd : B )

prod2 : (A B : Set) → Set
prod2 A B = sig (
  fst : A, --line comment
  snd : B )

prod3 : (A B : Set) → Set
prod3 A B = sig (
  fst : --line comment
    A,
  snd : B )

prod4 : (A B : Set) → Set
prod4 A B = sig (
  fst --line comment
    : A,
  snd : B )

_&_ : A → A → A
_&_ x y = x
infix 0 _&_

triple : prod ℕ (prod ℕ ℕ)
triple = (0, (0, 0))

triple2 : prod ℕ (prod ℕ ℕ)
triple2 = (
  0, --comment
  (0, 0))

triple3 : prod ℕ (prod ℕ ℕ)
triple3 = (
  0, --comment
  (0, --comment
   0))

postulate f :
  A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A →
    A → A
    → ℕ

postulate f2 : (x : A) → B → C

postulate f3 : (x : A) → B → C

postulate f4 : (x : A) → B → C

postulate f5 : (x : A) → B →
  C → C → C → C → C → C → C → C → C → C → C → C → C → C → C → C → C → C → C
  → C

postulate a : A

faaa = f a --hello
      --goodbye
      a a

faaa1 = f a {- hello -}
      --goodbye
      a a

faaa2 = f a {- hello
      world -}
      --goodbye
      a a

faaa3 = f a
      --goodbye
      a a

faaa4 = f a a a

faaa5 = f a a a

postulate a_long_thing : A

flong : ℕ
flong = f a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing

flong2 : ℕ
flong2 = f a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing
    : ℕ

ftype : A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A →
    A
    → Set
ftype _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = ℕ

flong3 : ℕ
flong3 = f a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing
    : ftype a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
        a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
        a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
        a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing

postulate ftoftype :
  A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A →
    A → A
    → ftype a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
        a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
        a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
        a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing

postulate a_very_long_type_to_wrap_the_line : Set

postulate a_very_long_term_to_wrap_the_line : a_very_long_type_to_wrap_the_line

a_very_long_thing_to_wrap_the_line : a_very_long_type_to_wrap_the_line
a_very_long_thing_to_wrap_the_line = a_very_long_term_to_wrap_the_line

postulate Q : ℕ → Set

{-
qq : Q
(f a_long_thing a_long_thing a_long_thing a_long_thing
a_long_thing a_long_thing a_long_thing a_long_thing
a_long_thing a_long_thing a_long_thing a_long_thing
a_long_thing a_long_thing a_long_thing a_long_thing
a_long_thing a_long_thing a_long_thing a_long_thing
a_long_thing)
→ Q
(f a_long_thing a_long_thing a_long_thing a_long_thing
a_long_thing a_long_thing a_long_thing a_long_thing
a_long_thing a_long_thing a_long_thing a_long_thing
a_long_thing a_long_thing a_long_thing a_long_thing
a_long_thing a_long_thing a_long_thing a_long_thing
a_long_thing)
qq x = ?
-}

pair : prod ℕ ℕ
pair = (
  f a a a a a a a a a a a a a a a a a a a a a,
  f a a a a a a a a a a a a a a a a a a a a a)

pair2 : prod ℕ ℕ
pair2 = (
  fst ≔ f a a a a a a a a a a a a a a a a a a a a a,
  snd ≔ f a a a a a a a a a a a a a a a a a a a a a)

lpair2 : prod ℕ ℕ
lpair2 = (
  fst ≔
    f a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing,
  snd ≔
    f a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing)

triple4 : prod ℕ (prod ℕ ℕ)
triple4 = (
  fst ≔ f a a a a a a a a a a a a a a a a a a a a a,
  snd ≔ (
    f a a a a a a a a a a a a a a a a a a a a a,
    f a a a a a a a a a a a a a a a a a a a a a))

-- This is the purpose of the 'trivial' intros data
triple5 : prod ℕ (prod ℕ ℕ)
triple5 = (
  f a a a a a a a a a a a a a a a a a a a a a,
  (f a a a a a a a a a a a a a a a a a a a a a,
   f a a a a a a a a a a a a a a a a a a a a a))

abstriple : ℕ → prod ℕ (prod ℕ ℕ)
abstriple x = (
  fst ≔ f a a a a a a a a a a a a a a a a a a a a a,
  snd ≔ (
    f a a a a a a a a a a a a a a a a a a a a a,
    f a a a a a a a a a a a a a a a a a a a a a))

abstriple1 : ℕ → prod ℕ (prod ℕ ℕ)
abstriple1 this_is_a_very_long_variable_name_to_wrap_the_line = (
  fst ≔ f a a a a a a a a a a a a a a a a a a a a a,
  snd ≔ (
    f a a a a a a a a a a a a a a a a a a a a a,
    f a a a a a a a a a a a a a a a a a a a a a))

id : ℕ → ℕ
id a_very_long_variable_name = match a_very_long_variable_name [
| zero ↦ zero
| suc x ↦ suc x]

id2 : ℕ → ℕ
id2 this_is_a_very_long_variable_name_to_wrap_the_line =
      match this_is_a_very_long_variable_name_to_wrap_the_line [
| zero ↦ zero
| suc x ↦ suc x]

⊤ : Set
⊤ = sig ()

⊥ : Set
⊥ = data []

ℕeq : ℕ → ℕ → Set
ℕeq m n = match m [
| zero ↦ match n [ zero ↦ ⊤ | suc _ ↦ ⊥ ]
| suc m ↦ match n [ zero ↦ ⊥ | suc n ↦ ℕeq m n ]]

longfun : Set
longfun = (x : A) (x : A) (x : A) (x : A) (x : A) (x : A) (x : A) (x : A) (x : A)
    (x : A)
    → C

longfun1 : Set
longfun1 = (x : A) → (x : A) → (x : A) → (x : A) → (x : A) → (x : A) → (x : A) →
    (x : A)
    → C

longfun2 : Set
longfun2 = A → A → A → A → A → A → A → A → A → A → B

longfun3 : Set
longfun3 = A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A
    → B

longfun4 : Set
longfun4 = (x : A) (x : A) (x : A) → A → (x : A) (_ : A) (x : A) (x : A) → (x : A)
    → C

postulate P : ℕ → Set

{- This looks a little weird, but I think only because "P" is so short. -}
longfun5 : Set
longfun5 = A → A → A →
    P
      (f a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
         a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
         a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
         a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
         a_long_thing) → A → A
    → B

wrap : (A : Set) → Set
wrap A = codata [ unwrap x : A ]

postulate object :
  A → A → A → A → A → A → A
    → wrap
        (A → A → A → A → A → wrap (A → A → A → A → A → A → wrap (A → A → B)))

objectb : B
objectb = object a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
        a_long_thing a_long_thing
      unwrap a_long_thing a_long_thing a_long_thing a_long_thing
        a_long_thing
      unwrap a_long_thing a_long_thing a_long_thing a_long_thing
        a_long_thing a_long_thing
      unwrap a_long_thing a_long_thing

postulate bareobj : wrap (A → A → A → A → A → B)

bareb : B
bareb = bareobj unwrap a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing

postulate toobj : A → A → A → A → A → A → A → A → wrap B

tob : B
tob = toobj a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
      a_long_thing a_long_thing a_long_thing unwrap

postulate wraps :
  wrap
      (wrap
         (wrap
            (wrap
               (wrap
                  (wrap
                     (wrap
                        (wrap
                           (wrap
                              (wrap
                                 (wrap
                                    (wrap
                                       (wrap
                                          (wrap
                                             (wrap
                                                (wrap
                                                   (wrap
                                                      (wrap (wrap (wrap B)))))))))))))))))))

wrapb : B
wrapb = wraps unwrap unwrap unwrap unwrap unwrap unwrap unwrap unwrap
      unwrap unwrap unwrap unwrap unwrap unwrap unwrap unwrap unwrap
      unwrap unwrap unwrap

bigabs : A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A → A →
    A
    → A
bigabs = longvar longvar longvar longvar longvar longvar longvar longvar longvar
      longvar longvar longvar longvar longvar longvar longvar longvar longvar
      longvar longvar ↦
    longvar

plus : ℕ → ℕ → ℕ
plus = λ { zero → λ n → n; suc m → λ n → suc (plus m n) }

tlet0 : ℕ
tlet0 = let a_long_variable : ℕ ≔ 0 in a_long_variable

tlet00 : ℕ
tlet00 = let an_even_longer_variable_name : ℕ ≔ 0 in
  an_even_longer_variable_name

tlet : ℕ
tlet = let a_long_variable : ℕ ≔ (plus (plus 0 (plus 0 0)) (plus 0 (plus 0 0))) in
  a_long_variable

tlet1 : ℕ
tlet1 = let a_long_variable
    : A → A → A → A → A → A → A → A → A → A → A → A → A → A → ℕ
    ≔ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ↦
      (plus (plus 0 (plus 0 0)) (plus 0 (plus 0 0))) in
  a_long_variable a a a a a a a a a a a a a a

tlet2 : prod ℕ ℕ
tlet2 = let a_long_variable : ℕ ≔ (plus (plus 0 (plus 0 0)) (plus 0 (plus 0 0))) in
  (a_long_variable, a_long_variable)

dlet : ℕ
dlet = let a_long_variable : ℕ ≔ 0 in let y : ℕ ≔ 0 in y

dlet2 : ℕ
dlet2 = let a_long_variable : ℕ ≔ 0 in
  let another_long_variable : ℕ ≔ 0 in
  another_long_variable

{- TODO: Could we collapse those abstractions onto one line? -}
dlet3 : A → A → A → A → ℕ
dlet3 = let a_long_variable : ℕ ≔ 0 in
  x y ↦
  z w ↦
  let another_long_variable : ℕ ≔ 0 in
  let yet_another_long_variable : ℕ ≔ 0 in
  another_long_variable

dlet4 : A → A → A → A → ℕ
dlet4 x =
  let a_long_variable : ℕ ≔ 0 in
  y z ↦
  let another_long_variable : ℕ ≔ 0 in
  let yet_another_long_variable : ℕ ≔ 0 in
  w ↦ another_long_variable

mlet : ℕ → ℕ → ℕ
mlet = let a_long_variable : ℕ ≔ (plus (plus 0 (plus 0 0)) (plus 0 (plus 0 0))) in
  match a_long_variable [
  | zero ↦
      let another_long_variable : ℕ
        ≔ (plus (plus 0 (plus 0 0)) (plus 0 (plus 0 0))) in
      x ↦ y ↦ 0
  | suc _ ↦ x ↦ y ↦ 0]

mtup : ℕ → prod ℕ ℕ
mtup = λ { zero → (0, 0); suc n → (n, n) }

mtup2 : ℕ → prod ℕ ℕ
mtup2 = λ {
  zero → (
    0, --line comment
    0);
  suc n → (fst ≔ n, snd ≔ n) }

mtm : ℕ → ℕ → prod ℕ ℕ
mtm m = λ {
  zero → (match m [ zero ↦ 0 | suc m ↦ 0 ], 0);
  suc n → (fst ≔ n, snd ≔ match m [ zero ↦ 0 | suc m ↦ 0 ]) }

postulate blahblah : A → A → A → A

postulate blahblah2 : A → A

postulate blahblah3 : A

blahblah4 : A
blahblah4 = blahblah (blahblah2 blahblah3) (blahblah2 (blahblah2 blahblah3))
      (blahblah blahblah3 blahblah3 blahblah3)

blahblah5 : A
blahblah5 = blahblah (blahblah2 blahblah3) -- line comment
      (blahblah2 (blahblah2 blahblah3))
      (blahblah blahblah3 blahblah3 blahblah3)

blahblah6 : A
blahblah6 = blahblah -- line comment
      (blahblah2 blahblah3) (blahblah2 (blahblah2 blahblah3))
      (blahblah blahblah3 blahblah3 blahblah3)

blahblah7 : A → A
blahblah7 bleh =
    blahblah -- line comment
      (blahblah2 blahblah3) (blahblah2 (blahblah2 blahblah3))
      (blahblah blahblah3 blahblah3 blahblah3)

blahblah8 : A → A → A → A → A → A → A → A → A → A → A → A → A
blahblah8 = blehbleh blehbleh blehbleh blehbleh blehbleh blehbleh blehbleh blehbleh
      blehbleh blehbleh blehbleh blehbleh ↦
    blahblah -- line comment
      (blahblah2 blahblah3) (blahblah2 (blahblah2 blahblah3))
      (blahblah blahblah3 blahblah3 blahblah3)

blubblub : A → A → A → A → A → Set
blubblub _ _ _ _ _ = A

bb : A
bb = let bubble
    : blubblub blahblah3 blahblah3 (blahblah2 (blahblah2 blahblah3))
        blahblah3 blahblah3
    ≔ blahblah (blahblah2 blahblah3) (blahblah2 (blahblah2 blahblah3))
        (blahblah blahblah3 blahblah3 blahblah3) in
  bubble

postulate unpair : prod A A → A

unpaired : A
unpaired = unpair (a, a)

unpaired2 : A
unpaired2 = unpair
      (blahblah (blahblah2 blahblah3) (blahblah2 (blahblah2 blahblah3))
         (blahblah blahblah3 blahblah3 blahblah3),
       blahblah (blahblah2 blahblah3) (blahblah2 (blahblah2 blahblah3))
         (blahblah blahblah3 blahblah3 blahblah3))

unpaired3 : A
unpaired3 = unpair (blahblah2 (blahblah2 blahblah3), blahblah2 (blahblah2 blahblah3))

unpaired4 : A
unpaired4 = unpair
      (fst ≔ blahblah2 (blahblah2 blahblah3),
       snd ≔ blahblah2 (blahblah2 blahblah3))

ml : ℕ → ℕ
ml = let x : ℕ ≔ 0 in λ { zero → 0; suc _ → 0 }

ml2 : ℕ → ℕ
ml2 = let x : ℕ ≔ 0 in
  λ { zero -- line comment
      →
      0
    ; suc _ → 0 }

ml3 : ℕ → ℕ
ml3 = let x : ℕ ≔ 0 in
  λ { zero → 0 -- line comment
    ; suc _ → 0 }

stream : (A : Set) → Set
stream A = codata [ head x : A | tail x : stream A ]

zeros : stream ℕ
zeros = record { head = 0; tail = zeros }

zeros2 : stream ℕ
zeros2 = record {
  head = 0 --comment
; tail = zeros }

dup : ℕ → stream ℕ
dup n = record {
  head = match n [ zero ↦ 0 | suc _ ↦ 0 ];
  tail = dup n }

fs : stream ℕ
fs = record {
  head =
    f a_long_thing a_long_thing a_long_thing a a a a a a a a a a a a a a a a
      a_long_thing a_long_thing
; tail = zeros }

ssz : stream (stream ℕ)
ssz = record {
  head = record { head = 0; tail = ssz head };
  tail = ssz }

postulate fsn :
  A → A → A → A → A → A → A → A → A → A → stream (stream ℕ)
    → stream (stream ℕ)

ssz2 : stream (stream ℕ)
ssz2 = record {
  head = record {
    head = 0;
    tail =
      fsn a_long_thing a a_long_thing a a_long_thing a a_long_thing a
        a_long_thing a_long_thing ssz2 head };
  tail = ssz }

mss : ℕ → stream (stream (prod ℕ ℕ))
mss n = record {
  head = record {
    head = match n [ zero ↦ (0, 0) | suc n ↦ (0, n) ];
    tail = mss 0 head };
  tail = mss 0 }

notation(3) A "×" B ≔ prod A B

notation(3) AAAAAAAAAAAAAAAAAAAA "×₁" BBBBBBBBBBBBBBBBBBBB
  ≔ prod AAAAAAAAAAAAAAAAAAAA BBBBBBBBBBBBBBBBBBBB

notation(3)
  AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA "×₂"
      BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB
  ≔ prod AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA
      BBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBBB

echo ℕ

echo f a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing

echo f a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
       a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing

synth f a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
        a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing

section foo ≔

  x : ℕ
  x = 3

  fooflong : ℕ
  fooflong = f a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
        a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
        a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
        a_long_thing a_long_thing a_long_thing a_long_thing a_long_thing
        a_long_thing

  section bar ≔

    y : ℕ
    y = f a a a a a a a a a a a a a a a a a a a a a

  end

end

x : ℕ
x = 0

y : ℕ
y = 0

{- block comment -}
x2 : ℕ
x2 = 0 -- line comment

--line comment
y2 : ℕ
y2 = 0

xy : ℕ
xy = let rec x : ℕ ≔ 0 and y : ℕ ≔ 0 in x

xy1 : ℕ
xy1 = let rec x : ℕ ≔ 0 --line comment
  {- block comment -}
  and y : ℕ ≔ 0 in
  x

xy2 : ℕ
xy2 = let rec x : ℕ --line comment
    ≔ 0
  and y --line comment
    : ℕ
    ≔ 0 in
  x

import "importable"

import "importable" | all

import "importable"
  | seq (renaming squab squish,
         renaming squish squab,
         renaming squab squish,
         renaming squish squab)

{- long parameter lists -}
eq : (A : Set) → (a : A) → A → Set
eq A a = data [ rfl : eq A a a ]

cat : (A : Set) → (x y z : A) → (u : eq A x y) → (v : eq A y z) → eq A x z
cat A x y z u v = match v [ rfl ↦ u ]

cat3 : (A : Set) → (x y z w : A) → (p : eq A x y) → (q : eq A y z) → (r : eq A z w) → eq A x w
cat3 A x y z w p q r = match q, r [ rfl, rfl ↦ p ]

{- empty match -}

abort : (A : Set) → (e : ⊥) → A
abort A e = match e [ ]

{- fractional tightness notations -}
postulate binop : A → A → A

notation(1.5) x "*+*" y ≔ binop x y

postulate _+_ : A → A → A

infixl 6 _+_

postulate -_ : A → A

infixr 8 -_

postulate if_then_else_ : A → A → A → A

infix 0 if_then_else_

postulate Fam : A → Set

postulate All : (X : Set) → (X → Set) → Set

notation(0) "∀" [x] ":" A "," B := All A B

echo (∀ x y:A,A)

echo (∀ x : A, y : Fam x, A)

postulate SigmaBody : (x : A) → Fam x → Set

postulate Sigma2 : (X : Set) → (Y : X → Set) → ((x : X) → Y x → Set) → Set

notation(0) "Σ" [x] ":" X "," [y] ":" Y "," Z := Sigma2 X Y Z

echo (Σ x:A,y : Fam x,SigmaBody x y)
