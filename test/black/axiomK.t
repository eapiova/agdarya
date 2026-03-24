Using the Martin-Löf "Jdentity type" as an indexed datatype, we can try to prove versions of Axiom K.

  $ cat >jd.ny <<EOF
  > data Jd (A : Set) (a : A) : A → Set where {
  > | rfl : Jd A a a
  > }
  > EOF

  $ agdarya -source-only jd.ny -v -e 'USIP : (A:Set) → (a:A) → (e:Jd A a a) → Jd (Jd A a a) e rfl' -e 'USIP A a e = match e [ rfl |-> rfl ]'
   ￫ error[E0200]
   ￭ $TESTCASE_ROOT/jd.ny
   2 | | rfl : Jd A a a
     ^ parse error
  
  [1]

  $ agdarya -source-only jd.ny -v -e 'K : (A:Set) → (a:A) → (P : Jd A a a -> Set) → (p : P rfl) → (e : Jd A a a) → P e' -e 'K A a P p e = match e [ rfl |-> p ]'
   ￫ error[E0200]
   ￭ $TESTCASE_ROOT/jd.ny
   2 | | rfl : Jd A a a
     ^ parse error
  
  [1]

This "weak K" is mentioned in the "Pattern-matching without K" paper as justifying their second "injectivity" restriction on unification.

  $ agdarya -source-only jd.ny -v -e 'weakK : (A:Set) → (a:A) → (P : Jd (Jd A a a) rfl rfl -> Set) → (p : P rfl) → (e : Jd (Jd A a a) rfl rfl) → P e' -e 'weakK A a P p e = match e [ rfl |-> p ]'
   ￫ error[E0200]
   ￭ $TESTCASE_ROOT/jd.ny
   2 | | rfl : Jd A a a
     ^ parse error
  
  [1]

The following indexed datatype appears in Agda bug #1025.

  $ cat >foo.ny <<EOF
  > import "jd"
  > postulate A : Set
  > postulate a : A
  > data Foo : Jd A a a → Set where { foo : Foo rfl }
  > EOF

  $ agdarya -source-only jd.ny foo.ny -v -e 'test : (e : Jd A a a) → (f : Foo e) → (i : Jd (Foo e) f f) → Jd (Jd (Foo e) f f) i rfl' -e 'test e f i = match f [ foo ↦ match i [ rfl ↦ rfl ]]'
   ￫ error[E0200]
   ￭ $TESTCASE_ROOT/jd.ny
   2 | | rfl : Jd A a a
     ^ parse error
  
  [1]

The heterogeneous Jdentity type also figures in some inconsistencies, such as Agda bug #1408.

  $ cat >hjd.ny <<EOF
  > data Hd (A : Set) (a : A) : (B : Set) → B → Set where { rfl : Hd A a A a }
  > data Bool : Set where { true : Bool ; false : Bool }
  > data D : Bool → Set where { x : D true ; y : D false }
  > data ∅ : Set where {}
  > EOF

  $ agdarya -source-only hjd.ny -v -e 'notpdf : (u : D false) → (e : Hd (D false) u (D true) x) → ∅' -e 'notpdf u e = match e [ ]'
   ￫ info[I0000]
   ￮ constant Hd defined
  
   ￫ info[I0000]
   ￮ constant Bool defined
  
   ￫ info[I0000]
   ￮ constant D defined
  
   ￫ info[I0000]
   ￮ constant ∅ defined
  
   ￫ error[E1300]
   ￭ command-line exec string
   1 | notpdf u e = match e [ ]
     ^ missing match clause for constructor rfl
  
  [1]
