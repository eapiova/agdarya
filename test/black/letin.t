Testing let-bindings

  $ cat >pre.ny <<EOF
  > postulate A:Set
  > postulate a0:A
  > postulate a1:A
  > postulate a2: Id A a0 a1
  > postulate B : A → Set
  > postulate b : B a0
  > postulate f : (x:A) → B x → B x
  > EOF

  $ agdarya -source-only -v pre.ny -e "a0' : A" -e "a0' = let id ≔ ((x ↦ x) : A → A) in id a0" -e "test : Id A a0 a0'" -e "test = refl a0"
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate a0 assumed
  
   ￫ info[I0001]
   ￮ postulate a1 assumed
  
   ￫ info[I0001]
   ￮ postulate a2 assumed
  
   ￫ info[I0001]
   ￮ postulate B assumed
  
   ￫ info[I0001]
   ￮ postulate b assumed
  
   ￫ info[I0001]
   ￮ postulate f assumed
  
   ￫ info[I0000]
   ￮ constant a0' defined
  
   ￫ info[I0000]
   ￮ constant test defined
  

  $ agdarya -source-only -v pre.ny -e "a0' : A" -e "a0' = let id : A → A ≔ x ↦ x in id a0" -e "test : Id A a0 a0'" -e "test = refl a0"
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate a0 assumed
  
   ￫ info[I0001]
   ￮ postulate a1 assumed
  
   ￫ info[I0001]
   ￮ postulate a2 assumed
  
   ￫ info[I0001]
   ￮ postulate B assumed
  
   ￫ info[I0001]
   ￮ postulate b assumed
  
   ￫ info[I0001]
   ￮ postulate f assumed
  
   ￫ info[I0000]
   ￮ constant a0' defined
  
   ￫ info[I0000]
   ￮ constant test defined
  

It matters what the variable is bound to:

  $ agdarya -source-only -v pre.ny -e "a0' : A" -e "a0' = let id : A → A ≔ x ↦ a1 in id a0" -e "untest : Id A a0 a0'" -e "untest = refl a0"
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate a0 assumed
  
   ￫ info[I0001]
   ￮ postulate a1 assumed
  
   ￫ info[I0001]
   ￮ postulate a2 assumed
  
   ￫ info[I0001]
   ￮ postulate B assumed
  
   ￫ info[I0001]
   ￮ postulate b assumed
  
   ￫ info[I0001]
   ￮ postulate f assumed
  
   ￫ info[I0000]
   ￮ constant a0' defined
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | untest = refl a0
     ^ term synthesized type
         Id A a0 a0
       but is being checked against type
         Id A a0 a1
       unequal head constants:
         a0
       does not equal
         a1
  
  [1]

Ap on let:

  $ agdarya -source-only -v pre.ny -e "a2' = refl ((y ↦ let id : A → A ≔ x ↦ x in id y) : A → A) a2" -e "test : Id (Id A a0 a1) a2 a2'" -e "test = refl a2"
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate a0 assumed
  
   ￫ info[I0001]
   ￮ postulate a1 assumed
  
   ￫ info[I0001]
   ￮ postulate a2 assumed
  
   ￫ info[I0001]
   ￮ postulate B assumed
  
   ￫ info[I0001]
   ￮ postulate b assumed
  
   ￫ info[I0001]
   ￮ postulate f assumed
  
   ￫ info[I0000]
   ￮ constant a2' defined
  
   ￫ info[I0000]
   ￮ constant test defined
  

Let affects typechecking:

  $ agdarya -source-only -v pre.ny -e "b' : B a0" -e "b' = let x ≔ a0 in f x b" -e "untest : B a0" -e "untest = ((x ↦ f x b) : A → B a0) a0"
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate a0 assumed
  
   ￫ info[I0001]
   ￮ postulate a1 assumed
  
   ￫ info[I0001]
   ￮ postulate a2 assumed
  
   ￫ info[I0001]
   ￮ postulate B assumed
  
   ￫ info[I0001]
   ￮ postulate b assumed
  
   ￫ info[I0001]
   ￮ postulate f assumed
  
   ￫ info[I0000]
   ￮ constant b' defined
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | untest = ((x ↦ f x b) : A → B a0) a0
     ^ term synthesized type
         B a0
       but is being checked against type
         B x
       unequal head terms:
         a0
       does not equal
         x
  
  [1]

Let can check in addition to synthesize:

  $ agdarya -source-only -v pre.ny -e "aconst : A → A" -e "aconst = let x ≔ a0 in y ↦ x"
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate a0 assumed
  
   ￫ info[I0001]
   ￮ postulate a1 assumed
  
   ￫ info[I0001]
   ￮ postulate a2 assumed
  
   ￫ info[I0001]
   ￮ postulate B assumed
  
   ￫ info[I0001]
   ￮ postulate b assumed
  
   ￫ info[I0001]
   ￮ postulate f assumed
  
   ￫ info[I0000]
   ￮ constant aconst defined
  

Let is allowed in case trees:

  $ agdarya -source-only -v pre.ny -e "atree : A → A" -e "atree = let x ≔ a0 in y ↦ y" -e "echo atree"
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate a0 assumed
  
   ￫ info[I0001]
   ￮ postulate a1 assumed
  
   ￫ info[I0001]
   ￮ postulate a2 assumed
  
   ￫ info[I0001]
   ￮ postulate B assumed
  
   ￫ info[I0001]
   ￮ postulate b assumed
  
   ￫ info[I0001]
   ￮ postulate f assumed
  
   ￫ info[I0000]
   ￮ constant atree defined
  
  atree
    : A → A
  

Let can contain case trees:

  $ cat >letcase.ny <<EOF
  > bool : Set
  > bool = data [ true | false ]
  > postulate u : bool
  > EOF

  $ agdarya -source-only -v letcase.ny -e 'not : bool -> bool' -e 'not x = let n : bool := match x [ true |-> false | false |-> true ] in n' -e 'echo not true' -e 'echo not false' -e 'echo not u'
   ￫ info[I0000]
   ￮ constant bool defined
  
   ￫ info[I0001]
   ￮ postulate u assumed
  
   ￫ info[I0000]
   ￮ constant not defined
  
  false
    : bool
  
  true
    : bool
  
  _let.F3.0.n{…}
    : bool
  

  $ agdarya -source-only -v letcase.ny -e 'not : bool -> bool' -e 'not x = let n : bool -> bool := y |-> match y [ true |-> false | false |-> true ] in n x' -e 'echo not true' -e 'echo not false' -e 'echo not u'
   ￫ info[I0000]
   ￮ constant bool defined
  
   ￫ info[I0001]
   ￮ postulate u assumed
  
   ￫ info[I0000]
   ￮ constant not defined
  
  false
    : bool
  
  true
    : bool
  
  _let.F3.0.n{…} u
    : bool
  

Synthesizing matches don't need to be annotated

  $ agdarya -source-only -v letcase.ny -e 'not : bool -> bool' -e 'not x = let n := match x [ true |-> (false : bool) | false |-> true ] in n' -e 'echo not true' -e 'echo not false' -e 'echo not u'
   ￫ info[I0000]
   ￮ constant bool defined
  
   ￫ info[I0001]
   ￮ postulate u assumed
  
   ￫ hint[E1101]
   ￭ command-line exec string
   1 | not x = let n := match x [ true |-> (false : bool) | false |-> true ] in n
     ^ match will not refine the goal or context (match in synthesizing position)
  
   ￫ info[I0000]
   ￮ constant not defined
  
  false
    : bool
  
  true
    : bool
  
  _let.F3.0.n{…}
    : bool
  

Either branch can synthesize:

  $ agdarya -source-only -v letcase.ny -e 'not : bool -> bool' -e 'not x = let n := match x [ true |-> false | false |-> (true : bool) ] in n' -e 'echo not true' -e 'echo not false' -e 'echo not u'
   ￫ info[I0000]
   ￮ constant bool defined
  
   ￫ info[I0001]
   ￮ postulate u assumed
  
   ￫ hint[E1101]
   ￭ command-line exec string
   1 | not x = let n := match x [ true |-> false | false |-> (true : bool) ] in n
     ^ match will not refine the goal or context (match in synthesizing position)
  
   ￫ info[I0000]
   ￮ constant not defined
  
  false
    : bool
  
  true
    : bool
  
  _let.F3.0.n{…}
    : bool
  

Let doesn't make a case tree unless it needs to:

  $ cat >letnocase.ny <<EOF
  > prod : (A B : Set) → Set
  > prod A B = sig (fst : A, snd : B)
  > foo : prod (Set -> Set) Set
  > foo = ( fst := X |-> X, snd := Set )
  > echo foo
  > foo' : prod (Set -> Set) Set
  > foo' = let z : prod (Set -> Set) Set := ( fst := X |-> X, snd := Set ) in z
  > echo foo'
  > EOF

  $ agdarya -v letnocase.ny
   ￫ info[I0000]
   ￮ constant prod defined
  
   ￫ info[I0000]
   ￮ constant foo defined
  
  foo
    : prod (Set → Set) Set
  
   ￫ info[I0000]
   ￮ constant foo' defined
  
  (fst ≔ λ X → X, snd ≔ Set)
    : prod (Set → Set) Set
  

Matches outside case trees can be implicitly wrapped in a let-binding:

  $ agdarya -source-only -v letcase.ny -e 'not : bool → bool' -e 'not b = ((x ↦ x) : bool → bool) (match b [ true ↦ false | false ↦ true ])' -e 'echo not true' -e 'echo not false' -e 'echo not u'
   ￫ info[I0000]
   ￮ constant bool defined
  
   ￫ info[I0001]
   ￮ postulate u assumed
  
   ￫ hint[H0403]
   ￭ command-line exec string
   1 | not b = ((x ↦ x) : bool → bool) (match b [ true ↦ false | false ↦ true ])
     ^ match encountered outside case tree, wrapping in implicit let-binding
  
   ￫ info[I0000]
   ￮ constant not defined
  
  false
    : bool
  
  true
    : bool
  
  _match.F3.0{…}
    : bool
  

Pattern-matching lambdas can be used in arbitrary places:

  $ agdarya -v - <<EOF
  > ℕ : Set
  > ℕ = data [ zero | suc (_:ℕ) ]
  > square : (f : ℕ → ℕ) → ℕ → ℕ
  > square f = x ↦ f (f x)
  > squaredec : ℕ → ℕ
  > squaredec = square (λ { zero → zero ; suc n → n })
  > echo squaredec 4
  > echo squaredec 1
  > postulate n : ℕ
  > echo squaredec n
  > EOF
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant square defined
  
   ￫ hint[H0403]
   ￭ stdin
   1 | squaredec = square (λ { zero → zero ; suc n → n })
     ^ match encountered outside case tree, wrapping in implicit let-binding
  
   ￫ info[I0000]
   ￮ constant squaredec defined
  
  2
    : ℕ
  
  0
    : ℕ
  
   ￫ info[I0001]
   ￮ postulate n assumed
  
  _match.F2.0{…}
    : ℕ
  

Matches in definitions of datatypes

  $ agdarya -v - <<EOF
  > Bool : Set
  > Bool = data [ true | false ]
  > Foo : (b : Bool) → Set
  > Foo b = data [ foo (_ : match b [ true ↦ Bool | false ↦ Bool ]) ]
  > f : Foo true
  > f = foo false
  > EOF
   ￫ info[I0000]
   ￮ constant Bool defined
  
   ￫ hint[H0403]
   ￭ stdin
   1 | Foo b = data [ foo (_ : match b [ true ↦ Bool | false ↦ Bool ]) ]
     ^ match encountered outside case tree, wrapping in implicit let-binding
  
   ￫ info[I0000]
   ￮ constant Foo defined
  
   ￫ info[I0000]
   ￮ constant f defined
  

Matches in non-toplevel definitions of datatype

  $ agdarya -v - <<EOF
  > Bool : Set
  > Bool = data [ true | false ]
  > prod : (A B : Set) → Set
  > prod A B = sig (fst : A, snd : B)
  > Foo : (b : Bool) → Set
  > Foo b = prod Bool (data [ foo (_ : match b [ true ↦ Bool | false ↦ Bool ]) ])
  > f : Foo true
  > f = (true, foo false)
  > EOF
   ￫ info[I0000]
   ￮ constant Bool defined
  
   ￫ info[I0000]
   ￮ constant prod defined
  
   ￫ hint[H0403]
   ￭ stdin
   1 | Foo b = prod Bool (data [ foo (_ : match b [ true ↦ Bool | false ↦ Bool ]) ])
     ^ data encountered outside case tree, wrapping in implicit let-binding
  
   ￫ hint[H0403]
   ￭ stdin
   1 | Foo b = prod Bool (data [ foo (_ : match b [ true ↦ Bool | false ↦ Bool ]) ])
     ^ match encountered outside case tree, wrapping in implicit let-binding
  
   ￫ info[I0000]
   ￮ constant Foo defined
  
   ￫ info[I0000]
   ￮ constant f defined
  
