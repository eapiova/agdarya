Testing notation commands

  $ agdarya -v -e 'postulate A:Set' -e 'postulate f:A->A->A' -e 'notation(0) x "&" y := f x y' -e 'ff : A → A → A' -e 'ff x y = x & y' -e 'postulate a : A' -e 'echo ff a a'
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate f assumed
  
   ￫ info[I0002]
   ￮ notation «_ & _» defined
  
   ￫ info[I0000]
   ￮ constant ff defined
  
   ￫ info[I0001]
   ￮ postulate a assumed
  
  a & a
    : A
  

  $ agdarya -v -e 'postulate A:Set' -e 'def(1) (x "&" y) : A -> A -> A := x y ↦ x' -e 'postulate a : A' -e 'synth a & a'
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ error[E0216]
   ￮ def syntax removed; use a top-level signature followed by one or more clauses
  
  [1]

  $ agdarya -e 'postulate A : Set' -e 'postulate _+_ : A → A → A' -e 'infixl 6 _+_' -e 'postulate a : A' -e 'echo a+a'
  a + a
    : A
  

  $ agdarya -e 'postulate A : Set' -e 'postulate -_ : A → A' -e 'infixr 8 -_' -e 'postulate a : A' -e 'echo - a'
  - a
    : A
  

  $ agdarya -e 'postulate A : Set' -e 'postulate if_then_else_ : A → A → A → A' -e 'infix 0 if_then_else_' -e 'postulate x : A' -e 'postulate y : A' -e 'postulate z : A' -e 'echo if x then y else z'
  if x then y else z
    : A
  

  $ agdarya -e 'postulate A : Set' -e 'section Nat :=' -e 'postulate _+_ : A → A → A' -e 'end' -e 'infixl 6 Nat._+_' -e 'postulate a : A' -e 'echo a+a'
  a + a
    : A
  

  $ agdarya -v -e 'postulate A : Set' -e 'data L : Set where { nil : L; _::_ : A → L → L }' -e 'infixr 5 _::_'
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0000]
   ￮ constant L defined
  
   ￫ info[I0002]
   ￮ notation «_ :: _» defined
  

  $ agdarya -e 'postulate A:Set' -e 'postulate f:A->A->A' -e 'notation(0) x "&" y.z := f x y.z'
   ￫ error[E0202]
   ￭ command-line exec string
   1 | notation(0) x "&" y.z := f x y.z
     ^ invalid local variable name: y.z
  
  [1]

  $ agdarya -e 'postulate A:Set' -e 'postulate f:A->A->A' -e 'notation(0) x "/" := f x x'
   ￫ error[E2207]
   ￮ notation variable 'x' used twice
  
  [1]


  $ agdarya -e 'postulate A:Set' -e 'postulate f:A->A->A' -e 'notation(0) x "&" y "#" z := f x y'
   ￫ error[E2206]
   ￮ unused notation variable: 'z'
  
  [1]


  $ agdarya -e 'postulate A:Set' -e 'postulate f:A->A->A' -e 'notation(0) x "/" := f x y'
   ￫ error[E2208]
   ￮ unbound variable(s) in notation definition: y
  
  [1]

  $ agdarya -e 'postulate A:Set' -e 'postulate f:A->A->A' -e 'notation(0) x "&" y "#" x := f x y'
   ￫ error[E2204]
   ￮ duplicate notation variable: 'x'
  
  [1]

  $ agdarya -e 'postulate A:Set' -e 'postulate f:A->A->A' -e 'notation "#" x "&" y "#" := f x y'

  $ agdarya -e 'postulate A:Set' -e 'postulate f:A->A->A' -e 'notation x "&" y "#" := f x y'
   ￫ error[E2203]
   ￮ notation command doesn't match pattern (tightness must be omitted only for outfix notations)
  
  [1]

  $ agdarya -e 'postulate A:Set' -e 'postulate f:A->A->A' -e 'notation(0) "#" x "&" y "#" := f x y'
   ￫ error[E2203]
   ￮ notation command doesn't match pattern (tightness must be omitted only for outfix notations)
  
  [1]

  $ agdarya -e 'postulate A:Set' -e 'postulate f:A->A->A' -e 'notation(0.5) x "&" y := f x y' -e 'ff : A → A → A' -e 'ff x y = x & y'


  $ agdarya -e 'postulate A:Set' -e 'postulate f:A->A->A' -e 'notation(0.1) x "&" y := f x y'
   ￫ error[E2200]
   ￭ command-line exec string
   1 | notation(0.1) x "&" y := f x y
     ^ invalid tightness: 0.1
  
  [1]

  $ agdarya -e 'postulate A:Set' -e 'postulate f:A->A->A' -e 'notation(0) x "&x" y := f x y'
   ￫ error[E2201]
   ￮ invalid notation symbol: &x
  
  [1]

  $ agdarya -e 'postulate A:Set' -e 'postulate f:A->A->A' -e 'notation(0) x "&" y := Set x y'
   ￫ error[E2205]
   ￮ invalid notation head: Set
  
  [1]

  $ agdarya -e 'postulate A:Set' -e 'postulate f:A' -e 'notation "&" := f'

  $ agdarya -e 'postulate A:Set' -e 'postulate f:A->A->A' -e 'notation(0) x "&" … "&" y := f x y'
   ￫ error[E0100]
   ￮ unimplemented: internal ellipses in notation
  
  [1]

  $ agdarya -e 'postulate A:Set' -e 'postulate f:A->A->A' -e 'notation(0) x "&" … y := f x y'
   ￫ error[E0100]
   ￮ unimplemented: internal ellipses in notation
  
  [1]

  $ agdarya -e 'postulate A:Set' -e 'postulate f:A->A->A' -e 'notation(0) … := f x y'
   ￫ error[E2202]
   ￮ invalid notation pattern: has no symbols
  
  [1]

  $ agdarya -e 'postulate A:Set' -e 'postulate f:A->A->A' -e 'notation(0) … x "&" y … := f x y'
   ￫ error[E2202]
   ￮ invalid notation pattern: can't be both right and left associative
  
  [1]

  $ agdarya -e 'postulate A:Set' -e 'postulate f:A->A' -e 'notation(0) x := f x'
   ￫ error[E2202]
   ￮ invalid notation pattern: has no symbols
  
  [1]

  $ agdarya -e 'postulate A:Set' -e 'postulate f:A->A->A' -e 'notation(0) "&" x y := f x y'
   ￫ error[E2202]
   ￮ invalid notation pattern: missing symbol between variables
  
  [1]

  $ agdarya -e 'postulate A : Set' -e 'postulate -_ : A → A' -e 'infixl 6 -_'
   ￫ error[E2202]
   ￭ command-line exec string
   1 | infixl 6 -_
     ^ invalid notation pattern: infixl requires an infix or postfix underscore name
  
  [1]

  $ agdarya -e 'postulate A : Set' -e 'postulate _! : A → A' -e 'infixr 6 _!'
   ￫ error[E2202]
   ￭ command-line exec string
   1 | infixr 6 _!
     ^ invalid notation pattern: infixr requires an infix or prefix underscore name
  
  [1]

  $ agdarya -e 'postulate A : Set' -e 'postulate foo_bar : A → A' -e 'infix 0 foo_bar'
   ￫ error[E2202]
   ￭ command-line exec string
   1 | infix 0 foo_bar
     ^ invalid notation pattern: outfix underscore names must use the notation command
  
  [1]

  $ agdarya -e 'postulate A : Set' -e 'postulate foo : A → A' -e 'infix 0 foo'
   ￫ error[E2202]
   ￭ command-line exec string
   1 | infix 0 foo
     ^ invalid notation pattern: fixity name must contain at least one underscore slot
  
  [1]

  $ agdarya -e 'postulate A : Set' -e 'postulate if__then_ : A → A → A' -e 'infix 0 if__then_'
   ￫ error[E2202]
   ￭ command-line exec string
   1 | infix 0 if__then_
     ^ invalid notation pattern: adjacent underscores are not allowed in fixity names
  
  [1]

  $ agdarya -v -e 'postulate A:Set' -e 'postulate f:A->A->A' -e 'notation(0) x "&" y := f x y' -e 'notation(0) x "%" y := f x y' -e 'ff : A → A → A' -e 'ff x y = x & y' -e 'ff2 : A → A → A' -e 'ff2 x y = x % y' -e 'postulate a : A' -e 'echo ff a a' -e 'echo ff2 a a'
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate f assumed
  
   ￫ info[I0002]
   ￮ notation «_ & _» defined
  
   ￫ warning[E2209]
   ￮ replacing printing notation for f (previous notation will still be parseable)
  
   ￫ info[I0002]
   ￮ notation «_ % _» defined
  
   ￫ info[I0000]
   ￮ constant ff defined
  
   ￫ info[I0000]
   ￮ constant ff2 defined
  
   ￫ info[I0001]
   ￮ postulate a assumed
  
  a % a
    : A
  
  a % a
    : A
  

This should be an error:

  $ agdarya -v -e 'postulate A:Set' -e 'postulate f:A->A->A' -e 'section nat :=' -e 'notation(0) x "+" y := f x y' -e 'end' -e 'postulate a:A' -e 'echo a + a'
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate f assumed
  
   ￫ info[I0007]
   ￮ section nat opened
  
   ￫ info[I0002]
   ￮ notation «_ + _» defined
  
   ￫ info[I0008]
   ￮ section nat closed
  
   ￫ info[I0001]
   ￮ postulate a assumed
  
   ￫ error[E0200]
   ￭ command-line exec string
   1 | echo a + a
     ^ parse error
  
  [1]

This should work:

  $ agdarya -v -e 'postulate A:Set' -e 'postulate f:A->A->A' -e 'section nat :=' -e 'notation(0) x "+" y := f x y' -e 'end' -e 'import nat | only notations' -e 'postulate a:A' -e 'echo a + a'
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate f assumed
  
   ￫ info[I0007]
   ￮ section nat opened
  
   ￫ info[I0002]
   ￮ notation «_ + _» defined
  
   ￫ info[I0008]
   ￮ section nat closed
  
   ￫ info[I0001]
   ￮ postulate a assumed
  
  a + a
    : A
  

Integrated notation definitions should export and import the same way:

  $ agdarya -v -e 'postulate A:Set' -e 'section nat :=' -e 'def(1) (x "+" y) : A -> A -> A := x y ↦ x' -e 'end' -e 'import nat | only notations' -e 'postulate a:A' -e 'synth a + a'
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ error[E0216]
   ￮ def syntax removed; use a top-level signature followed by one or more clauses
  
  [1]

As should this:

  $ agdarya -v -e 'postulate A:Set' -e 'postulate f:A->A->A' -e 'section nat :=' -e 'notation(0) x "+" y := f x y' -e 'end' -e 'import nat | seq (only notations, renaming notations notations.nat)' -e 'postulate a:A' -e 'echo a + a'
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate f assumed
  
   ￫ info[I0007]
   ￮ section nat opened
  
   ￫ info[I0002]
   ￮ notation «_ + _» defined
  
   ￫ info[I0008]
   ￮ section nat closed
  
   ￫ info[I0001]
   ￮ postulate a assumed
  
  a + a
    : A
  
