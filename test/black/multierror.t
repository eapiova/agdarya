  $ cat >multierr.ny <<EOF
  > postulate A:Set
  > postulate B:Set
  > postulate C:Set
  > postulate a:A
  > record prod (X Y : Set) : Set where { field fst : X ; snd : Y }
  > foo : prod B C
  > foo = (a,a)
  > EOF

  $ agdarya -v multierr.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate B assumed
  
   ￫ info[I0001]
   ￮ postulate C assumed
  
   ￫ info[I0001]
   ￮ postulate a assumed
  
   ￫ info[I0000]
   ￮ constant prod defined
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   1 | foo = (a,a)
     ^ term synthesized type
         A
       but is being checked against type
         B
       unequal head constants:
         A
       does not equal
         B
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   1 | foo = (a,a)
     ^ term synthesized type
         A
       but is being checked against type
         C
       unequal head constants:
         A
       does not equal
         C
  
  [1]

  $ cat >multierr.ny <<EOF
  > postulate A:Set
  > postulate B:Set
  > postulate C:Set
  > postulate a:A
  > postulate c:C
  > record prod (X Y : Set) : Set where { field fst : X ; snd : Y }
  > foo : prod B C
  > foo = (a,c)
  > EOF

  $ agdarya -v multierr.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate B assumed
  
   ￫ info[I0001]
   ￮ postulate C assumed
  
   ￫ info[I0001]
   ￮ postulate a assumed
  
   ￫ info[I0001]
   ￮ postulate c assumed
  
   ￫ info[I0000]
   ￮ constant prod defined
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   1 | foo = (a,c)
     ^ term synthesized type
         A
       but is being checked against type
         B
       unequal head constants:
         A
       does not equal
         B
  
  [1]


  $ cat >multierr.ny <<EOF
  > postulate A:Set
  > postulate B:Set
  > postulate C:Set
  > postulate a:A
  > record prod (X Y : Set) : Set where { field fst : X ; snd : Y }
  > foo : prod (prod B C) (prod C B)
  > foo = ((a,a),(a,a))
  > EOF

  $ agdarya -v multierr.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate B assumed
  
   ￫ info[I0001]
   ￮ postulate C assumed
  
   ￫ info[I0001]
   ￮ postulate a assumed
  
   ￫ info[I0000]
   ￮ constant prod defined
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   1 | foo = ((a,a),(a,a))
     ^ term synthesized type
         A
       but is being checked against type
         B
       unequal head constants:
         A
       does not equal
         B
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   1 | foo = ((a,a),(a,a))
     ^ term synthesized type
         A
       but is being checked against type
         C
       unequal head constants:
         A
       does not equal
         C
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   1 | foo = ((a,a),(a,a))
     ^ term synthesized type
         A
       but is being checked against type
         C
       unequal head constants:
         A
       does not equal
         C
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   1 | foo = ((a,a),(a,a))
     ^ term synthesized type
         A
       but is being checked against type
         B
       unequal head constants:
         A
       does not equal
         B
  
  [1]

  $ cat >multierr.ny <<EOF
  > postulate A:Set
  > postulate B:Set
  > postulate P:B->Set
  > postulate a:A
  > record Sigma (X : Set) (Y : X -> Set) : Set where { field fst : X ; snd : Y fst }
  > foo : Sigma B P
  > foo = (a,a)
  > EOF

  $ agdarya -v multierr.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate B assumed
  
   ￫ info[I0001]
   ￮ postulate P assumed
  
   ￫ info[I0001]
   ￮ postulate a assumed
  
   ￫ info[I0000]
   ￮ constant Sigma defined
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   1 | foo = (a,a)
     ^ term synthesized type
         A
       but is being checked against type
         B
       unequal head constants:
         A
       does not equal
         B
  
  [1]

  $ cat >multierr.ny <<EOF
  > postulate A:Set
  > postulate B:Set
  > postulate a:A
  > data bool : Set where { true : bool ; false : bool }
  > P : bool -> Set
  > P = λ { true → A ; false → B }
  > record Sigma (X : Set) (Y : X -> Set) : Set where { field fst : X ; snd : Y fst }
  > foo : Sigma bool P
  > foo = (a, a)
  > EOF

  $ agdarya -v multierr.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate B assumed
  
   ￫ info[I0001]
   ￮ postulate a assumed
  
   ￫ info[I0000]
   ￮ constant bool defined
  
   ￫ info[I0000]
   ￮ constant P defined
  
   ￫ info[I0000]
   ￮ constant Sigma defined
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   1 | foo = (a, a)
     ^ term synthesized type
         A
       but is being checked against type
         bool
       unequal head constants:
         A
       does not equal
         bool
  
  [1]

Even trivial dependency blocks going on, as long as there is the potential for dependency.  Avoiding this would probably involve more laziness in function arguments.

  $ cat >multierr.ny <<EOF
  > postulate A:Set
  > postulate B:Set
  > postulate a:A
  > record Sigma (X : Set) (Y : X -> Set) : Set where { field fst : X ; snd : Y fst }
  > foo : Sigma B (λ _ → B)
  > foo = (a, a)
  > EOF

  $ agdarya -v multierr.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate B assumed
  
   ￫ info[I0001]
   ￮ postulate a assumed
  
   ￫ info[I0000]
   ￮ constant Sigma defined
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   1 | foo = (a, a)
     ^ term synthesized type
         A
       but is being checked against type
         B
       unequal head constants:
         A
       does not equal
         B
  
  [1]


  $ cat >multierr.ny <<EOF
  > postulate A:Set
  > postulate B:Set
  > postulate a:A
  > streamB : Set
  > streamB = codata [ head x : B | tail x : streamB ]
  > foo : streamB
  > foo = record { head = a ; tail = a }
  > EOF

  $ agdarya -v multierr.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate B assumed
  
   ￫ info[I0001]
   ￮ postulate a assumed
  
   ￫ info[I0000]
   ￮ constant streamB defined
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   1 | foo = record { head = a ; tail = a }
     ^ term synthesized type
         A
       but is being checked against type
         B
       unequal head constants:
         A
       does not equal
         B
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   1 | foo = record { head = a ; tail = a }
     ^ term synthesized type
         A
       but is being checked against type
         streamB
       unequal head constants:
         A
       does not equal
         streamB
  
  [1]

  $ cat >multierr.ny <<EOF
  > postulate A:Set
  > postulate B:Set
  > postulate a:A
  > streamB : Set
  > streamB = codata [ head x : B | tail x : streamB ]
  > foo : B
  > foo = let x : streamB = record { head = a ; tail = a } in x head
  > EOF

  $ agdarya -v multierr.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate B assumed
  
   ￫ info[I0001]
   ￮ postulate a assumed
  
   ￫ info[I0000]
   ￮ constant streamB defined
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   1 | foo = let x : streamB = record { head = a ; tail = a } in x head
     ^ term synthesized type
         A
       but is being checked against type
         B
       unequal head constants:
         A
       does not equal
         B
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   1 | foo = let x : streamB = record { head = a ; tail = a } in x head
     ^ term synthesized type
         A
       but is being checked against type
         streamB
       unequal head constants:
         A
       does not equal
         streamB
  
  [1]

  $ cat >multierr.ny <<EOF
  > postulate A:Set
  > postulate B:Set
  > postulate a:A
  > data bool : Set where { true : bool ; false : bool }
  > foo : bool -> B
  > foo x = match x [ true ↦ a | false ↦ a ]
  > EOF

  $ agdarya -v multierr.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate B assumed
  
   ￫ info[I0001]
   ￮ postulate a assumed
  
   ￫ info[I0000]
   ￮ constant bool defined
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   1 | foo x = match x [ true ↦ a | false ↦ a ]
     ^ term synthesized type
         A
       but is being checked against type
         B
       unequal head constants:
         A
       does not equal
         B
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   1 | foo x = match x [ true ↦ a | false ↦ a ]
     ^ term synthesized type
         A
       but is being checked against type
         B
       unequal head constants:
         A
       does not equal
         B
  
  [1]

  $ cat >multierr.ny <<EOF
  > postulate A:Set
  > postulate a:A
  > data foo : Set where { true : a → foo ; false : a → foo }
  > EOF

  $ agdarya -v multierr.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate a assumed
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   1 | data foo : Set where { true : a → foo ; false : a → foo }
     ^ term synthesized type
         A
       but is being checked against type
         Set
       unequal head terms:
         A
       does not equal
         Set
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   1 | data foo : Set where { true : a → foo ; false : a → foo }
     ^ term synthesized type
         A
       but is being checked against type
         Set
       unequal head terms:
         A
       does not equal
         Set
  
  [1]

  $ cat >multierr.ny <<EOF
  > postulate A:Set
  > postulate a:A
  > record foo : Set where { field fst : a ; snd : a }
  > EOF

  $ agdarya -v multierr.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate a assumed
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   1 | record foo : Set where { field fst : a ; snd : a }
     ^ term synthesized type
         A
       but is being checked against type
         Set
       unequal head terms:
         A
       does not equal
         Set
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   1 | record foo : Set where { field fst : a ; snd : a }
     ^ term synthesized type
         A
       but is being checked against type
         Set
       unequal head terms:
         A
       does not equal
         Set
  
  [1]

  $ cat >multierr.ny <<EOF
  > postulate A:Set
  > postulate a:A
  > postulate B : A -> Set
  > record foo : Set where { field fst : a ; snd : B fst }
  > EOF

  $ agdarya -v multierr.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate a assumed
  
   ￫ info[I0001]
   ￮ postulate B assumed
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   1 | record foo : Set where { field fst : a ; snd : B fst }
     ^ term synthesized type
         A
       but is being checked against type
         Set
       unequal head terms:
         A
       does not equal
         Set
  
  [1]

  $ cat >multierr.ny <<EOF
  > postulate A:Set
  > postulate a:A
  > foo : Set
  > foo = codata [ fst x : a | snd x : a ]
  > EOF

  $ agdarya -v multierr.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate a assumed
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   1 | foo = codata [ fst x : a | snd x : a ]
     ^ term synthesized type
         A
       but is being checked against type
         Set
       unequal head terms:
         A
       does not equal
         Set
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   1 | foo = codata [ fst x : a | snd x : a ]
     ^ term synthesized type
         A
       but is being checked against type
         Set
       unequal head terms:
         A
       does not equal
         Set
  
  [1]

  $ cat >multierr.ny <<EOF
  > data Nat : Set where { zero : Nat ; suc : Nat → Nat }
  > postulate f : Nat -> Nat
  > pred : Nat -> Nat
  > pred x = match x [ zero |-> Nat | suc y |-> f (pred y) ]
  > EOF

  $ agdarya -v multierr.ny
   ￫ info[I0000]
   ￮ constant Nat defined
  
   ￫ info[I0001]
   ￮ postulate f assumed
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   1 | pred x = match x [ zero |-> Nat | suc y |-> f (pred y) ]
     ^ term synthesized type
         Set
       but is being checked against type
         Nat
       unequal head terms:
         Set
       does not equal
         Nat
  
  [1]

  $ cat >multierr.ny <<EOF
  > data color : Set where { red : color ; green : color ; blue : color }
  > postulate A:Set
  > postulate a:A
  > foo x = match x [ red ↦ (a,a a) | green ↦ a | blue ↦ A ]
  > EOF

  $ agdarya -v multierr.ny
   ￫ info[I0000]
   ￮ constant color defined
  
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate a assumed
  
   ￫ error[E0400]
   ￮ non-synthesizing term in synthesizing position (body of def without specified type)
  
  [1]

  $ cat >multierr.ny <<EOF
  > postulate A:Set
  > postulate a:A
  > echo a a : a
  > EOF

  $ agdarya -v multierr.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate a assumed
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   1 | echo a a : a
     ^ term synthesized type
         A
       but is being checked against type
         Set
       unequal head terms:
         A
       does not equal
         Set
  
   ￫ error[E0701]
   ￭ $TESTCASE_ROOT/multierr.ny
   1 | echo a a : a
     ^ attempt to apply/instantiate
         a
       of type
         A
       which is not a function-type or universe
  
  [1]

  $ cat >multierr.ny <<EOF
  > postulate A:Set
  > postulate a:A
  > foo : A
  > foo = (a, a) : a
  > EOF

  $ agdarya -v multierr.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate a assumed
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/multierr.ny
   1 | foo = (a, a) : a
     ^ term synthesized type
         A
       but is being checked against type
         Set
       unequal head terms:
         A
       does not equal
         Set
  
   ￫ error[E0900]
   ￭ $TESTCASE_ROOT/multierr.ny
   1 | foo = (a, a) : a
     ^ checking tuple against non-record type A
  
  [1]
