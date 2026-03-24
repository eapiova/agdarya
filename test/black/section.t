  $ cat >err.ny <<EOF
  > postulate A : Set
  > section B :=
  >   postulate f : A -> Set
  > end
  > echo B.f
  > echo f
  > EOF

  $ agdarya -v err.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0007]
   ￮ section B opened
  
   ￫ info[I0001]
   ￮ postulate f assumed
  
   ￫ info[I0008]
   ￮ section B closed
  
  B.f
    : A → Set
  
   ￫ error[E0300]
   ￭ $TESTCASE_ROOT/err.ny
   1 | echo f
     ^ unbound variable: f
  
  [1]

  $ agdarya -v -e 'end'
   ￫ error[E2600]
   ￮ no section here to end
  
  [1]

  $ cat >section.ny <<EOF
  > postulate A:Set
  > section one :=
  >   postulate B:Set
  >   section two :=
  >     postulate f : A -> B
  >   end
  >   postulate a:A
  >   b : B
  >   b = two.f a
  >   section three :=
  >     postulate C : B -> Set
  >     postulate c : C b
  >   end
  >   postulate g : (y:B) → three.C y
  > end
  > postulate gc : Id (one.three.C one.b) one.three.c (one.g one.b)
  > import one.three
  > postulate gc' : Id (C one.b) c (one.g one.b)
  > EOF

  $ agdarya -v section.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0007]
   ￮ section one opened
  
   ￫ info[I0001]
   ￮ postulate B assumed
  
   ￫ info[I0007]
   ￮ section two opened
  
   ￫ info[I0001]
   ￮ postulate f assumed
  
   ￫ info[I0008]
   ￮ section two closed
  
   ￫ info[I0001]
   ￮ postulate a assumed
  
   ￫ info[I0000]
   ￮ constant b defined
  
   ￫ info[I0007]
   ￮ section three opened
  
   ￫ info[I0001]
   ￮ postulate C assumed
  
   ￫ info[I0001]
   ￮ postulate c assumed
  
   ￫ info[I0008]
   ￮ section three closed
  
   ￫ info[I0001]
   ￮ postulate g assumed
  
   ￫ info[I0008]
   ￮ section one closed
  
   ￫ info[I0001]
   ￮ postulate gc assumed
  
   ￫ info[I0001]
   ￮ postulate gc' assumed
  

  $ agdarya -e 'section notations := '
   ￫ error[E2601]
   ￮ invalid section name: notations
  
  [1]

  $ agdarya -e 'section foo.notations := '
   ￫ error[E2601]
   ￮ invalid section name: foo.notations
  
  [1]

  $ agdarya -e 'section notations.foo := '
   ￫ error[E2601]
   ￮ invalid section name: notations.foo
  
  [1]
