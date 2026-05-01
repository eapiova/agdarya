  $ cat >err.ny <<EOF
  > postulate A : Set
  > module B where {
  >   postulate f : A -> Set
  > }
  > echo B.f
  > echo f
  > EOF

  $ agdarya -v err.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate f assumed
  
  B.f
    : A → Set
  
   ￫ error[E0300]
   ￭ $TESTCASE_ROOT/err.ny
   1 | echo f
     ^ unbound variable: f
  
  [1]

  $ agdarya -v -e 'end'
   ￫ error[E0200]
   ￮ parse error
  
  [1]

  $ cat >section.ny <<EOF
  > postulate A:Set
  > module one where {
  >   postulate B:Set;
  >   module two where {
  >     postulate f : A -> B
  >   };
  >   postulate a:A;
  >   b : B;
  >   b = two.f a;
  >   module three where {
  >     postulate C : B -> Set;
  >     postulate c : C b
  >   };
  >   postulate g : (y:B) → three.C y
  > }
  > postulate gc : Id (one.three.C one.b) one.three.c (one.g one.b)
  > open one.three
  > postulate gc' : Id (C one.b) c (one.g one.b)
  > EOF

  $ agdarya -v section.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate B assumed
  
   ￫ info[I0001]
   ￮ postulate f assumed
  
   ￫ info[I0001]
   ￮ postulate a assumed
  
   ￫ info[I0000]
   ￮ constant b defined
  
   ￫ info[I0001]
   ￮ postulate C assumed
  
   ￫ info[I0001]
   ￮ postulate c assumed
  
   ￫ info[I0001]
   ￮ postulate g assumed
  
   ￫ info[I0001]
   ￮ postulate gc assumed
  
   ￫ info[I0001]
   ￮ postulate gc' assumed
  

  $ agdarya -e 'module notations where { postulate A : Set }'
   ￫ error[E2601]
   ￮ invalid section name: notations
  
  [1]

  $ agdarya -e 'module foo.notations where { postulate A : Set }'
   ￫ error[E2601]
   ￮ invalid section name: foo.notations
  
  [1]

  $ agdarya -e 'module notations.foo where { postulate A : Set }'
   ￫ error[E2601]
   ￮ invalid section name: notations.foo
  
  [1]
