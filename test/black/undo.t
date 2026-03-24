Undo single command

  $ cat >undo.ny <<EOF
  > postulate A:Set
  > postulate a:A
  > echo a
  > undo 1
  > echo a
  > EOF

  $ agdarya -v -fake-interact undo.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate a assumed
  
  a
    : A
  
   ￫ info[I0006]
   ￮ 1 command undone
  
   ￫ error[E0300]
   ￭ undo.ny
   1 | echo a
     ^ unbound variable: a
  

Undo multiple commands

  $ cat >undo2.ny <<EOF
  > postulate A:Set
  > postulate a:A
  > postulate b:A
  > echo a
  > undo 2
  > echo a
  > EOF

  $ agdarya -v -fake-interact undo2.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate a assumed
  
   ￫ info[I0001]
   ￮ postulate b assumed
  
  a
    : A
  
   ￫ info[I0006]
   ￮ 2 commands undone
  
   ￫ error[E0300]
   ￭ undo2.ny
   1 | echo a
     ^ unbound variable: a
  

Undo nothing

  $ cat >no-undo.ny <<EOF
  > undo 1
  > EOF

  $ agdarya -v -fake-interact no-undo.ny
   ￫ error[E2500]
   ￮ not enough commands to undo
  

Undo notations

  $ cat >undo-notn.ny <<EOF
  > postulate A:Set
  > postulate a:A
  > postulate f : A -> A -> A
  > notation(1) x "+" y := f x y
  > echo a + a
  > undo 1
  > echo a + a
  > EOF

  $ agdarya -v -fake-interact undo-notn.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate a assumed
  
   ￫ info[I0001]
   ￮ postulate f assumed
  
   ￫ info[I0002]
   ￮ notation «_ + _» defined
  
  a + a
    : A
  
   ￫ info[I0006]
   ￮ 1 command undone
  
   ￫ error[E0200]
   ￭ undo-notn.ny
   1 | echo a + a
     ^ parse error
  
