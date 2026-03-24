Import files

  $ cat >one.ny <<EOF
  > postulate A : Set
  > EOF

  $ cat >two.ny <<EOF
  > import "one"
  > postulate a0 : A
  > EOF

  $ agdarya -source-only -v two.ny
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/one.ny
  
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/one.ny (source)
  
   ￫ info[I0001]
   ￮ postulate a0 assumed
  

Command-line strings see namespaces from explicitly loaded files only

  $ agdarya -source-only -v two.ny -e 'postulate a1 : A'
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/one.ny
  
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/one.ny (source)
  
   ￫ info[I0001]
   ￮ postulate a0 assumed
  
   ￫ error[E0300]
   ￭ command-line exec string
   1 | postulate a1 : A
     ^ unbound variable: A
  
  [1]

  $ agdarya -source-only -v one.ny -e 'postulate a1 : A'
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate a1 assumed
  

Unless we explicitly export them:

  $ cat >etwo.ny <<EOF
  > export "one"
  > postulate a0 : A
  > EOF

  $ agdarya -source-only -v etwo.ny -e 'postulate a1 : A'
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/one.ny
  
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/one.ny (source)
  
   ￫ info[I0001]
   ￮ postulate a0 assumed
  
   ￫ info[I0001]
   ￮ postulate a1 assumed
  


Requiring a file multiple times

  $ cat >three.ny <<EOF
  > import "one"
  > postulate a1 : A
  > EOF

  $ cat >twothree.ny <<EOF
  > import "two"
  > import "three"
  > postulate a2 : Id A a0 a1
  > EOF

  $ agdarya -source-only -v twothree.ny
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/two.ny
  
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/one.ny
  
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/one.ny (source)
  
   ￫ info[I0001]
   ￮ postulate a0 assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/two.ny (source)
  
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/three.ny
  
   ￫ info[I0001]
   ￮ postulate a1 assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/three.ny (source)
  
   ￫ error[E0300]
   ￭ $TESTCASE_ROOT/twothree.ny
   1 | postulate a2 : Id A a0 a1
     ^ unbound variable: A
  
  [1]

  $ cat >four.ny <<EOF
  > import "one"
  > import "two"
  > import "three"
  > postulate a2 : Id A a0 a1
  > EOF

  $ agdarya -source-only -v four.ny
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/one.ny
  
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/one.ny (source)
  
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/two.ny
  
   ￫ info[I0001]
   ￮ postulate a0 assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/two.ny (source)
  
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/three.ny
  
   ￫ info[I0001]
   ￮ postulate a1 assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/three.ny (source)
  
   ￫ info[I0001]
   ￮ postulate a2 assumed
  

Circular dependency

  $ cat >foo.ny <<EOF
  > import "bar"
  > EOF

  $ cat >bar.ny <<EOF
  > import "foo"
  > EOF

  $ agdarya -source-only foo.ny
   ￫ error[E2300]
   ￮ circular imports:
     $TESTCASE_ROOT/foo.ny
       imports $TESTCASE_ROOT/bar.ny
       imports $TESTCASE_ROOT/foo.ny
  
  [1]

Import is relative to the file's directory

  $ mkdir subdir

  $ cat >subdir/one.ny <<EOF
  > postulate A:Set
  > EOF

  $ cat >subdir/two.ny <<EOF
  > import "one"
  > postulate a : A
  > EOF

  $ agdarya -source-only -v -e 'import "subdir/two"'
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/subdir/two.ny
  
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/subdir/one.ny
  
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/subdir/one.ny (source)
  
   ￫ info[I0001]
   ￮ postulate a assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/subdir/two.ny (source)
  

A file isn't loaded twice even if referred to in different ways

  $ agdarya -source-only -v subdir/one.ny -e 'import "subdir/two"'
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/subdir/two.ny
  
   ￫ info[I0001]
   ￮ postulate a assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/subdir/two.ny (source)
  

Notations are used from explicitly imported files, but not transitively.

  $ cat >n1.ny <<EOF
  > postulate A:Set
  > postulate f : A -> A -> A
  > postulate a:A
  > EOF

  $ cat >n2.ny <<EOF
  > import "n1"
  > notation(0) x "&" y := f x y
  > EOF

  $ cat >n3.ny <<EOF
  > import "n1"
  > import "n2"
  > notation(0) x "%" y := f x y
  > EOF

  $ agdarya -source-only n1.ny n3.ny -e 'echo a % a'
   ￫ warning[E2209]
   ￮ replacing printing notation for f (previous notation will still be parseable)
  
  a % a
    : A
  

  $ agdarya -source-only n1.ny n3.ny -e 'echo a & a'
   ￫ warning[E2209]
   ￮ replacing printing notation for f (previous notation will still be parseable)
  
   ￫ error[E0200]
   ￭ command-line exec string
   1 | echo a & a
     ^ parse error
  
  [1]

  $ cat >n4.ny <<EOF
  > import "n1"
  > import "n3"
  > echo a % a
  > EOF

  $ agdarya -source-only n4.ny
   ￫ warning[E2209]
   ￮ replacing printing notation for f (previous notation will still be parseable)
  
  a % a
    : A
  

Quitting in imports quits only that file

  $ cat >qone.ny <<EOF
  > postulate A : Set
  > quit
  > postulate B : Set
  > EOF

  $ cat >qtwo.ny <<EOF
  > import "qone"
  > postulate a0 : A
  > EOF

  $ agdarya -source-only -v qtwo.ny
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/qone.ny
  
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0200]
   ￮ execution of $TESTCASE_ROOT/qone.ny terminated by quit
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/qone.ny (source)
  
   ￫ info[I0001]
   ￮ postulate a0 assumed
  

Definitions are linked

  $ cat >lone.ny <<EOF
  > data Nat : Set where { zero : Nat; suc : Nat → Nat }
  > EOF

  $ cat >ltwo.ny <<EOF
  > import "lone"
  > foo : (n : Nat) → Set
  > foo n = match n [ zero ↦ Nat | suc n ↦ Nat ]
  > EOF

  $ agdarya -v lone.ny
   ￫ info[I0000]
   ￮ constant Nat defined
  

  $ agdarya -v ltwo.ny
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/lone.ny (compiled)
  
   ￫ info[I0000]
   ￮ constant foo defined
  

Undoing and redoing an import

  $ cat >undoimport.ny <<EOF
  > import "one"
  > undo 1
  > import "one"
  > postulate a:A
  > EOF

  $ agdarya -fake-interact undoimport.ny
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/one.ny (compiled)
  
   ￫ info[I0006]
   ￮ 1 command undone
  
   ￫ info[I0001]
   ￮ postulate a assumed
  
Importing after creating a hole

  $ rm one.nyo

  $ cat >importhole.ny <<EOF
  > Z : Set
  > Z = ?
  > import "one"
  > W : Set
  > W = Z
  > EOF

  $ agdarya -v importhole.ny
   ￫ info[I0000]
   ￮ constant Z defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     ----------------------------------------------------------------------
     Set
  
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/one.ny
  
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/one.ny (source)
  
   ￫ info[I0000]
   ￮ constant W defined
  
   ￫ error[E3002]
   ￮ file importhole.ny contains open holes
  
  [1]
