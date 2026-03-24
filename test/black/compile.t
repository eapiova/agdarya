Import compiled files

  $ cat >one.ny <<EOF
  > postulate A : Set
  > EOF

  $ cat >two.ny <<EOF
  > import "one"
  > postulate a0 : A
  > EOF

  $ agdarya one.ny

  $ agdarya -v two.ny
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/one.ny (compiled)
  
   ￫ info[I0001]
   ￮ postulate a0 assumed
  

Modified files are recompiled

  $ touch one.ny

  $ agdarya -v two.ny
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/one.ny
  
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/one.ny (source)
  
   ￫ info[I0001]
   ￮ postulate a0 assumed
  

Files are recompiled if the flags change

  $ agdarya -dtt -v two.ny
   ￫ warning[W2303]
   ￮ file '$TESTCASE_ROOT/one.ny' was compiled with incompatible flags -arity 2 -direction e,refl,Id,ap -internal, recompiling
  
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/one.ny
  
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/one.ny (source)
  
   ￫ info[I0001]
   ￮ postulate a0 assumed
  

  $ agdarya two.ny
   ￫ warning[W2303]
   ￮ file '$TESTCASE_ROOT/one.ny' was compiled with incompatible flags -parametric -arity 1 -direction d -external, recompiling
  

Requiring a file multiple times

  $ cat >three.ny <<EOF
  > import "one"
  > postulate a1 : A
  > EOF

  $ agdarya three.ny

  $ cat >four.ny <<EOF
  > import "one"
  > import "two"
  > import "three"
  > postulate a2 : Id A a0 a1
  > EOF

  $ agdarya -v four.ny
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/one.ny (compiled)
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/two.ny (compiled)
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/three.ny (compiled)
  
   ￫ info[I0001]
   ￮ postulate a2 assumed
  

Files are recompiled if their dependencies need to be

  $ touch one.ny

  $ agdarya -v four.ny
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

  $ agdarya foo.ny
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

  $ agdarya subdir/one.ny

  $ agdarya subdir/two.ny

  $ agdarya -v -e 'import "subdir/two"'
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/subdir/one.ny (compiled)
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/subdir/two.ny (compiled)
  

A file isn't loaded twice even if referred to in different ways

  $ agdarya -v -e 'import "subdir/one"' -e 'import "subdir/two"'
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/subdir/one.ny (compiled)
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/subdir/two.ny (compiled)
  

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

  $ agdarya n1.ny

  $ agdarya n2.ny

  $ agdarya n1.ny n3.ny -e 'echo a % a'
   ￫ warning[E2209]
   ￮ replacing printing notation for f (previous notation will still be parseable)
  
  a % a
    : A
  

  $ agdarya n1.ny n3.ny -e 'echo a & a'
   ￫ warning[E2209]
   ￮ replacing printing notation for f (previous notation will still be parseable)
  
   ￫ error[E0200]
   ￭ command-line exec string
   1 | echo a & a
     ^ parse error
  
  [1]

Quitting in imports quits only that file

  $ cat >qone.ny <<EOF
  > postulate A : Set
  > quit
  > postulate B : Set
  > EOF

  $ agdarya qone.ny

  $ cat >qtwo.ny <<EOF
  > import "qone"
  > postulate a0 : A
  > EOF

  $ agdarya -v qtwo.ny
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/qone.ny (compiled)
  
   ￫ info[I0001]
   ￮ postulate a0 assumed
  
Dimensions work in files loaded from source

  $ cat >dim.ny <<EOF
  > postulate A:Set
  > postulate a0:A
  > postulate a1:A
  > postulate a2 : Id A a0 a1
  > EOF

  $ agdarya dim.ny

  $ agdarya -v -e 'import "dim" echo a2'
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/dim.ny (compiled)
  
  a2
    : Id A a0 a1
  
Echos are not re-executed in compiled files

  $ cat >echo.ny <<EOF
  > postulate A:Set
  > echo A
  > EOF

  $ agdarya -e 'import "echo"'
  A
    : Set
  

  $ agdarya -e 'import "echo"'
   ￫ warning[W2400]
   ￮ not re-executing echo/synth/show commands when loading compiled file $TESTCASE_ROOT/echo.nyo
  
