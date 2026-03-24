  $ cat >one.ny <<EOF
  > A : Set
  > A = Set
  > EOF

  $ cat >two.ny <<EOF
  > import "one"
  > A : Set
  > A = sig ()
  > EOF

  $ agdarya -v two.ny
   ￫ info[I0003]
   ￮ loading file: $TESTCASE_ROOT/one.ny
  
   ￫ info[I0000]
   ￮ constant A defined
  
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/one.ny (source)
  
   ￫ info[I0000]
   ￮ constant A defined
  

  $ cat >three.ny <<EOF
  > export "one"
  > A : Set
  > A = sig ()
  > EOF

  $ agdarya -v three.ny
   ￫ info[I0004]
   ￮ file loaded: $TESTCASE_ROOT/one.ny (compiled)
  
   ￫ warning[E2100]
   ￭ $TESTCASE_ROOT/three.ny
   1 | A : Set
     ^ redefining constant: A
   ￭ $TESTCASE_ROOT/one.ny
   1 | A : Set
     ^ previous definition
  
   ￫ info[I0000]
   ￮ constant A defined
  

  $ cat >oneone.ny <<EOF
  > A : Set
  > A = Set
  > A : Set
  > A = sig ()
  > EOF

  $ agdarya oneone.ny
   ￫ error[E2202]
   ￭ $TESTCASE_ROOT/oneone.ny
   1 | A : Set
     ^ invalid notation pattern: duplicate type signature in definition group
  
  [1]

  $ cat >onesect.ny <<EOF
  > A : Set
  > A = Set
  > section foo ≔
  >   A : Set
  >   A = sig ()
  >   data B : Set where { }
  >   data C : Set where { one : C }
  > end
  > import foo
  > B : Set
  > B = codata []
  > export foo
  > C : Set
  > C = sig ( one : Set )
  > EOF

  $ agdarya -v onesect.ny
   ￫ info[I0000]
   ￮ constant A defined
  
   ￫ info[I0007]
   ￮ section foo opened
  
   ￫ info[I0000]
   ￮ constant A defined
  
   ￫ info[I0000]
   ￮ constant B defined
  
   ￫ info[I0000]
   ￮ constant C defined
  
   ￫ info[I0008]
   ￮ section foo closed
  
   ￫ info[I0000]
   ￮ constant B defined
  
   ￫ warning[E2100]
   ￭ $TESTCASE_ROOT/onesect.ny
   1 | C : Set
     ^ redefining constant: C
   ￭ $TESTCASE_ROOT/onesect.ny
   1 |   data C : Set where { one : C }
     ^ previous definition
  
   ￫ info[I0000]
   ￮ constant C defined
  
