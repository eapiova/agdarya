Recursive let-bindings

  $ cat >letrec.ny <<EOF
  > ℕ : Set
  > ℕ = data [ zero | suc (_:ℕ) ]
  > times : (x y : ℕ) → ℕ
  > times x y =
  >   let rec plus : ℕ → ℕ → ℕ = λ m n → match n [ zero ↦ m | suc p ↦ suc (plus m p) ] in
  >   match y [ zero ↦ zero | suc z ↦ plus (times x z) x ]
  > EOF

  $ agdarya -v letrec.ny -e 'echo times 3 4' -e 'echo times'
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant times defined
  
  12
    : ℕ
  
  times
    : (x : ℕ) (y : ℕ) → ℕ
  
In kinetic terms

  $ cat >letrec-k.ny <<EOF
  > ℕ : Set
  > ℕ = data [ zero | suc (_:ℕ) ]
  > idℕ : ℕ → ℕ
  > idℕ = λ x → x
  > times : (x y : ℕ) → ℕ
  > times x y = idℕ
  >   (let rec plus : ℕ → ℕ → ℕ = λ m n → match n [ zero ↦ m | suc p ↦ suc (plus m p) ] in
  >    match y [ zero ↦ zero | suc z ↦ plus (times x z) x ])
  > EOF

  $ agdarya -v letrec-k.ny -e 'echo times 3 4' -e 'echo times'
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant idℕ defined
  
   ￫ hint[H0403]
   ￭ $TESTCASE_ROOT/letrec-k.ny
   3 |    match y [ zero ↦ zero | suc z ↦ plus (times x z) x ])
     ^ match encountered outside case tree, wrapping in implicit let-binding
  
   ￫ info[I0000]
   ￮ constant times defined
  
  12
    : ℕ
  
  times
    : (x : ℕ) (y : ℕ) → ℕ
  
Local recursive datatypes

  $ cat >letrec-ty.ny <<EOF
  > adder : Set
  > adder = sig (t : Set, one : t, plus : t → t → t)
  > ℕadder : adder
  > ℕadder =
  >   let rec ℕ : Set = data [ zero | suc (_ : ℕ) ] in
  >   let rec plus : ℕ → ℕ → ℕ = λ x y → match y [ zero ↦ x | suc y ↦ suc (plus x y) ] in
  >   (ℕ, suc zero, plus)
  > EOF

  $ agdarya -v letrec-ty.ny -e "echo ℕadder plus (ℕadder one) (ℕadder one)"
   ￫ info[I0000]
   ￮ constant adder defined
  
   ￫ info[I0000]
   ￮ constant ℕadder defined
  
  2
    : _letrec.F2.0.ℕ{…}
  

Local mutually recursive definitions

  $ cat >even-odd.ny <<EOF
  > bool : Set
  > bool = data [ false | true ]
  > ℕ : Set
  > ℕ = data [ zero | suc (_:ℕ) ]
  > even_odd : sig ( even : ℕ → bool, odd : ℕ → bool)
  > even_odd =
  >   let rec even : ℕ → bool = λ { zero → true ; suc n → odd n }
  >   and odd : ℕ → bool = λ { zero → false ; suc n → even n } in
  >   (even, odd)
  > echo even_odd even 4
  > echo even_odd odd 4
  > postulate n : ℕ
  > echo even_odd even n
  > EOF

  $ agdarya -v even-odd.ny
   ￫ info[I0000]
   ￮ constant bool defined
  
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ hint[H0403]
   ￭ $TESTCASE_ROOT/even-odd.ny
   1 | even_odd : sig ( even : ℕ → bool, odd : ℕ → bool)
     ^ sig encountered outside case tree, wrapping in implicit let-binding
  
   ￫ info[I0000]
   ￮ constant even_odd defined
  
  true
    : bool
  
  false
    : bool
  
   ￫ info[I0001]
   ￮ postulate n assumed
  
  _letrec.F2.1.even{…} n
    : bool
  
