  $ agdarya -v matchterm.ny
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant plus defined
  
   ￫ info[I0000]
   ￮ constant bool defined
  
   ￫ info[I0000]
   ￮ constant plus_is_1 defined
  
  true
    : bool
  
  false
    : bool
  
  true
    : bool
  
  false
    : bool
  
  false
    : bool
  
   ￫ info[I0000]
   ￮ constant ⊥ defined
  
   ￫ info[I0000]
   ￮ constant contra defined
  
   ￫ hint[E1101]
   ￭ $TESTCASE_ROOT/matchterm.ny
   1 | doublematch n = match n [ zero ↦ false | suc k ↦ match n [ zero ↦ true | suc _ ↦ false ]]
     ^ match will not refine the goal or context (discriminee is let-bound): n
  
   ￫ info[I0000]
   ￮ constant doublematch defined
  
   ￫ info[I0000]
   ￮ constant doublematch' defined
  
   ￫ info[I0000]
   ￮ constant ⊤ defined
  
   ￫ info[I0000]
   ￮ constant zero_or_suc defined
  
   ￫ info[I0000]
   ￮ constant plus_zero_or_suc defined
  
   ￫ info[I0000]
   ￮ constant Vec defined
  
   ￫ info[I0000]
   ￮ constant idvec defined
  
   ￫ info[I0000]
   ￮ constant nil_or_cons defined
  
   ￫ info[I0000]
   ￮ constant idvec_nil_or_cons defined
  

  $ agdarya -v -parametric multi.ny
   ￫ info[I0000]
   ￮ constant bool defined
  
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant bool.and defined
  
  true
    : bool
  
  false
    : bool
  
   ￫ info[I0000]
   ￮ constant plus defined
  
   ￫ info[I0002]
   ￮ notation «_ + _» defined
  
   ￫ info[I0000]
   ￮ constant fib defined
  
  13
    : ℕ
  
  21
    : ℕ
  
   ￫ info[I0000]
   ￮ constant fib' defined
  
   ￫ info[I0000]
   ￮ constant fib'' defined
  
   ￫ info[I0000]
   ￮ constant even defined
  
   ￫ info[I0000]
   ￮ constant minus2 defined
  
  2
    : ℕ
  
   ￫ info[I0000]
   ￮ constant bothzero defined
  
  false
    : bool
  
  false
    : bool
  
  true
    : bool
  
   ￫ info[I0000]
   ￮ constant ⊥ defined
  
   ￫ info[I0000]
   ￮ constant abort1 defined
  
   ￫ info[I0000]
   ￮ constant abort2 defined
  
   ￫ info[I0000]
   ￮ constant Gel defined
  
   ￫ info[I0000]
   ￮ constant ⊤ defined
  
   ￫ hint[H0403]
   ￭ $TESTCASE_ROOT/multi.ny
   1 | ⊤eq⊥ = Gel ⊤ ⊥ (λ { })
     ^ matching lambda encountered outside case tree, wrapping in implicit let-binding
  
   ￫ info[I0000]
   ￮ constant ⊤eq⊥ defined
  
   ￫ info[I0000]
   ￮ constant foo defined
  
   ￫ info[I0000]
   ￮ constant one_not_even defined
  
   ￫ info[I0000]
   ￮ constant suc_even_not_even defined
  
   ￫ info[I0000]
   ￮ constant suc_even_not_even' defined
  
   ￫ info[I0000]
   ￮ constant sum defined
  
   ￫ info[I0000]
   ￮ constant sum⊥ defined
  
   ￫ info[I0000]
   ￮ constant sum⊥' defined
  
   ￫ info[I0001]
   ￮ postulate oops assumed
  
  sum⊥' Set (inr oops)
    : Set
  
   ￫ info[I0000]
   ￮ constant sum⊥'' defined
  
   ￫ info[I0000]
   ￮ constant sum⊥''' defined
  
   ￫ info[I0000]
   ￮ constant is_zero defined
  
   ￫ info[I0000]
   ￮ constant is_zero_eq_zero defined
  
   ￫ info[I0000]
   ￮ constant is_zero_eq_zero' defined
  
   ￫ info[I0000]
   ￮ constant is_zero_eq_zero_rev defined
  
   ￫ info[I0000]
   ￮ constant is_zero_eq_zero_rev' defined
  
   ￫ info[I0000]
   ￮ constant bar defined
  
   ￫ info[I0000]
   ￮ constant bar' defined
  
   ￫ info[I0000]
   ￮ constant bar'' defined
  
   ￫ info[I0000]
   ￮ constant baz defined
  
   ￫ info[I0000]
   ￮ constant bazzz defined
  


  $ agdarya -e 'data bool : Set where { true : bool ; false : bool }' -e 'bool.and : bool → bool → bool' -e 'bool.and x y = match x,y [ true , true ↦ true | true , false ↦ false | _ , false ↦ false ]'
   ￫ error[E1307]
   ￭ command-line exec string
   1 | bool.and x y = match x,y [ true , true ↦ true | true , false ↦ false | _ , false ↦ false ]
     ^ overlapping patterns in match
  
  [1]

  $ agdarya -e 'postulate A : Set' -e 'postulate B : Set' -e 'data AB : Set where { left : A → AB ; right : B → AB }' -e 'foo : AB → AB → AB' -e 'foo x y = match x,y [ left a, right b ↦ left a | left a, left b ↦ left b | left a, right b ↦ left a | right b, _ ↦ right b ]'
   ￫ error[E1302]
   ￭ command-line exec string
   1 | foo x y = match x,y [ left a, right b ↦ left a | left a, left b ↦ left b | left a, right b ↦ left a | right b, _ ↦ right b ]
     ^ constructor right appears twice in match
  
  [1]

  $ agdarya -e 'data bool : Set where { true : bool ; false : bool }' -e 'test : bool → bool → bool' -e 'test x y = match x,y [ true , true ↦ true | false ↦ false ]'
   ￫ error[E1305]
   ￭ command-line exec string
   1 | test x y = match x,y [ true , true ↦ true | false ↦ false ]
     ^ wrong number of patterns for match
  
  [1]

  $ agdarya -e 'data bool : Set where { true : bool ; false : bool }' -e 'test : bool → bool → bool' -e 'test x y = match x,y [ true , true ↦ true | true, false, false ↦ false ]'
   ￫ error[E0200]
   ￭ command-line exec string
   1 | test x y = match x,y [ true , true ↦ true | true, false, false ↦ false ]
     ^ parse error
  
  [1]

  $ agdarya -e 'data bool : Set where { true : bool ; false : bool }' -e 'neg : bool → bool' -e 'neg x = match x [ true ↦ false | false ↦ . ]'
   ￫ error[E1309]
   ￭ command-line exec string
   1 | neg x = match x [ true ↦ false | false ↦ . ]
     ^ invalid refutation: no discriminee has an empty type
  
  [1]

  $ agdarya -v -e 'data bool : Set where { true : bool ; false : bool }' -e 'data ⊥ : Set where { }' -e 'foo : ⊥ → bool → ⊥' -e 'foo x y = match x, y [ ]' -e 'foo2 : ⊥ → bool → ⊥' -e 'foo2 x y = match y, x [ ]' -e 'data unit : Set where { star : unit }' -e 'foo3 : bool → unit → ⊥' -e 'foo3 x y = match x, y [ ]'
   ￫ info[I0000]
   ￮ constant bool defined
  
   ￫ info[I0000]
   ￮ constant ⊥ defined
  
   ￫ info[I0000]
   ￮ constant foo defined
  
   ￫ info[I0000]
   ￮ constant foo2 defined
  
   ￫ info[I0000]
   ￮ constant unit defined
  
   ￫ error[E1300]
   ￭ command-line exec string
   1 | foo3 x y = match x, y [ ]
     ^ missing match clause for constructor true
  
  [1]

  $ agdarya -e 'data bool : Set where { true : bool ; false : bool }' -e 'foo : bool → bool' -e 'foo x = match x [ true ↦ false | false y ↦ true ]'
   ￫ error[E1303]
   ￭ command-line exec string
   1 | foo x = match x [ true ↦ false | false y ↦ true ]
     ^ too many arguments to constructor false in match pattern (1 extra)
  
  [1]


  $ agdarya -e 'data bool : Set where { true : bool ; false : bool }' -e 'foo : bool → bool' -e 'foo x = match x [ true ↦ false | true y ↦ true ]'
   ￫ error[E1306]
   ￭ command-line exec string
   1 | foo x = match x [ true ↦ false | true y ↦ true ]
     ^ inconsistent patterns in match
  
  [1]
  $ agdarya -e 'data prod (A B : Set) : Set where { pair : A → B → prod A B }' -e 'proj1 : (A B C : Set) → prod (prod A B) C → C' -e 'proj1 A B C u = match u [ pair (pair x x) x ↦ x ]'
   ￫ error[E1304]
   ￭ command-line exec string
   1 | proj1 A B C u = match u [ pair (pair x x) x ↦ x ]
     ^ variable name 'x' used more than once in match patterns
  
  [1]

  $ agdarya -e 'data prod (A B : Set) : Set where { pair : A → B → prod A B }' -e 'proj1 : (A B : Set) → prod A B → A' -e 'proj1 A B u = match u return _ ↦ A [ pair x x ↦ x ]'
   ￫ error[E1304]
   ￭ command-line exec string
   1 | proj1 A B u = match u return _ ↦ A [ pair x x ↦ x ]
     ^ variable name 'x' used more than once in match patterns
  
  [1]

  $ agdarya -e 'data bool : Set where { true : bool ; false : bool }' -e 'foo : bool → bool → bool' -e 'foo = λ { }'
   ￫ error[E1300]
   ￭ command-line exec string
   1 | foo = λ { }
     ^ missing match clause for constructor true
  
  [1]

  $ agdarya -e 'data bool : Set where { true : bool ; false : bool }' -e 'foo : Set → bool → bool' -e 'foo = λ { }'
   ￫ error[E1200]
   ￭ command-line exec string
   1 | foo = λ { }
     ^ can't match on variable belonging to non-datatype Set
  
  [1]

  $ agdarya -v -parametric -e 'data bool : Set where { true : bool ; false : bool }' -e 'bool.not : bool → bool' -e 'bool.not x = match x [ true ⤇ false | false ⤇ true]'
   ￫ info[I0000]
   ￮ constant bool defined
  
   ￫ error[E0508]
   ￭ command-line exec string
   1 | bool.not x = match x [ true ⤇ false | false ⤇ true]
     ^ cube abstraction not allowed for zero-dimensional match
  
  [1]

  $ agdarya -v -parametric -e 'data bool : Set where { true : bool ; false : bool }' -e 'bool.and : bool → bool → bool' -e 'bool.and x y = match x, y [ true, true ⤇ true | true, false ⤇ false | false, true ⤇ false | false, false ⤇ false]'
   ￫ info[I0000]
   ￮ constant bool defined
  
   ￫ error[E0508]
   ￭ command-line exec string
   1 | bool.and x y = match x, y [ true, true ⤇ true | true, false ⤇ false | false, true ⤇ false | false, false ⤇ false]
     ^ cube abstraction not allowed for zero-dimensional match
  
  [1]

  $ agdarya -v -parametric -e 'data ℕ : Set where { zero : ℕ ; suc : ℕ → ℕ }' -e 'bar : (y0 y1 : ℕ) → Id ℕ y0 y1 → Set' -e 'bar y0 y1 y2 = match y2 [ zero ↦ ℕ | suc n ↦ bar n⟨0⟩ n⟨1⟩ n⟨2⟩ ]'
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ error[E0510]
   ￭ command-line exec string
   1 | bar y0 y1 y2 = match y2 [ zero ↦ ℕ | suc n ↦ bar n⟨0⟩ n⟨1⟩ n⟨2⟩ ]
     ^ e-dimensional match requires cube abstraction
  
  [1]

  $ agdarya -v -parametric -e 'data ℕ : Set where { zero : ℕ ; suc : ℕ → ℕ }' -e 'bar : (x : ℕ) → (y0 y1 : ℕ) → Id ℕ y0 y1 → Set' -e 'bar x y0 y1 y2 = match x, y2 [ zero, zero ↦ ℕ | zero, suc n ↦ bar x n⟨0⟩ n⟨1⟩ n⟨2⟩ | suc _, zero ↦ ℕ | suc _, suc n ↦ bar x n⟨0⟩ n⟨1⟩ n⟨2⟩ ]'
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ error[E0510]
   ￭ command-line exec string
   1 | bar x y0 y1 y2 = match x, y2 [ zero, zero ↦ ℕ | zero, suc n ↦ bar x n⟨0⟩ n⟨1⟩ n⟨2⟩ | suc _, zero ↦ ℕ | suc _, suc n ↦ bar x n⟨0⟩ n⟨1⟩ n⟨2⟩ ]
     ^ e-dimensional match requires cube abstraction
  
   ￫ error[E0510]
   ￭ command-line exec string
   1 | bar x y0 y1 y2 = match x, y2 [ zero, zero ↦ ℕ | zero, suc n ↦ bar x n⟨0⟩ n⟨1⟩ n⟨2⟩ | suc _, zero ↦ ℕ | suc _, suc n ↦ bar x n⟨0⟩ n⟨1⟩ n⟨2⟩ ]
     ^ e-dimensional match requires cube abstraction
  
  [1]
