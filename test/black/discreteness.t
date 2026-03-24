  $ cat >jd.ny <<EOF
  > data Jd (X:Set) (x:X) : X → Set where { rfl : Jd X x x }
  > EOF

Arbitrary types are not discrete:

  $ cat >arb.ny <<EOF
  > postulate A : Set
  > postulate a : A
  > T = A⁽ᵈ⁾ a
  > EOF

  $ agdarya -source-only -parametric -arity 1 -direction d arb.ny jd.ny -e 'test : (t1 : T) → (t2 : T) → Jd T t1 t2' -e 'test t1 t2 = rfl'
   ￫ error[E1003]
   ￭ command-line exec string
   1 | test t1 t2 = rfl
     ^ index
         t1
       of constructor application doesn't match the corresponding index
         t2
       of datatype instance: unequal head variables:
         t1
       does not equal
         t2
  
  [1]

They remain so even when discreteness is on:

  $ agdarya -source-only -parametric -arity 1 -direction d -discreteness arb.ny jd.ny -e 'test : (t1 : T) → (t2 : T) → Jd T t1 t2' -e 'test t1 t2 = rfl'
   ￫ error[E1003]
   ￭ command-line exec string
   1 | test t1 t2 = rfl
     ^ index
         t1
       of constructor application doesn't match the corresponding index
         t2
       of datatype instance: unequal head variables:
         t1
       does not equal
         t2
  
  [1]

There are no discrete datatypes if discreteness is off:

  $ cat >natd.ny <<EOF
  > data ℕ : Set where { zero : ℕ; suc : ℕ → ℕ }
  > postulate n : ℕ
  > T = ℕ⁽ᵈ⁾ n
  > EOF

  $ agdarya -source-only -v -parametric -arity 1 -direction d natd.ny jd.ny -e 'test : (t1 : T) → (t2 : T) → Jd T t1 t2' -e 'test t1 t2 = rfl'
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0001]
   ￮ postulate n assumed
  
   ￫ info[I0000]
   ￮ constant T defined
  
   ￫ info[I0000]
   ￮ constant Jd defined
  
   ￫ error[E1003]
   ￭ command-line exec string
   1 | test t1 t2 = rfl
     ^ index
         t1
       of constructor application doesn't match the corresponding index
         t2
       of datatype instance: unequal head variables:
         t1
       does not equal
         t2
  
  [1]

Discrete datatypes are not themselves propositions:

  $ cat >nat.ny <<EOF
  > data T : Set where { zero : T; suc : T → T }
  > EOF

  $ agdarya -source-only -v -parametric -arity 1 -direction d -discreteness nat.ny jd.ny -e 'test : (t1 : T) → (t2 : T) → Jd T t1 t2' -e 'test t1 t2 = rfl'
   ￫ info[I0000]
   ￮ discrete constant T defined
  
   ￫ info[I0000]
   ￮ constant Jd defined
  
   ￫ error[E1003]
   ￭ command-line exec string
   1 | test t1 t2 = rfl
     ^ index
         t1
       of constructor application doesn't match the corresponding index
         t2
       of datatype instance: unequal head variables:
         t1
       does not equal
         t2
  
  [1]

But their degenerate versions are:

  $ cat >natd.ny <<EOF
  > data ℕ : Set where { zero : ℕ; suc : ℕ → ℕ }
  > postulate n : ℕ
  > T = ℕ⁽ᵈ⁾ n
  > EOF

  $ agdarya -source-only -v -parametric -arity 1 -direction d -discreteness natd.ny jd.ny -e 'test : (t1 : T) → (t2 : T) → Jd T t1 t2' -e 'test t1 t2 = rfl'
   ￫ info[I0000]
   ￮ discrete constant ℕ defined
  
   ￫ info[I0001]
   ￮ postulate n assumed
  
   ￫ info[I0000]
   ￮ constant T defined
  
   ￫ info[I0000]
   ￮ constant Jd defined
  
   ￫ info[I0000]
   ￮ constant test defined
  

Datatypes with nondiscrete parameters are not discrete:

  $ cat >param.ny <<EOF
  > data List (A:Set) : Set where { nil : List A; cons : A → List A → List A }
  > postulate A : Set
  > postulate l : List A
  > T = (List A)⁽ᵈ⁾ l
  > EOF

  $ agdarya -source-only -v -parametric -arity 1 -direction d -discreteness param.ny jd.ny -e 'test : (t1 : T) → (t2 : T) → Jd T t1 t2' -e 'test t1 t2 = rfl'
   ￫ info[I0000]
   ￮ constant List defined
  
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate l assumed
  
   ￫ info[I0000]
   ￮ constant T defined
  
   ￫ info[I0000]
   ￮ constant Jd defined
  
   ￫ error[E1003]
   ￭ command-line exec string
   1 | test t1 t2 = rfl
     ^ index
         t1
       of constructor application doesn't match the corresponding index
         t2
       of datatype instance: unequal head variables:
         t1
       does not equal
         t2
  
  [1]

Even trivial parameters:

  $ cat >param2.ny <<EOF
  > data param_empty (A:Set) : Set where { }
  > postulate A : Set
  > postulate l : param_empty A
  > T = (param_empty A)⁽ᵈ⁾ l
  > EOF

  $ agdarya -source-only -v -parametric -arity 1 -direction d -discreteness param2.ny jd.ny -e 'test : (t1 : T) → (t2 : T) → Jd T t1 t2' -e 'test t1 t2 = rfl'
   ￫ info[I0000]
   ￮ constant param_empty defined
  
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate l assumed
  
   ￫ info[I0000]
   ￮ constant T defined
  
   ￫ info[I0000]
   ￮ constant Jd defined
  
   ￫ error[E1003]
   ￭ command-line exec string
   1 | test t1 t2 = rfl
     ^ index
         t1
       of constructor application doesn't match the corresponding index
         t2
       of datatype instance: unequal head variables:
         t1
       does not equal
         t2
  
  [1]


But datatypes with discrete parameters are discrete:

  $ cat >param3.ny <<EOF
  > data ℕ : Set where { zero : ℕ; suc : ℕ → ℕ }
  > data param_empty (n:ℕ) : Set where { }
  > postulate l : param_empty zero
  > T = (param_empty zero)⁽ᵈ⁾ l
  > EOF

  $ agdarya -source-only -v -parametric -arity 1 -direction d -discreteness param3.ny jd.ny -e 'test : (t1 : T) → (t2 : T) → Jd T t1 t2' -e 'test t1 t2 = rfl'
   ￫ info[I0000]
   ￮ discrete constant ℕ defined
  
   ￫ info[I0000]
   ￮ discrete constant param_empty defined
  
   ￫ info[I0001]
   ￮ postulate l assumed
  
   ￫ info[I0000]
   ￮ constant T defined
  
   ￫ info[I0000]
   ￮ constant Jd defined
  
   ￫ info[I0000]
   ￮ constant test defined
  


Datatypes with discrete indices are discrete:

  $ cat >index.ny <<EOF
  > data ℕ : Set where { zero : ℕ; suc : ℕ → ℕ }
  > data iszero : ℕ → Set where { iszero : iszero zero }
  > postulate n : ℕ
  > postulate z : iszero n
  > T = (iszero n)⁽ᵈ⁾ z
  > EOF

  $ agdarya -source-only -v -parametric -arity 1 -direction d -discreteness index.ny jd.ny -e 'test : (t1 : T) → (t2 : T) → Jd T t1 t2' -e 'test t1 t2 = rfl'
   ￫ info[I0000]
   ￮ discrete constant ℕ defined
  
   ￫ info[I0000]
   ￮ discrete constant iszero defined
  
   ￫ info[I0001]
   ￮ postulate n assumed
  
   ￫ info[I0001]
   ￮ postulate z assumed
  
   ￫ info[I0000]
   ￮ constant T defined
  
   ￫ info[I0000]
   ￮ constant Jd defined
  
   ￫ info[I0000]
   ￮ constant test defined
  

But datatypes with nondiscrete indices, even trivial ones, are not discrete:

  $ cat >index2.ny <<EOF
  > postulate N : Set
  > postulate n : N
  > data index_unit : N → Set where { foo : index_unit n }
  > postulate z : index_unit n
  > T = (index_unit n)⁽ᵈ⁾ z
  > EOF

  $ agdarya -source-only -v -parametric -arity 1 -direction d -discreteness index2.ny jd.ny -e 'test : (t1 : T) → (t2 : T) → Jd T t1 t2' -e 'test t1 t2 = rfl'
   ￫ info[I0001]
   ￮ postulate N assumed
  
   ￫ info[I0001]
   ￮ postulate n assumed
  
   ￫ info[I0000]
   ￮ constant index_unit defined
  
   ￫ info[I0001]
   ￮ postulate z assumed
  
   ￫ info[I0000]
   ￮ constant T defined
  
   ￫ info[I0000]
   ￮ constant Jd defined
  
   ￫ error[E1003]
   ￭ command-line exec string
   1 | test t1 t2 = rfl
     ^ index
         t1
       of constructor application doesn't match the corresponding index
         t2
       of datatype instance: unequal head variables:
         t1
       does not equal
         t2
  
  [1]


Datatypes with constructors having non-discrete arguments are not discrete:

  $ cat >constr.ny <<EOF
  > data foo : Set where { foo : Set → foo }
  > postulate f : foo
  > T = foo⁽ᵈ⁾ f
  > EOF

  $ agdarya -source-only -v -parametric -arity 1 -direction d -discreteness constr.ny jd.ny -e 'test : (t1 : T) → (t2 : T) → Jd T t1 t2' -e 'test t1 t2 = rfl'
   ￫ info[I0000]
   ￮ constant foo defined
  
   ￫ info[I0001]
   ￮ postulate f assumed
  
   ￫ info[I0000]
   ￮ constant T defined
  
   ￫ info[I0000]
   ￮ constant Jd defined
  
   ￫ error[E1003]
   ￭ command-line exec string
   1 | test t1 t2 = rfl
     ^ index
         t1
       of constructor application doesn't match the corresponding index
         t2
       of datatype instance: unequal head variables:
         t1
       does not equal
         t2
  
  [1]


Trivially mutually datatypes are discrete:

  $ cat >mutual2.ny <<EOF
  > data empty : Set where { } and unit : Set where { }
  > postulate e : unit
  > T = unit⁽ᵈ⁾ e
  > EOF

  $ agdarya -source-only -v -parametric -arity 1 -direction d -discreteness mutual2.ny jd.ny -e 'test : (t1 : T) → (t2 : T) → Jd T t1 t2' -e 'test t1 t2 = rfl'
   ￫ info[I0000]
   ￮ discrete constants defined mutually:
       empty
       unit
  
   ￫ info[I0001]
   ￮ postulate e assumed
  
   ￫ info[I0000]
   ￮ constant T defined
  
   ￫ info[I0000]
   ￮ constant Jd defined
  
   ￫ info[I0000]
   ￮ constant test defined
  


Nontrivially mutual datatypes can also be discrete, if treating them all as discrete validates all of their discreteness:

  $ cat >mutual3.ny <<EOF
  > data even : Set where { zero : even; suc : odd → even } and odd : Set where { suc : even → odd }
  > postulate e : even
  > T = even⁽ᵈ⁾ e
  > EOF

  $ agdarya -source-only -v -parametric -arity 1 -direction d -discreteness mutual3.ny jd.ny -e 'test : (t1 : T) → (t2 : T) → Jd T t1 t2' -e 'test t1 t2 = rfl'
   ￫ info[I0000]
   ￮ discrete constants defined mutually:
       even
       odd
  
   ￫ info[I0001]
   ￮ postulate e assumed
  
   ￫ info[I0000]
   ￮ constant T defined
  
   ￫ info[I0000]
   ￮ constant Jd defined
  
   ￫ info[I0000]
   ￮ constant test defined
  


Including if they have discrete indices:

  $ cat >mutual4.ny <<EOF
  > data ℕ : Set where { zero : ℕ; suc : ℕ → ℕ }
  > data even : ℕ → Set where { zero : even zero; suc : (n : ℕ) → odd n → even (suc n) } and odd : ℕ → Set where { suc : (n:ℕ) → even n → odd (suc n) }
  > postulate e : even 2
  > T = even⁽ᵈ⁾ {2} 2 e
  > EOF

  $ agdarya -source-only -v -parametric -arity 1 -direction d -discreteness mutual4.ny jd.ny -e 'test : (t1 : T) → (t2 : T) → Jd T t1 t2' -e 'test t1 t2 = rfl'
   ￫ info[I0000]
   ￮ discrete constant ℕ defined
  
   ￫ info[I0000]
   ￮ discrete constants defined mutually:
       even
       odd
  
   ￫ info[I0001]
   ￮ postulate e assumed
  
   ￫ info[I0000]
   ￮ constant T defined
  
   ￫ info[I0000]
   ￮ constant Jd defined
  
   ￫ info[I0000]
   ￮ constant test defined
  

But nondiscreteness of any of them throws the others off:

  $ cat >mutual5.ny <<EOF
  > data empty1 (A : Set) : Set where { } and empty2 : Set where { }
  > postulate e : empty2
  > T = empty2⁽ᵈ⁾ e
  > EOF

  $ agdarya -source-only -v -parametric -arity 1 -direction d -discreteness mutual5.ny jd.ny -e 'test : (t1 : T) → (t2 : T) → Jd T t1 t2' -e 'test t1 t2 = rfl'
   ￫ info[I0000]
   ￮ constants defined mutually:
       empty1
       empty2
  
   ￫ info[I0001]
   ￮ postulate e assumed
  
   ￫ info[I0000]
   ￮ constant T defined
  
   ￫ info[I0000]
   ￮ constant Jd defined
  
   ￫ error[E1003]
   ￭ command-line exec string
   1 | test t1 t2 = rfl
     ^ index
         t1
       of constructor application doesn't match the corresponding index
         t2
       of datatype instance: unequal head variables:
         t1
       does not equal
         t2
  
  [1]

Some other discrete types:

  $ agdarya -source-only -v -parametric -arity 1 -direction d -discreteness -e 'data ℕ : Set where { zero : ℕ; suc : ℕ → ℕ }' -e 'data ℤ : Set where { zero : ℤ; suc : ℕ → ℤ; negsuc : ℕ → ℤ }' -e 'data btree : Set where { leaf : btree; node : btree → btree → btree }'
   ￫ info[I0000]
   ￮ discrete constant ℕ defined
  
   ￫ info[I0000]
   ￮ discrete constant ℤ defined
  
   ￫ info[I0000]
   ￮ discrete constant btree defined
  
