  $ agdarya -v -parametric errors.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate a assumed
  
   ￫ info[I0001]
   ￮ postulate f assumed
  
   ￫ info[I0001]
   ￮ postulate x assumed
  
   ￫ info[I0001]
   ￮ postulate y assumed
  
   ￫ info[I0001]
   ￮ postulate xy assumed
  
   ￫ info[I0000]
   ￮ constant Σ defined
  
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant Nat defined
  
   ￫ info[I0001]
   ￮ postulate B assumed
  
   ￫ info[I0001]
   ￮ postulate s assumed
  
   ￫ info[I0000]
   ￮ constant Gel defined
  
   ￫ info[I0001]
   ￮ postulate A0 assumed
  
   ￫ info[I0001]
   ￮ postulate B0 assumed
  
   ￫ info[I0001]
   ￮ postulate R0 assumed
  
   ￫ info[I0001]
   ￮ postulate A1 assumed
  
   ￫ info[I0001]
   ￮ postulate B1 assumed
  
   ￫ info[I0001]
   ￮ postulate R1 assumed
  
   ￫ info[I0001]
   ￮ postulate A2 assumed
  
   ￫ info[I0001]
   ￮ postulate B2 assumed
  
   ￫ info[I0001]
   ￮ postulate R2 assumed
  
   ￫ info[I0001]
   ￮ postulate a0 assumed
  
   ￫ info[I0001]
   ￮ postulate a1 assumed
  
   ￫ info[I0001]
   ￮ postulate a2 assumed
  
   ￫ info[I0001]
   ￮ postulate b0 assumed
  
   ￫ info[I0001]
   ￮ postulate b1 assumed
  
   ￫ info[I0001]
   ￮ postulate b2 assumed
  
   ￫ info[I0001]
   ￮ postulate r0 assumed
  
   ￫ info[I0001]
   ￮ postulate r1 assumed
  
   ￫ info[I0001]
   ￮ postulate r2 assumed
  
   ￫ info[I0000]
   ￮ constant r2ty defined
  
   ￫ info[I0000]
   ￮ constant symr2ty defined
  
   ￫ info[I0001]
   ￮ postulate gg assumed
  
   ￫ info[I0001]
   ￮ postulate gg' assumed
  
   ￫ info[I0001]
   ￮ postulate af assumed
  
   ￫ info[I0000]
   ￮ constant Stream defined
  
   ￫ info[I0000]
   ￮ constant zeros defined
  
   ￫ info[I0001]
   ￮ postulate idz assumed
  
  $ agdarya -parametric errors.ny -e "echo a : Set"
   ￫ error[E0401]
   ￭ command-line exec string
   1 | echo a : Set
     ^ term synthesized type
         A
       but is being checked against type
         Set
       unequal head terms:
         A
       does not equal
         Set
  
  [1]
  $ agdarya -parametric errors.ny -e "echo (refl f {a})"
   ￫ error[E0502]
   ￭ command-line exec string
   1 | echo (refl f {a})
     ^ not enough arguments for a higher-dimensional function application
  
  [1]

  $ agdarya -parametric errors.ny -e "echo (refl f {a} {a})"
   ￫ error[E0502]
   ￭ command-line exec string
   1 | echo (refl f {a} {a})
     ^ not enough arguments for a higher-dimensional function application
  
  [1]
  $ agdarya -parametric errors.ny -e "echo (refl f (refl a) a)"
   ￫ error[E0701]
   ￭ command-line exec string
   1 | echo (refl f (refl a) a)
     ^ attempt to apply/instantiate
         ap f (refl a)
       of type
         Id A (f a) (f a)
       which is not a function-type or universe
  
  [1]

  $ agdarya -parametric errors.ny -e "echo (Id A a)"
   ￫ error[E0503]
   ￭ command-line exec string
   1 | echo (Id A a)
     ^ not enough arguments to instantiate a higher-dimensional type
  
  [1]
  $ agdarya -parametric errors.ny -e "echo ((x |-> x) : Id (A -> A) f f)"
   ￫ error[E0702]
   ￭ command-line exec string
   1 | echo ((x |-> x) : Id (A -> A) f f)
     ^ unexpected explicit abstraction: expecting implicit variable
  
  [1]
  $ agdarya -parametric errors.ny -e "echo (({x} {y} |-> x) : Id (A -> A) f f)"
   ￫ error[E0501]
   ￭ command-line exec string
   1 | echo (({x} {y} |-> x) : Id (A -> A) f f)
     ^ not enough non-cube variables for higher-dimensional abstraction: need 1 more
  
  [1]
  $ agdarya -parametric errors.ny -e "echo (({x0} {x1} x2 x3 ↦ refl f x0 x1 x2) : Id (A -> A) f f)"
   ￫ error[E0700]
   ￭ command-line exec string
   1 | echo (({x0} {x1} x2 x3 ↦ refl f x0 x1 x2) : Id (A -> A) f f)
     ^ checking abstraction against non-function type Id A (f x0) (f x1)
  
  [1]
  $ agdarya -parametric errors.ny -e "echo (refl (x |-> x))"
   ￫ error[E0400]
   ￭ command-line exec string
   1 | echo (refl (x |-> x))
     ^ non-synthesizing term in synthesizing position (argument of degeneracy)
  
  [1]
  $ agdarya -parametric errors.ny -e "echo refl"
   ￫ error[E0600]
   ￭ command-line exec string
   1 | echo refl
     ^ missing argument for degeneracy refl
  
  [1]
  $ agdarya -parametric errors.ny -e "echo (sym f)"
   ￫ error[E0601]
   ￭ command-line exec string
   1 | echo (sym f)
     ^ insufficient dimension for argument of degeneracy 'sym':
        0 does not factor through ee
  
  [1]
  $ agdarya -parametric errors.ny -e "echo (sym a2)"
   ￫ error[E0601]
   ￭ command-line exec string
   1 | echo (sym a2)
     ^ insufficient dimension for argument of degeneracy 'sym':
        e does not factor through ee
  
  [1]
  $ agdarya -parametric errors.ny -e "echo g"
   ￫ error[E0300]
   ￭ command-line exec string
   1 | echo g
     ^ unbound variable: g
  
  [1]
  $ agdarya -parametric errors.ny -e "echo (a : Id A)"
   ￫ error[E0401]
   ￭ command-line exec string
   1 | echo (a : Id A)
     ^ term synthesized type
         Set⁽ᵉ⁾ A A
       but is being checked against type
         Set
       unequal head terms:
         Set⁽ᵉ⁾
       does not equal
         Set
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | echo (a : Id A)
     ^ term synthesized type
         Set⁽ᵉ⁾ A A
       but is being checked against type
         Set
       unequal head terms:
         Set⁽ᵉ⁾
       does not equal
         Set
  
  [1]
  $ agdarya -parametric errors.ny -e "echo (a : Id (Id A) (refl a) (refl a))"
   ￫ error[E0401]
   ￭ command-line exec string
   1 | echo (a : Id (Id A) (refl a) (refl a))
     ^ term synthesized type
         Set⁽ᵉ⁾ (Id A a a) (Id A a a)
       but is being checked against type
         Set
       unequal head terms:
         Set⁽ᵉ⁾
       does not equal
         Set
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | echo (a : Id (Id A) (refl a) (refl a))
     ^ term synthesized type
         Set⁽ᵉ⁾ (Id A a a) (Id A a a)
       but is being checked against type
         Set
       unequal head terms:
         Set⁽ᵉ⁾
       does not equal
         Set
  
  [1]
  $ agdarya -parametric errors.ny -e "q = Id Set A (Id A)"
   ￫ error[E0401]
   ￭ command-line exec string
   1 | q = Id Set A (Id A)
     ^ term synthesized type
         Set⁽ᵉ⁾ A A
       but is being checked against type
         Set
       unequal head terms:
         Set⁽ᵉ⁾
       does not equal
         Set
  
  [1]
  $ agdarya -parametric errors.ny -e "f (x"

  $ agdarya -parametric errors.ny -e ".fst x"
  $ agdarya -parametric errors.ny -e "echo (x |-> x fs.t y)"
   ￫ error[E0300]
   ￭ command-line exec string
   1 | echo (x |-> x fs.t y)
     ^ unbound variable: fs.t
  
  [1]
  $ agdarya -parametric errors.ny -e "echo (f (con.str. x))"
   ￫ error[E0100]
   ￭ command-line exec string
   1 | echo (f (con.str. x))
     ^ unimplemented: higher constructors in terms
  
  [1]
  $ agdarya -parametric errors.ny -e "echo (x |-> f 0.1.2 x)"
   ￫ error[E0205]
   ￭ command-line exec string
   1 | echo (x |-> f 0.1.2 x)
     ^ invalid numeral: 0.1.2
  
  [1]
  $ agdarya -parametric errors.ny -e "echo (let x.y ≔ z in w)"
   ￫ error[E0202]
   ￭ command-line exec string
   1 | echo (let x.y ≔ z in w)
     ^ invalid local variable name: x.y
  
  [1]
  $ agdarya -parametric errors.ny -e "echo (x.y ↦ z)"
   ￫ error[E0202]
   ￭ command-line exec string
   1 | echo (x.y ↦ z)
     ^ invalid local variable name: x.y
  
  [1]
  $ agdarya -parametric errors.ny -e "echo (a x.y b ↦ z)"
   ￫ error[E0202]
   ￭ command-line exec string
   1 | echo (a x.y b ↦ z)
     ^ invalid local variable name: x.y
  
  [1]
  $ agdarya -parametric errors.ny -e "echo (↦ z)"
   ￫ error[E0200]
   ￭ command-line exec string
   1 | echo (↦ z)
     ^ parse error
  
  [1]
  $ agdarya -parametric errors.ny -e "echo ((f x) y ↦ z)"
   ￫ error[E0200]
   ￭ command-line exec string
   1 | echo ((f x) y ↦ z)
     ^ parse error
  
  [1]
  $ agdarya -parametric errors.ny -e "echo _"
   ￫ error[E0100]
   ￭ command-line exec string
   1 | echo _
     ^ unimplemented: unification arguments
  
  [1]
  $ agdarya -parametric errors.ny -e "echo (a ↦ ( fst ≔ a, fst ≔ a ))"
   ￫ error[E0904]
   ￭ command-line exec string
   1 | echo (a ↦ ( fst ≔ a, fst ≔ a ))
     ^ record field 'fst' appears more than once in tuple
  
  [1]
  $ agdarya -parametric errors.ny -e "echo ( (x) ≔ a )"
   ￫ error[E0905]
   ￭ command-line exec string
   1 | echo ( (x) ≔ a )
     ^ invalid field in tuple
  
  [1]
  $ agdarya -parametric errors.ny -e "echo ([ _ ↦ a ])"
   ￫ error[E0217]
   ￭ command-line exec string
   1 | echo ([ _ ↦ a ])
     ^ standalone bracket syntax removed; use λ { … } for matching lambdas or record { … } for codata values
  
  [1]
  $ agdarya -parametric errors.ny -e "echo ([ (x) ↦ a ])"
   ￫ error[E0217]
   ￭ command-line exec string
   1 | echo ([ (x) ↦ a ])
     ^ standalone bracket syntax removed; use λ { … } for matching lambdas or record { … } for codata values
  
  [1]
  $ agdarya -parametric errors.ny -e "echo ([ | | head |-> 0 | tail |-> f ])"
   ￫ error[E0200]
   ￭ command-line exec string
   1 | echo ([ | | head |-> 0 | tail |-> f ])
     ^ parse error
  
  [1]
  $ agdarya -parametric errors.ny -e "echo (( fst ≔ a ) : Σ A B)"
   ￫ error[E0902]
   ￭ command-line exec string
   1 | echo (( fst ≔ a ) : Σ A B)
     ^ record field 'snd' missing in tuple
  
  [1]
  $ agdarya -parametric errors.ny -e "echo (( fst ≔ a ) : A)"
   ￫ error[E0900]
   ￭ command-line exec string
   1 | echo (( fst ≔ a ) : A)
     ^ checking tuple against non-record type A
  
  [1]
  $ agdarya -parametric errors.ny -e "echo (( fst ≔ a ) : ℕ)"
   ￫ error[E0900]
   ￭ command-line exec string
   1 | echo (( fst ≔ a ) : ℕ)
     ^ checking tuple against non-record type ℕ
  
  [1]
  $ agdarya -parametric errors.ny -e "echo (s third)"
   ￫ error[E0800]
   ￭ command-line exec string
   1 | echo (s third)
     ^ record type Σ has no field named third
  
  [1]
  $ agdarya -parametric errors.ny -e "echo (zero : Σ A B)"
   ￫ error[E1000]
   ￭ command-line exec string
   1 | echo (zero : Σ A B)
     ^ non-datatype Σ A B has no constructor named zero
  
  [1]
  $ agdarya -parametric errors.ny -e "echo (two : ℕ)"
   ￫ error[E0300]
   ￭ command-line exec string
   1 | echo (two : ℕ)
     ^ unbound variable: two
  
  [1]
  $ agdarya -parametric errors.ny -e "echo ((zero a) : ℕ)"
   ￫ error[E1001]
   ￭ command-line exec string
   1 | echo ((zero a) : ℕ)
     ^ too many arguments to constructor zero (1 extra)
  
  [1]
  $ agdarya -parametric errors.ny -e "echo ((suc ) : ℕ)"
   ￫ error[E1001]
   ￭ command-line exec string
   1 | echo ((suc ) : ℕ)
     ^ not enough arguments to constructor suc (need 1 more)
  
  [1]
  $ agdarya -parametric errors.ny -e "echo ((ungel ≔ r2) : symr2ty)"
   ￫ error[E0901]
   ￭ command-line exec string
   1 | echo ((ungel ≔ r2) : symr2ty)
     ^ can't check a tuple against a record Gel with a nonidentity degeneracy applied
  
  [1]
  $ agdarya -parametric errors.ny -e "echo (gg' ungel)"
   ￫ error[E0800]
   ￭ command-line exec string
   1 | echo (gg' ungel)
     ^ record type with a nonidentity degeneracy applied is no longer a record, hence has no field named ungel
  
  [1]
  $ agdarya -parametric errors.ny -e "echo ((x ↦ x⟨0⟩) : A -> A)"  
   ￫ error[E0506]
   ￭ command-line exec string
   1 | echo ((x ↦ x⟨0⟩) : A -> A)
     ^ invalid face: variable of dimension 0 has no face '0'
  
  [1]
  $ agdarya -parametric errors.ny -e "echo ((x ⤇ x) : A -> A)"
   ￫ error[E0508]
   ￭ command-line exec string
   1 | echo ((x ⤇ x) : A -> A)
     ^ cube abstraction not allowed for zero-dimensional function
  
  [1]
  $ agdarya -parametric errors.ny -e "echo ((x ↦ x) : Id (A→A) f f)"
   ￫ error[E0702]
   ￭ command-line exec string
   1 | echo ((x ↦ x) : Id (A→A) f f)
     ^ unexpected explicit abstraction: expecting implicit variable
  
  [1]
  $ agdarya -parametric errors.ny -e "echo ((a x ⤇ refl f {x.0} {x.1} x⟨2⟩) : A → Id (A→A) f f)"
   ￫ error[E0508]
   ￭ command-line exec string
   1 | echo ((a x ⤇ refl f {x.0} {x.1} x⟨2⟩) : A → Id (A→A) f f)
     ^ cube abstraction not allowed for zero-dimensional function
  
  [1]
  $ agdarya -parametric errors.ny -e "echo ((x ↦ x ⤇ x) : A → Id (A→A) f f)"
   ￫ error[E0401]
   ￭ command-line exec string
   1 | echo ((x ↦ x ⤇ x) : A → Id (A→A) f f)
     ^ term synthesized type
         Id A x′.0 x′.1
       but is being checked against type
         Id A (f x′.0) (f x′.1)
       unequal head terms:
         x′.0
       does not equal
         f
  
  [1]
  $ agdarya -parametric errors.ny -e "echo ((a x ⤇ refl af {a.0} {a.1} a⟨2⟩ {x.00} {x.01} {x.02} {x.10} {x.11} {x.12} {x.20} {x.21} x⟨22⟩) : Id (A → Id (A→A) f f) af af)"
   ￫ error[E0509]
   ￭ command-line exec string
   1 | echo ((a x ⤇ refl af {a.0} {a.1} a⟨2⟩ {x.00} {x.01} {x.02} {x.10} {x.11} {x.12} {x.20} {x.21} x⟨22⟩) : Id (A → Id (A→A) f f) af af)
     ^ previous variable
     ^ can't combine cube abstractions of different dimensions: e ≠ ee
  
  [1]
  $ agdarya -parametric errors.ny -e "echo ((n0 n1 n2 ↦ match n2 [ zero ↦ zero | suc n ↦ suc n⟨2⟩ ]) : (n0 n1 : ℕ) → Id ℕ n0 n1 → Id ℕ n0 n1)"
   ￫ error[E0510]
   ￭ command-line exec string
   1 | echo ((n0 n1 n2 ↦ match n2 [ zero ↦ zero | suc n ↦ suc n⟨2⟩ ]) : (n0 n1 : ℕ) → Id ℕ n0 n1 → Id ℕ n0 n1)
     ^ e-dimensional match requires cube abstraction
  
  [1]
  $ agdarya -parametric errors.ny -e "echo ((n0 n1 n2 ↦ match n2 [ zero ⤇ zero | suc n ↦ suc n⟨2⟩ ]) : (n0 n1 : ℕ) → Id ℕ n0 n1 → Id ℕ n0 n1)"
   ￫ error[E0510]
   ￭ command-line exec string
   1 | echo ((n0 n1 n2 ↦ match n2 [ zero ⤇ zero | suc n ↦ suc n⟨2⟩ ]) : (n0 n1 : ℕ) → Id ℕ n0 n1 → Id ℕ n0 n1)
     ^ e-dimensional match requires cube abstraction
  
  [1]
  $ agdarya -parametric errors.ny -e "echo ([ head ⤇ 0 | tail ↦ zeros ] : Stream ℕ)"
   ￫ error[E0217]
   ￭ command-line exec string
   1 | echo ([ head ⤇ 0 | tail ↦ zeros ] : Stream ℕ)
     ^ standalone bracket syntax removed; use λ { … } for matching lambdas or record { … } for codata values
  
  [1]
  $ agdarya -parametric errors.ny -e "echo ([ head ↦ 0 | tail ⤇ zeros ] : Stream ℕ)"
   ￫ error[E0217]
   ￭ command-line exec string
   1 | echo ([ head ↦ 0 | tail ⤇ zeros ] : Stream ℕ)
     ^ standalone bracket syntax removed; use λ { … } for matching lambdas or record { … } for codata values
  
  [1]
  $ agdarya -parametric errors.ny -e "echo x y {\` unterminated block comment"
   ￫ bug[E0000]
   ￮ anomaly: zero-width range during parse failure before EOF
  
  [1]
