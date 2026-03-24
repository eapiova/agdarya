  $ agdarya -parametric -v holes.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate B assumed
  
  B
    : Set
  
   ￫ info[I0000]
   ￮ constant id defined
  
   ￫ info[I0001]
   ￮ postulate b assumed
  
   ￫ info[I0001]
   ￮ postulate g assumed
  
   ￫ info[I0000]
   ￮ constant f defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     ----------------------------------------------------------------------
     A → B
  
   ￫ info[I0001]
   ￮ postulate a_very_long_variable assumed
  
   ￫ info[I0001]
   ￮ postulate a_very_long_function assumed
  
   ￫ info[I0000]
   ￮ constant f' defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?1:
     
     ----------------------------------------------------------------------
     A → B
  
   ￫ info[I0007]
   ￮ section sec opened
  
   ￫ info[I0002]
   ￮ notation «&» defined
  
   ￫ info[I0000]
   ￮ constant f' defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?2:
     
     ----------------------------------------------------------------------
     A → B
  
   ￫ info[I0008]
   ￮ section sec closed
  
   ￫ info[I0002]
   ￮ notation «$» defined
  
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant plus defined, containing 2 holes
  
   ￫ info[I3003]
   ￮ hole ?3:
     
     m : ℕ
     n ≔ 0 : ℕ
     ----------------------------------------------------------------------
     ℕ
  
   ￫ info[I3003]
   ￮ hole ?4:
     
     m : ℕ
     n : ℕ
     n′ ≔ suc n : ℕ (not in scope)
     ----------------------------------------------------------------------
     ℕ
  
   ￫ info[I0001]
   ￮ postulate P assumed
  
   ￫ info[I0000]
   ￮ constant anop defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?5:
     
     n″ : ℕ (not in scope)
     n′ : ℕ
     n : ℕ
     ----------------------------------------------------------------------
     P n
  
   ￫ info[I0000]
   ￮ constant anop' defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?6:
     
     n′ : ℕ
     n″ : ℕ (not in scope)
     n : ℕ
     ----------------------------------------------------------------------
     P n
  
   ￫ info[I0000]
   ￮ constant anop'' defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?7:
     
     n′ : ℕ (not in scope)
     𝑥 : ℕ (not in scope)
     n : ℕ
     ----------------------------------------------------------------------
     P n
  
   ￫ info[I0000]
   ￮ constant anop''' defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?8:
     
     𝑥 : ℕ
     𝑦 : ℕ (not in scope)
     n : ℕ
     ----------------------------------------------------------------------
     P n
  
   ￫ info[I0000]
   ￮ constant Σ defined
  
   ￫ info[I0000]
   ￮ constant pp defined, containing 2 holes
  
   ￫ info[I3003]
   ￮ hole ?9:
     
     ----------------------------------------------------------------------
     Set
  
   ￫ info[I3003]
   ￮ hole ?10:
     
     ----------------------------------------------------------------------
     pp fst
  
   ￫ info[I0000]
   ￮ constant pp' defined, containing 2 holes
  
   ￫ info[I3003]
   ￮ hole ?11:
     
     ----------------------------------------------------------------------
     Set
  
   ￫ info[I3003]
   ￮ hole ?12:
     
     ----------------------------------------------------------------------
     ?11{…}
  
   ￫ info[I0000]
   ￮ constant foo defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?13:
     
     bar : ℕ
     ----------------------------------------------------------------------
     Set
  
   ￫ info[I0000]
   ￮ constant foo' defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?14:
     
     bar : Set
     x : bar
     ----------------------------------------------------------------------
     Set
  
   ￫ info[I0000]
   ￮ constant gel0 defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?15:
     
     A : Set
     B : Set
     x : A
     y : B
     ----------------------------------------------------------------------
     Set
  
   ￫ info[I0000]
   ￮ constant gel1 defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?16:
     
     A : Set
     B : Set
     x : A
     y : B
     one : Set
     ----------------------------------------------------------------------
     Set
  
   ￫ info[I0000]
   ￮ constant gel2 defined, containing 2 holes
  
   ￫ info[I3003]
   ￮ hole ?17:
     
     A : Set
     B : Set
     x : A
     y : B
     ----------------------------------------------------------------------
     Set
  
   ￫ info[I3003]
   ￮ hole ?18:
     
     A : Set
     B : Set
     x : A
     y : B
     one : ?17{…}
     ----------------------------------------------------------------------
     Set
  
   ￫ info[I0000]
   ￮ constant gel3 defined, containing 2 holes
  
   ￫ info[I3003]
   ￮ hole ?19:
     
     A : Set
     B : Set
     x.0 : A
     x.1 : B
     x.2 : gel3 A B x.0 x.1
     ----------------------------------------------------------------------
     Set
  
   ￫ info[I3003]
   ￮ hole ?20:
     
     A : Set
     B : Set
     x.0 : A
     x.1 : B
     x.2 : gel3 A B x.0 x.1
     ----------------------------------------------------------------------
     Set
  
   ￫ info[I0001]
   ￮ postulate C assumed
  
   ￫ info[I0000]
   ￮ constant AC defined
  
   ￫ info[I0000]
   ￮ constant ac defined, containing 2 holes
  
   ￫ info[I3003]
   ￮ hole ?21:
     
     ----------------------------------------------------------------------
     ℕ → A
  
   ￫ info[I3003]
   ￮ hole ?22:
     
     ----------------------------------------------------------------------
     C (ac a 0)
  
   ￫ info[I0000]
   ￮ constant ida defined
  
   ￫ info[I0000]
   ￮ constant ideqid defined
  
  λ u u′ u″ → u″
    : {𝑥₀ : A} {𝑥₁ : A} (𝑥₂ : Id A 𝑥₀ 𝑥₁) →⁽ᵉ⁾ Id A 𝑥₀ 𝑥₁
  
   ￫ info[I0000]
   ￮ constant ideqid' defined
  
  λ u u′ u′′ → u′′
    : {𝑥₀ : A} {𝑥₁ : A} (𝑥₂ : Id A 𝑥₀ 𝑥₁) →⁽ᵉ⁾ Id A 𝑥₀ 𝑥₁
  
   ￫ info[I0000]
   ￮ constant ideqid'' defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?23:
     
     u″ : A (not in scope)
     u′ : A (not in scope)
     u : Id A u″ u′
     ----------------------------------------------------------------------
     refl A u″ u′
  
   ￫ info[I0000]
   ￮ constant afam defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?24:
     
     X : Set
     ----------------------------------------------------------------------
     Set
  
   ￫ info[I0000]
   ￮ constant idafam defined
  
   ￫ info[I0001]
   ￮ postulate f0 assumed
  
   ￫ info[I0000]
   ￮ constant f2 defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?25:
     
     x.0 : A
     x.1 : A
     x.2 : Id A x.0 x.1
     ----------------------------------------------------------------------
     refl B (f0 x.0) (f0 x.1)
  
   ￫ info[I0000]
   ￮ constant prod defined
  
   ￫ info[I0000]
   ￮ constant p defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?26:
     
     ----------------------------------------------------------------------
     prod
  
   ￫ info[I0001]
   ￮ postulate p0 assumed
  
   ￫ info[I0000]
   ￮ constant p2 defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?27:
     
     ----------------------------------------------------------------------
     refl prod p0 p0
  
   ￫ info[I0000]
   ￮ constant prod' defined
  
   ￫ warning[E2100]
   ￭ $TESTCASE_ROOT/holes.ny
   1 | p : prod'
     ^ redefining constant: p
   ￭ $TESTCASE_ROOT/holes.ny
   1 | p : prod
     ^ previous definition
  
   ￫ info[I0000]
   ￮ constant p defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?28:
     
     ----------------------------------------------------------------------
     prod'
  
   ￫ error[E3002]
   ￮ file holes.ny contains open holes
  
  [1]

  $ agdarya -v -dtt dtt-holes.ny
   ￫ info[I0000]
   ￮ constant f defined
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/dtt-holes.ny
   1 | g X = (f ?)⁽ᵈ⁾
     ^ term synthesized type
         Set⁽ᵈ⁾ ?0{…}
       but is being checked against type
         Set⁽ᵈ⁾ X
       unequal head terms:
         ?0{…}
       does not equal
         X
  
  [1]

Holes in echo:

  $ agdarya -e 'echo (? : Set)'
  ?0{…}
    : Set
  
   ￫ error[E3002]
   ￮ command-line exec string contains open holes
  
  [1]

No holes in imported file

  $ echo 'A : Set' >to_import.ny
  $ echo 'A = ?' >>to_import.ny

  $ agdarya -e 'import "to_import"'
   ￫ error[E2002]
   ￭ $TESTCASE_ROOT/to_import.ny
   1 | A = ?
     ^ imported file '$TESTCASE_ROOT/to_import.ny' cannot contain holes
  
  [1]
