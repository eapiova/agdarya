  $ agdarya -dtt -v sst.ny
   ￫ info[I0000]
   ￮ constant Gel defined
  
   ￫ info[I0000]
   ￮ constant SST defined
  
   ￫ info[I0000]
   ￮ constant 0s defined
  
   ￫ info[I0000]
   ￮ constant 1s defined
  
   ￫ info[I0000]
   ￮ constant 2s defined
  
   ￫ info[I0000]
   ￮ constant 3s defined
  
   ￫ info[I0000]
   ￮ constant eq defined
  
   ￫ info[I0000]
   ￮ constant Sing defined
  
   ￫ info[I0001]
   ￮ postulate A assumed
  
  A
    : Set
  
   ￫ info[I0001]
   ￮ postulate a₀ assumed
  
   ￫ info[I0001]
   ￮ postulate a₁ assumed
  
  Gel A (λ y → eq A a₀ y) a₁
    : Set
  
   ￫ info[I0001]
   ￮ postulate a₀₁ assumed
  
   ￫ info[I0001]
   ￮ postulate a₂ assumed
  
   ￫ info[I0001]
   ￮ postulate a₀₂ assumed
  
   ￫ info[I0001]
   ￮ postulate a₁₂ assumed
  
  Gel⁽ᵈ⁾ (Gel A (λ y → eq A a₀ y)) {λ y → eq A a₁ y}
    (y ⤇ eq⁽ᵈ⁾ (Gel A (λ y′ → eq A a₀ y′)) a₀₁ y.1) a₀₂ a₁₂
    : Set
  
   ￫ info[I0001]
   ￮ postulate a₀₁₂ assumed
  
   ￫ info[I0001]
   ￮ postulate a₃ assumed
  
   ￫ info[I0001]
   ￮ postulate a₀₃ assumed
  
   ￫ info[I0001]
   ￮ postulate a₁₃ assumed
  
   ￫ info[I0001]
   ￮ postulate a₀₁₃ assumed
  
   ￫ info[I0001]
   ￮ postulate a₂₃ assumed
  
   ￫ info[I0001]
   ￮ postulate a₀₂₃ assumed
  
   ￫ info[I0001]
   ￮ postulate a₁₂₃ assumed
  
  Gel⁽ᵈᵈ⁾
    (Gel⁽ᵈ⁾ (Gel A (λ y → eq A a₀ y)) {λ y → eq A a₁ y}
       (y ⤇ eq⁽ᵈ⁾ (Gel A (λ y′ → eq A a₀ y′)) a₀₁ y.1)) {λ y → eq A a₂ y}
    {y ⤇ eq⁽ᵈ⁾ (Gel A (λ y′ → eq A a₀ y′)) a₀₂ y.1}
    {y ⤇ eq⁽ᵈ⁾ (Gel A (λ y′ → eq A a₁ y′)) a₁₂ y.1}
    (y ⤇
     eq⁽ᵈᵈ⁾
       (Gel⁽ᵈ⁾ (Gel A (λ y′ → eq A a₀ y′)) {λ y′ → eq A a₁ y′}
          (y′ ⤇ eq⁽ᵈ⁾ (Gel A (λ y″ → eq A a₀ y″)) a₀₁ y′.1)) a₀₁₂ y.11) a₀₁₃
    a₀₂₃ a₁₂₃
    : Set
  
   ￫ info[I0000]
   ￮ constant sst.∅ defined
  
   ￫ info[I0000]
   ￮ constant sst.𝟙 defined
  
   ￫ info[I0000]
   ￮ constant sst_prod defined
  
   ￫ info[I0000]
   ￮ constant sst.Σ defined
  
   ￫ info[I0000]
   ￮ constant sst.const defined
  
   ￫ info[I0000]
   ￮ constant sst.sum defined
  
   ￫ info[I0000]
   ￮ constant ASST defined
  
   ￫ info[I0000]
   ￮ constant sst_pt defined
  
   ￫ info[I0000]
   ￮ constant sst.hom defined
  
   ￫ info[I0000]
   ￮ constant sst.id defined
  
   ￫ info[I0000]
   ￮ constant sst.comp defined
  
   ￫ info[I0000]
   ￮ constant sst.abort defined
  
   ￫ info[I0000]
   ￮ constant sst.uniq defined
  
   ￫ info[I0000]
   ￮ constant sst_pair defined
  
   ￫ info[I0000]
   ￮ constant sst.abortz defined
  
   ￫ info[I0000]
   ￮ constant sst.const_abort defined
  
   ￫ info[I0000]
   ￮ constant sst.copair defined
  
   ￫ warning[W2305]
   ￮ can't write compiled file: $TESTCASE_ROOT/sst.nyo
  

  $ agdarya -parametric -arity 2 -direction p -external -v sct.ny
   ￫ info[I0000]
   ￮ constant SCT defined
  
   ￫ info[I0000]
   ￮ constant 0s defined
  
   ￫ info[I0000]
   ￮ constant 1s defined
  
   ￫ info[I0000]
   ￮ constant 2s defined
  
  $ agdarya -dtt -e "foo : (X:Set) → Set^^(d) X" -e "foo X = X^^(d)"
   ￫ error[E0310]
   ￭ command-line exec string
   1 | foo X = X^^(d)
     ^ variable not available inside external degeneracy
  
  [1]

Can't take external degeneracies of nonparametric axioms.

  $ agdarya -dtt -v -e "postulate #(nonparametric) A : Set" -e "echo A⁽ᵈ⁾"
   ￫ info[I0001]
   ￮ nonparametric postulate A assumed
  
   ￫ error[E0311]
   ￭ command-line exec string
   1 | echo A⁽ᵈ⁾
     ^ constant A is or uses a nonparametric postulate, can't appear inside an external degeneracy
  
  [1]

Or of anything that uses a nonparametric postulate.

  $ agdarya -dtt -v -e "postulate #(nonparametric) A : Set" -e "f : A → A" -e "f x = x" -e "echo f⁽ᵈ⁾"
   ￫ info[I0001]
   ￮ nonparametric postulate A assumed
  
   ￫ info[I0000]
   ￮ nonparametric constant f defined
  
   ￫ error[E0311]
   ￭ command-line exec string
   1 | echo f⁽ᵈ⁾
     ^ constant f is or uses a nonparametric postulate, can't appear inside an external degeneracy
  
  [1]

All axioms using a nonparametric postulate must also be nonparametric

  $ agdarya -dtt -v -e "postulate #(nonparametric) A : Set postulate #(nonparametric) a : A postulate a' : A"
   ￫ info[I0001]
   ￮ nonparametric postulate A assumed
  
   ￫ info[I0001]
   ￮ nonparametric postulate a assumed
  
   ￫ error[E0312]
   ￭ command-line exec string
   1 | postulate #(nonparametric) A : Set postulate #(nonparametric) a : A postulate a' : A
     ^ constant A is or uses a nonparametric postulate, can't be used in a parametric command
  
  [1]


We check that a family of mutual definitions can apply external degeneracies to each other.  This was an issue once because they are temporarily defined as "axioms" during definition, and by default axioms don't admit external degeneracies.

  $ agdarya -dtt -v -e "X : Set" -e "X = Set" -e "Y : (x : X) → X⁽ᵈ⁾ x" -e "Y x = ?"
   ￫ info[I0000]
   ￮ constant X defined
  
   ￫ info[I0000]
   ￮ constant Y defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     x : Set
     ----------------------------------------------------------------------
     Set⁽ᵈ⁾ x
  
   ￫ error[E3002]
   ￮ command-line exec string contains open holes
  
  [1]

But if one of them uses an postulate, the others don't have external degeneracies either.

  $ agdarya -dtt -v -e "postulate #(nonparametric) A:Set" -e "f : Set" -e "f = A" -e "g : Set" -e "g = sig ()" -e "echo g⁽ᵈ⁾"
   ￫ info[I0001]
   ￮ nonparametric postulate A assumed
  
   ￫ info[I0000]
   ￮ nonparametric constant f defined
  
   ￫ info[I0000]
   ￮ constant g defined
  
  g⁽ᵈ⁾
    : Set⁽ᵈ⁾ g
  

When a constant is defined containing a hole, it is allowed to be parametric, but then the hole cannot be filled by any term that uses an postulate.

  $ agdarya -dtt -v -fake-interact "postulate #(nonparametric) A:Set" "B : Set" "B = ?" "echo B⁽ᵈ⁾" "solve 0 := A"
   ￫ error[E2302]
   ￮ filename 'B : Set' does not have 'ny' extension
  
  [1]
