  $ agdarya -parametric -v gel.ny
   ￫ info[I0000]
   ￮ constant Gel defined
  
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate B assumed
  
   ￫ info[I0001]
   ￮ postulate R assumed
  
   ￫ info[I0001]
   ￮ postulate a₀ assumed
  
   ￫ info[I0001]
   ￮ postulate a₁ assumed
  
   ￫ info[I0001]
   ￮ postulate a₂ assumed
  
   ￫ info[I0001]
   ￮ postulate b₀ assumed
  
   ￫ info[I0001]
   ￮ postulate b₁ assumed
  
   ￫ info[I0001]
   ￮ postulate b₂ assumed
  
   ￫ info[I0001]
   ￮ postulate r₀ assumed
  
   ￫ info[I0001]
   ￮ postulate r₁ assumed
  
   ￫ info[I0001]
   ￮ postulate M assumed
  
  sym M
    : Gel⁽ᵉ⁾ (Id A) (Id B) (Id R) a₂ b₂ (_ ≔ r₀) (_ ≔ r₁)
  
  sym M ungel
    : Id R a₂ b₂ r₀ r₁
  
   ￫ info[I0000]
   ￮ constant eta defined
  
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
  
   ￫ info[I0000]
   ￮ constant r_gelr2 defined
  
  r_gelr2
    : Set⁽ᵉᵉ⁾ A2 B2 (Gel A0 B0 R0) (Gel A1 B1 R1)
  
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
  
   ￫ info[I0000]
   ￮ constant r2ty defined
  
   ￫ info[I0001]
   ￮ postulate r2 assumed
  
   ￫ info[I0000]
   ￮ constant r_sym_gelr2 defined
  
  r_sym_gelr2
    : Set⁽ᵉᵉ⁾ (Gel A0 B0 R0) (Gel A1 B1 R1) A2 B2
  
   ￫ info[I0000]
   ￮ constant sym_r2ty defined
  
   ￫ info[I0001]
   ￮ postulate r2' assumed
  
  sym r2
    : sym (Gel⁽ᵉ⁾ A2 B2 R2) {a0} {b0} (ungel ≔ r0) {a1} {b1} (ungel ≔ r1) a2
        b2
  
  sym r2'
    : Gel⁽ᵉ⁾ A2 B2 R2 a2 b2 (ungel ≔ r0) (ungel ≔ r1)
  
   ￫ info[I0000]
   ￮ constant symsym_r2 defined
  
   ￫ info[I0000]
   ￮ constant symsym_r2_eq_r2 defined
  
   ￫ info[I0000]
   ￮ constant symsym_r2' defined
  
   ￫ info[I0000]
   ￮ constant symsym_r2'_eq_r2' defined
  
   ￫ warning[W2305]
   ￮ can't write compiled file: $TESTCASE_ROOT/gel.nyo
  

  $ agdarya -parametric gel.ny -e "r2ty_eq_sym_r2ty : Id Set r2ty sym_r2ty" -e "r2ty_eq_sym_r2ty = refl r2ty"
  sym M
    : Gel⁽ᵉ⁾ (Id A) (Id B) (Id R) a₂ b₂ (_ ≔ r₀) (_ ≔ r₁)
  
  sym M ungel
    : Id R a₂ b₂ r₀ r₁
  
  r_gelr2
    : Set⁽ᵉᵉ⁾ A2 B2 (Gel A0 B0 R0) (Gel A1 B1 R1)
  
  r_sym_gelr2
    : Set⁽ᵉᵉ⁾ (Gel A0 B0 R0) (Gel A1 B1 R1) A2 B2
  
  sym r2
    : sym (Gel⁽ᵉ⁾ A2 B2 R2) {a0} {b0} (ungel ≔ r0) {a1} {b1} (ungel ≔ r1) a2
        b2
  
  sym r2'
    : Gel⁽ᵉ⁾ A2 B2 R2 a2 b2 (ungel ≔ r0) (ungel ≔ r1)
  
   ￫ warning[W2305]
   ￮ can't write compiled file: $TESTCASE_ROOT/gel.nyo
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | r2ty_eq_sym_r2ty = refl r2ty
     ^ term synthesized type
         Set⁽ᵉ⁾ (Gel⁽ᵉ⁾ A2 B2 R2 a2 b2 (ungel ≔ r0) (ungel ≔ r1))
           (Gel⁽ᵉ⁾ A2 B2 R2 a2 b2 (ungel ≔ r0) (ungel ≔ r1))
       but is being checked against type
         Set⁽ᵉ⁾ (Gel⁽ᵉ⁾ A2 B2 R2 a2 b2 (ungel ≔ r0) (ungel ≔ r1))
           (sym (Gel⁽ᵉ⁾ A2 B2 R2) {a0} {b0} (ungel ≔ r0) {a1} {b1} (ungel ≔ r1) a2 b2)
       unequal terms:
         refl Gel A2 B2 R2 a2 b2 (ungel ≔ r0) (ungel ≔ r1)
       does not equal
         sym (refl Gel A2 B2 R2) {a0} {b0} (ungel ≔ r0) {a1} {b1} (ungel ≔ r1) a2 b2
  
  [1]
