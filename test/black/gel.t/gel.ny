 {- -*- agdarya-prog-args: ("-proofgeneral" "-parametric") -*- -}

Gel : (A B : Set) → (R : A → B → Set) → Id Set A B

Gel A B R = sig a b ↦ ( ungel : R a b )

postulate A : Set

postulate B : Set

postulate R : A → B → Set

postulate a₀ : A

postulate a₁ : A

postulate a₂ : Id A a₀ a₁

postulate b₀ : B

postulate b₁ : B

postulate b₂ : Id B b₀ b₁

postulate r₀ : R a₀ b₀

postulate r₁ : R a₁ b₁ {- An intrinsic symmetry of a higher-dimensional Gel is no longer a record type -}

postulate M : (Gel A B R)⁽ᵉ¹⁾ {a₀} {b₀} (r₀,) {a₁} {b₁} (r₁,) a₂ b₂

echo sym M

echo sym M ungel {- And it satisfies an eta-rule inherited from that record type -}

eta : Id ((Gel A B R)⁽ᵉ¹⁾ {a₀} {b₀} (r₀,) {a₁} {b₁} (r₁,) a₂ b₂) M
        (sym (ungel ≔ sym M ungel))

eta = refl M {- refl of Gel builds a square of correspondences-}

postulate A0 : Set

postulate B0 : Set

postulate R0 : A0 → B0 → Set

postulate A1 : Set

postulate B1 : Set

postulate R1 : A1 → B1 → Set

postulate A2 : Id Set A0 A1

postulate B2 : Id Set B0 B1

postulate R2 : refl ((X ↦ Y ↦ (X → Y → Set)) : Set → Set → Set) A2 B2 R0 R1

r_gelr2 = refl Gel A2 B2 R2

synth r_gelr2 {-We can apply it to some points.-}

postulate a0 : A0

postulate a1 : A1

postulate a2 : A2 a0 a1

postulate b0 : B0

postulate b1 : B1

postulate b2 : B2 b0 b1

postulate r0 : R0 a0 b0

postulate r1 : R1 a1 b1

r2ty = r_gelr2 a2 b2 (ungel ≔ r0) (ungel ≔ r1)

postulate r2 : r2ty

r_sym_gelr2 = sym (refl Gel A2 B2 R2)

synth r_sym_gelr2 {-This doesn't compute to anything: the symmetry is "stuck" as an insertion outside the Gel.  In particular, it is a different type (see the comments below two synth commands above), which can be applied to the same points in transposed order.-}

sym_r2ty = r_sym_gelr2 {a0} {b0} (ungel ≔ r0) {a1} {b1} (ungel ≔ r1) a2 b2

postulate r2' : sym_r2ty {-However, it is *isomorphic* to the original double span, by symmetry again.-}

echo (sym r2 : sym_r2ty)

echo (sym r2' : r2ty)

symsym_r2 = sym (sym r2)

symsym_r2_eq_r2 : Id r2ty symsym_r2 r2

symsym_r2_eq_r2 = refl r2

symsym_r2' = sym (sym r2')

symsym_r2'_eq_r2' : Id r2ty symsym_r2 r2

symsym_r2'_eq_r2' = refl r2
