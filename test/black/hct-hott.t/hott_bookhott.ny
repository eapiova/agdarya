{- -*- agdarya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br") -*- -}

import "isfibrant"
import "bookhott"

{- Facts about the interaction of Book HoTT equivalences (regarded as the outer 2LTT layer) and HOTT identity types. -}

{- An Id of equalities induces an equality involving transport -}
Id_eq : (A0 A1 : Set) → (A2 : Br Set A0 A1) → (a00 : A0) → (a01 : A1) → (a02 : A2 a00 a01) → (a10 : A0) → (a11 : A1) → (a12 : A2 a10 a11) → (a20 : eq A0 a00 a10) → (a21 : eq A1 a01 a11) → (a22 : Br eq A2 a02 a12 a20 a21) → eq (A2 a10 a11)
      (eq.trr2 A0 A1 (x y ↦ A2 x y) a00 a10 a20 a01 a11 a21 a02) a12
Id_eq A0 A1 A2 a00 a01 a02 a10 a11 a12 a20 a21 a22 = match a22 [ eq.rfl ⤇ eq.rfl ]

{- An Id of equivalences induces an equivalence on Ids. -}
Id_eqv : (A0 : Set) → (A1 : Set) → (A2 : Br Set A0 A1) → (B0 : Set) → (B1 : Set) → (B2 : Br Set B0 B1) → (e0 : A0 ≅ B0) → (e1 : A1 ≅ B1) → (e2 : Br eqv A2 B2 e0 e1) → (b0 : B0) → (b1 : B1) → A2 (e0 fro b0) (e1 fro b1) ≅ B2 b0 b1
Id_eqv A0 A1 A2 B0 B1 B2 e0 e1 e2 b0 b1 = let f0 ≔ e0 to in
  let g0 ≔ e0 fro in
  let ap_g0 ≔ eq.ap B0 A0 g0 in
  let fg0 : B0 → B0 ≔ x ↦ f0 (g0 x) in
  let gfg0 : B0 → A0 ≔ x ↦ g0 (f0 (g0 x)) in
  let ε0 ≔ e0 to_fro in
  let η0 ≔ e0 fro_to in
  let f1 ≔ e1 to in
  let g1 ≔ e1 fro in
  let ap_g1 ≔ eq.ap B1 A1 g1 in
  let fg1 : B1 → B1 ≔ x ↦ f1 (g1 x) in
  let gfg1 : B1 → A1 ≔ x ↦ g1 (f1 (g1 x)) in
  let ε1 ≔ e1 to_fro in
  let η1 ≔ e1 fro_to in
  let f2 ≔ e2 to in
  let g2 ≔ e2 fro in
  let η2 ≔ e2 fro_to in
  let ε2 ≔ e2 to_fro in
  adjointify (A2 (g0 b0) (g1 b1)) (B2 b0 b1)
    (a2 ↦
     eq.trr2 B0 B1 (b0 b1 ↦ B2 b0 b1) (fg0 b0) b0 (ε0 b0) (fg1 b1) b1
       (ε1 b1) (f2 a2)) (b2 ↦ g2 b2)
    (a2 ↦
     eq.cat (A2 (g0 b0) (g1 b1))
       (g2
          (eq.trr2 B0 B1 (x y ↦ B2 x y) (fg0 b0) b0 (ε0 b0) (fg1 b1) b1
             (ε1 b1) (f2 a2)))
       (eq.trr2 A0 A1 (x y ↦ A2 x y) (gfg0 b0) (g0 b0)
          (ap_g0 (fg0 b0) b0 (ε0 b0)) (gfg1 b1) (g1 b1)
          (ap_g1 (fg1 b1) b1 (ε1 b1)) (g2 (f2 a2))) a2
       (eq.trr2_ap B0 B1 (x y ↦ B2 x y) A0 A1 (x y ↦ A2 x y) g0 g1
          (x0 x1 x2 ↦ g2 x2) (fg0 b0) b0 (ε0 b0) (fg1 b1) b1 (ε1 b1)
          (f2 a2))
       (Id_eq A0 A1 A2 (gfg0 b0) (gfg1 b1) (g2 (f2 a2)) (g0 b0) (g1 b1) a2
          (ap_g0 (fg0 b0) b0 (ε0 b0)) (ap_g1 (fg1 b1) b1 (ε1 b1))
          (eq.trl2 (eq A0 (gfg0 b0) (g0 b0)) (eq A1 (gfg1 b1) (g1 b1))
             (u v ↦ Br eq A2 (g2 (f2 a2)) a2 u v)
             (ap_g0 (fg0 b0) b0 (ε0 b0)) (η0 (g0 b0))
             (fro_to_fro A0 B0 e0 b0) (ap_g1 (fg1 b1) b1 (ε1 b1))
             (η1 (g1 b1)) (fro_to_fro A1 B1 e1 b1) (η2 a2))))
    (b2 ↦
     Id_eq B0 B1 B2 (fg0 b0) (fg1 b1) (f2 (g2 b2)) b0 b1 b2 (ε0 b0) (ε1 b1)
       (ε2 b2))

{- Fibrancy transports across equivalences. -}
𝕗eqv : (A B : Set) → (e : A ≅ B) → (𝕗A : isFibrant A) → isFibrant B
𝕗eqv A B e 𝕗A = record {
  trr⟨p⟩ = λ b0 → e⟨1⟩ to (𝕗A.2 trr (e.0 fro b0));
  trl⟨p⟩ = λ b1 → e⟨0⟩ to (𝕗A.2 trl (e.1 fro b1));
  liftr⟨p⟩ = λ b0 →
    eq.trr B.0 (b ↦ B.2 b (e.1 to (𝕗A.2 trr (e.0 fro b0))))
      (e.0 to (e.0 fro b0)) b0 (e.0 to_fro b0)
      (e.2 to (𝕗A.2 liftr (e.0 fro b0)));
  liftl⟨p⟩ = λ b1 →
    eq.trr B.1 (b ↦ B.2 (e.0 to (𝕗A.2 trl (e.1 fro b1))) b)
      (e.1 to (e.1 fro b1)) b1 (e.1 to_fro b1)
      (e.2 to (𝕗A.2 liftl (e.1 fro b1)));
  id⟨p⟩ = λ b0 b1 →
    𝕗eqv (A.2 (e.0 fro b0) (e.1 fro b1)) (B.2 b0 b1)
      (Id_eqv A.0 A.1 A.2 B.0 B.1 B.2 e⟨0⟩ e⟨1⟩ e⟨2⟩ b0 b1)
      (𝕗A.2 id (e.0 fro b0) (e.1 fro b1)) }

{- Symmetry is an equivalence -}
sym_eqv : (A00 A01 : Set) → (A02 : Br Set A00 A01) → (A10 A11 : Set) → (A12 : Br Set A10 A11) → (A20 : Br Set A00 A10) → (A21 : Br Set A01 A11) → (A22 : Br (Br Set) A02 A12 A20 A21) → (a00 : A00) → (a01 : A01) → (a02 : A02 a00 a01) → (a10 : A10) → (a11 : A11) → (a12 : A12 a10 a11) → (a20 : A20 a00 a10) → (a21 : A21 a01 a11) → A22 a02 a12 a20 a21 ≅ sym A22 a20 a21 a02 a12
sym_eqv A00 A01 A02 A10 A11 A12 A20 A21 A22 a00 a01 a02 a10 a11 a12 a20 a21 = (
  to ≔ a22 ↦ sym a22,
  fro ≔ a22 ↦ sym a22,
  to_fro ≔ _ ↦ eq.rfl,
  fro_to ≔ _ ↦ eq.rfl,
  to_fro_to ≔ _ ↦ eq.rfl)

312_eqv : (A000 : Set) → (A001 : Set) → (A002 : Br Set A000 A001)
  → (A010 : Set) → (A011 : Set) → (A012 : Br Set A010 A011)
  → (A020 : Br Set A000 A010) → (A021 : Br Set A001 A011)
  → (A022 : Br (Br Set) A002 A012 A020 A021)
  → {- Top face -} (A100 : Set) → (A101 : Set) → (A102 : Br Set A100 A101)
  → (A110 : Set) → (A111 : Set) → (A112 : Br Set A110 A111)
  → (A120 : Br Set A100 A110) → (A121 : Br Set A101 A111)
  → (A122 : Br (Br Set) A102 A112 A120 A121)
  → {- Front face -} (A200 : Br Set A000 A100) → (A201 : Br Set A001 A101)
  → (A202 : Br (Br Set) A002 A102 A200 A201)
  → {- Back face -} (A210 : Br Set A010 A110) → (A211 : Br Set A011 A111)
  → (A212 : Br (Br Set) A012 A112 A210 A211)
  → {- Left face -} (A220 : Br (Br Set) A020 A120 A200 A210)
  → {- Right face -} (A221 : Br (Br Set) A021 A121 A201 A211)
  → {- Center -} (A222 : Br (Br (Br Set)) A022 A122 A202 A212 A220 A221)
  → (a000 : A000) → (a001 : A001) → (a002 : A002 a000 a001)
  → (a010 : A010) → (a011 : A011) → (a012 : A012 a010 a011)
  → (a020 : A020 a000 a010) → (a021 : A021 a001 a011)
  → (a022 : A022 a002 a012 a020 a021)
  → {- Top face -} (a100 : A100) → (a101 : A101) → (a102 : A102 a100 a101)
  → (a110 : A110) → (a111 : A111) → (a112 : A112 a110 a111)
  → (a120 : A120 a100 a110) → (a121 : A121 a101 a111)
  → (a122 : A122 a102 a112 a120 a121)
  → {- Front face -} (a200 : A200 a000 a100) → (a201 : A201 a001 a101)
  → (a202 : A202 a002 a102 a200 a201)
  → {- Back face -} (a210 : A210 a010 a110) → (a211 : A211 a011 a111)
  → (a212 : A212 a012 a112 a210 a211)
  → {- Left face -} (a220 : A220 a020 a120 a200 a210)
  → {- Right face -} (a221 : A221 a021 a121 a201 a211)
  → A222 a022 a122 a202 a212 a220 a221
  ≅ A222⁽³¹²⁾ a220 a221 (sym a022) (sym a122) (sym a202) (sym a212)
312_eqv =
  λ A000 A001 A002 A010 A011 A012 A020 A021 A022
    A100 A101 A102 A110 A111 A112 A120 A121 A122
    A200 A201 A202
    A210 A211 A212
    A220 A221
    A222 a000 a001 a002 a010 a011 a012 a020 a021 a022
    a100 a101 a102 a110 a111 a112 a120 a121 a122
    a200 a201 a202
    a210 a211 a212
    a220 a221 →
  (
  to ≔ a222 ↦ a222⁽³¹²⁾,
  fro ≔ a222 ↦ a222⁽²³¹⁾,
  to_fro ≔ _ ↦ eq.rfl,
  fro_to ≔ _ ↦ eq.rfl,
  to_fro_to ≔ _ ↦ eq.rfl)
