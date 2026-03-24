{- -*- agdarya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br") -*- -}

import "isfibrant"
import "bookhott"
import "hott_bookhott"

{- Since identity types compute only up to definitional isomorphism, in order to prove that anything is fibrant by corecursion, we need to be able to transport fibrancy across definitional isomorphisms.  In fact, we can transport it across any Book-HoTT equivalence defined using the Martin-Lof identity type. -}

{- The unit type -}

⊤ : Set
⊤ = sig ()

id_⊤_iso : (x y : ⊤) → ⊤ ≅ Br ⊤ x y
id_⊤_iso x y = (
  to ≔ _ ↦ (),
  fro ≔ _ ↦ (),
  to_fro ≔ _ ↦ eq.rfl,
  fro_to ≔ _ ↦ eq.rfl,
  to_fro_to ≔ _ ↦ eq.rfl)

𝕗⊤ : isFibrant ⊤
𝕗⊤ = record {
  trr⟨p⟩ = λ x → x;
  trl⟨p⟩ = λ x → x;
  liftr⟨p⟩ = λ _ → ();
  liftl⟨p⟩ = λ _ → ();
  id⟨p⟩ = λ x y → 𝕗eqv ⊤ (Br ⊤ x y) (id_⊤_iso x y) 𝕗⊤ }

{- Product types -}

prod : (A B : Set) → Set
prod A B = sig ( fst : A, snd : B )

notation(2) A "×" B ≔ prod A B

id_prod_iso : (A0 : Set) → (A1 : Set) → (A2 : Br Set A0 A1) → (B0 : Set) → (B1 : Set) → (B2 : Br Set B0 B1) → (a0 : A0) → (a1 : A1) → (b0 : B0) → (b1 : B1) → A2 a0 a1 × B2 b0 b1 ≅ Br prod A2 B2 (a0, b0) (a1, b1)
id_prod_iso A0 A1 A2 B0 B1 B2 a0 a1 b0 b1 = (
  to ≔ u ↦ (u fst, u snd),
  fro ≔ v ↦ (v fst, v snd),
  to_fro ≔ _ ↦ eq.rfl,
  fro_to ≔ _ ↦ eq.rfl,
  to_fro_to ≔ _ ↦ eq.rfl)

𝕗prod : (A B : Set) → (𝕗A : isFibrant A) → (𝕗B : isFibrant B) → isFibrant (A × B)
𝕗prod A B 𝕗A 𝕗B = record {
  trr⟨p⟩ = λ u0 → (𝕗A.2 trr (u0 fst), 𝕗B.2 trr (u0 snd));
  trl⟨p⟩ = λ u1 → (𝕗A.2 trl (u1 fst), 𝕗B.2 trl (u1 snd));
  liftr⟨p⟩ = λ u0 → (𝕗A.2 liftr (u0 fst), 𝕗B.2 liftr (u0 snd));
  liftl⟨p⟩ = λ u1 → (𝕗A.2 liftl (u1 fst), 𝕗B.2 liftl (u1 snd));
  id⟨p⟩ = λ u0 u1 →
    𝕗eqv (A.2 (u0 fst) (u1 fst) × B.2 (u0 snd) (u1 snd))
      (rel prod A.2 B.2 u0 u1)
      (id_prod_iso A.0 A.1 A.2 B.0 B.1 B.2 (u0 fst) (u1 fst) (u0 snd)
         (u1 snd))
      (𝕗prod (A.2 (u0 fst) (u1 fst)) (B.2 (u0 snd) (u1 snd))
         (𝕗A.2 id (u0 fst) (u1 fst)) (𝕗B.2 id (u0 snd) (u1 snd))) }

{- Σ-types -}

Σ : (A : Set) → (B : A → Set) → Set
Σ A B = sig ( fst : A, snd : B fst )

id_Σ_iso : (A0 : Set) → (A1 : Set) → (A2 : Br Set A0 A1) → (B0 : A0 → Set) → (B1 : A1 → Set) → (B2 : (A2 ⇒ rel Set) B0 B1) → (a0 : A0) → (a1 : A1) → (b0 : B0 a0) → (b1 : B1 a1) → Σ (A2 a0 a1) (a2 ↦ B2 a2 b0 b1) ≅ Br Σ A2 B2 (a0, b0) (a1, b1)
id_Σ_iso A0 A1 A2 B0 B1 B2 a0 a1 b0 b1 = (
  to ≔ u ↦ (u fst, u snd),
  fro ≔ v ↦ (v fst, v snd),
  to_fro ≔ _ ↦ eq.rfl,
  fro_to ≔ _ ↦ eq.rfl,
  to_fro_to ≔ _ ↦ eq.rfl)

𝕗Σ : (A : Set) → (B : A → Set) → (𝕗A : isFibrant A) → (𝕗B : (x : A) → isFibrant (B x)) → isFibrant (Σ A B)
𝕗Σ A B 𝕗A 𝕗B = record {
  trr⟨p⟩ = λ u0 → (
    𝕗A.2 trr (u0 fst),
    𝕗B.2 (𝕗A.2 liftr (u0 fst)) trr (u0 snd));
  trl⟨p⟩ = λ u1 → (
    𝕗A.2 trl (u1 fst),
    𝕗B.2 (𝕗A.2 liftl (u1 fst)) trl (u1 snd));
  liftr⟨p⟩ = λ u0 → (
    𝕗A.2 liftr (u0 fst),
    𝕗B.2 (𝕗A.2 liftr (u0 fst)) liftr (u0 snd));
  liftl⟨p⟩ = λ u1 → (
    𝕗A.2 liftl (u1 fst),
    𝕗B.2 (𝕗A.2 liftl (u1 fst)) liftl (u1 snd));
  id⟨p⟩ = λ u0 u1 →
    𝕗eqv (Σ (A.2 (u0 fst) (u1 fst)) (a2 ↦ B.2 a2 (u0 snd) (u1 snd)))
      (Br Σ A.2 B.2 u0 u1)
      (id_Σ_iso A.0 A.1 A.2 B.0 B.1 B.2 (u0 fst) (u1 fst) (u0 snd) (u1 snd))
      (𝕗Σ (A.2 (u0 fst) (u1 fst)) (a2 ↦ B.2 a2 (u0 snd) (u1 snd))
         (𝕗A.2 id (u0 fst) (u1 fst)) (a2 ↦ 𝕗B.2 a2 id (u0 snd) (u1 snd))) }

{- Fibrant Σ-types -}
Σ𝕗 : (A : Fib) → (B : A t → Fib) → Fib
Σ𝕗 A B = (
  t ≔ Σ (A t) (a ↦ B a t),
  f ≔ 𝕗Σ (A t) (a ↦ B a t) (A f) (a ↦ B a f))

{- Π-types -}

Π : (A : Set) → (B : A → Set) → Set
Π A B = (x : A) → B x

id_Π_iso : (A0 : Set) → (A1 : Set) → (A2 : Br Set A0 A1) → (B0 : A0 → Set) → (B1 : A1 → Set) → (B2 : Br Π A2 {_ ↦ Set} {_ ↦ Set} (_ ⤇ rel Set) B0 B1) → (f0 : (a0 : A0) → B0 a0) → (f1 : (a1 : A1) → B1 a1) → ((a0 : A0) (a1 : A1) (a2 : A2 a0 a1) → B2 a2 (f0 a0) (f1 a1))
    ≅ Br Π A2 B2 f0 f1
id_Π_iso A0 A1 A2 B0 B1 B2 f0 f1 = (
  to ≔ f ↦ a ⤇ f a⟨0⟩ a⟨1⟩ a⟨2⟩,
  fro ≔ g ↦ a0 a1 a2 ↦ g a2,
  to_fro ≔ _ ↦ eq.rfl,
  fro_to ≔ _ ↦ eq.rfl,
  to_fro_to ≔ _ ↦ eq.rfl)

𝕗Π : (A : Set) → (B : A → Set) → (𝕗A : isFibrant A) → (𝕗B : (x : A) → isFibrant (B x)) → isFibrant ((x : A) → B x)
𝕗Π A B 𝕗A 𝕗B = record {
  trr⟨p⟩ = λ f0 a1 → 𝕗B.2 (𝕗A.2 liftl a1) trr (f0 (𝕗A.2 trl a1));
  trl⟨p⟩ = λ f1 a0 → 𝕗B.2 (𝕗A.2 liftr a0) trl (f1 (𝕗A.2 trr a0));
  liftr⟨p⟩ = λ f0 → a ⤇
    rel 𝕗B.2
        (sym (sym (rel 𝕗A.2) id⟨1⟩ a⟨2⟩ (𝕗A.2 liftl a⟨1⟩) liftl (rel a⟨1⟩)))
      id⟨1⟩ (rel f0 (𝕗A.2⁽ᵖ¹⁾ id⟨1⟩ a⟨2⟩ (𝕗A.2 liftl a⟨1⟩) trl (rel a⟨1⟩)))
        (rel (𝕗B.2 (𝕗A.2 liftl a⟨1⟩) trr (f0 (𝕗A.2 trl a⟨1⟩)))) trl
        (𝕗B.2 (𝕗A.2 liftl a⟨1⟩) liftr (f0 (𝕗A.2 trl a⟨1⟩)));
  liftl⟨p⟩ = λ f1 → a ⤇
    rel 𝕗B.2
        (sym (sym (rel 𝕗A.2) id⟨1⟩ a⟨2⟩ (𝕗A.2 liftr a⟨0⟩) liftr (rel a⟨0⟩)))
      id⟨1⟩ (rel (𝕗B.2 (𝕗A.2 liftr a⟨0⟩) trl (f1 (𝕗A.2 trr a⟨0⟩))))
        (rel f1 (𝕗A.2⁽ᵖ¹⁾ id⟨1⟩ a⟨2⟩ (𝕗A.2 liftr a⟨0⟩) trr (rel a⟨0⟩))) trl
        (𝕗B.2 (𝕗A.2 liftr a⟨0⟩) liftl (f1 (𝕗A.2 trr a⟨0⟩)));
  id⟨p⟩ = λ f0 f1 →
    𝕗eqv ((a0 : A.0) (a1 : A.1) (a2 : A.2 a0 a1) → B.2 a2 (f0 a0) (f1 a1))
      (Br Π A.2 B.2 f0 f1) (id_Π_iso A.0 A.1 A.2 B.0 B.1 B.2 f0 f1)
      (𝕗Π A.0 (a0 ↦ (a1 : A.1) (a2 : A.2 a0 a1) → B.2 a2 (f0 a0) (f1 a1))
         𝕗A.0
         (a0 ↦
          𝕗Π A.1 (a1 ↦ (a2 : A.2 a0 a1) → B.2 a2 (f0 a0) (f1 a1)) 𝕗A.1
            (a1 ↦
             𝕗Π (A.2 a0 a1) (a2 ↦ B.2 a2 (f0 a0) (f1 a1)) (𝕗A.2 id a0 a1)
               (a2 ↦ 𝕗B.2 a2 id (f0 a0) (f1 a1))))) }

{- Fibrant Π-types -}
Π𝕗 : (A : Fib) → (B : A t → Fib) → Fib
Π𝕗 A B = (
  t ≔ (a : A t) → B a t,
  f ≔ 𝕗Π (A t) (a ↦ B a t) (A f) (a ↦ B a f))

{- Empty type -}

∅ : Set
∅ = data []

𝕗∅ : isFibrant ∅
𝕗∅ = record {
  trr⟨p⟩ = λ { };
  trl⟨p⟩ = λ { };
  liftr⟨p⟩ = λ { };
  liftl⟨p⟩ = λ { };
  id⟨p⟩ = λ { } }

{- Gel types -}

Gel : (A B : Set) → (R : A → B → Set) → Br Set A B
Gel A B R = sig a b ↦ (
  ungel : R a b )

Gel_iso : (A B : Set) → (R : A → B → Set) → (a : A) → (b : B) → R a b ≅ Gel A B R a b
Gel_iso A B R a b = (
  to ≔ r ↦ (r,),
  fro ≔ g ↦ g .0,
  to_fro ≔ _ ↦ eq.rfl,
  fro_to ≔ _ ↦ eq.rfl,
  to_fro_to ≔ _ ↦ eq.rfl)

𝕗Gel : (A B : Set) → (R : A → B → Set) → (𝕗R : (a : A) (b : B) → isFibrant (R a b)) → (a : A) → (b : B) → isFibrant (Gel A B R a b)
𝕗Gel A B R 𝕗R a b = 𝕗eqv (R a b) (Gel A B R a b) (Gel_iso A B R a b) (𝕗R a b)

{- Sum type -}

sum : (A B : Set) → Set
sum A B = data [ left (_ : A) | right (_ : B) ]

notation(1.5) A "⊔" B ≔ sum A B

sum_code : (A0 A1 : Set) → (A2 : Br Set A0 A1) → (B0 B1 : Set) → (B2 : Br Set B0 B1) → (u0 : A0 ⊔ B0) → (u1 : A1 ⊔ B1) → Set
sum_code A0 A1 A2 B0 B1 B2 u0 u1 = match u0, u1 [
| left a0, left a1 ↦ A2 a0 a1
| left a0, right b1 ↦ ∅
| right b0, left a1 ↦ ∅
| right b0, right b1 ↦ B2 b0 b1]

id_sum_iso : (A0 A1 : Set) → (A2 : Br Set A0 A1) → (B0 B1 : Set) → (B2 : Br Set B0 B1) → (u0 : A0 ⊔ B0) → (u1 : A1 ⊔ B1) → sum_code A0 A1 A2 B0 B1 B2 u0 u1 ≅ Br sum A2 B2 u0 u1
id_sum_iso A0 A1 A2 B0 B1 B2 u0 u1 = (
  to ≔ v2 ↦ match u0, u1 [
  | left a0, left a1 ↦ left v2
  | left a0, right b1 ↦ match v2 [ ]
  | right b0, left a1 ↦ match v2 [ ]
  | right b0, right b1 ↦ right v2],
  fro ≔ λ { left a ⤇ a⟨2⟩; right b ⤇ b⟨2⟩ },
  to_fro ≔ λ { left a ⤇ eq.rfl; right b ⤇ eq.rfl },
  fro_to ≔ v2 ↦ match u0, u1 [
  | left a0, left a1 ↦ eq.rfl
  | left a0, right b1 ↦ match v2 [ ]
  | right b0, left a1 ↦ match v2 [ ]
  | right b0, right b1 ↦ eq.rfl],
  to_fro_to ≔ v2 ↦ match u0, u1 [
  | left a0, left a1 ↦ eq.rfl
  | left a0, right b1 ↦ match v2 [ ]
  | right b0, left a1 ↦ match v2 [ ]
  | right b0, right b1 ↦ eq.rfl])

𝕗sum : (A B : Set) → (𝕗A : isFibrant A) → (𝕗B : isFibrant B) → isFibrant (A ⊔ B)
𝕗sum A B 𝕗A 𝕗B = record {
  trr⟨p⟩ = λ { left a0 → left (𝕗A.2 trr a0); right b0 → right (𝕗B.2 trr b0) };
  trl⟨p⟩ = λ { left a1 → left (𝕗A.2 trl a1); right b1 → right (𝕗B.2 trl b1) };
  liftr⟨p⟩ = λ { left a0 → left (𝕗A.2 liftr a0); right b0 → right (𝕗B.2 liftr b0) };
  liftl⟨p⟩ = λ { left a1 → left (𝕗A.2 liftl a1); right b1 → right (𝕗B.2 liftl b1) };
  id⟨p⟩ = λ u0 u1 →
    𝕗eqv (sum_code A.0 A.1 A.2 B.0 B.1 B.2 u0 u1) (Br sum A.2 B.2 u0 u1)
      (id_sum_iso A.0 A.1 A.2 B.0 B.1 B.2 u0 u1)
      (match u0, u1 [
       | left a0, left a1 ↦ 𝕗A.2 id a0 a1
       | left _, right _ ↦ 𝕗∅
       | right _, left _ ↦ 𝕗∅
       | right b0, right b1 ↦ 𝕗B.2 id b0 b1]) }

{- The natural numbers -}

ℕ : Set
ℕ = data [ zero | suc (_ : ℕ) ]

ℕ_code : (m n : ℕ) → Set
ℕ_code m n = match m, n [
| zero, zero ↦ ⊤
| zero, suc _ ↦ ∅
| suc _, zero ↦ ∅
| suc m, suc n ↦ ℕ_code m n]

id_ℕ_iso : (n0 n1 : ℕ) → ℕ_code n0 n1 ≅ Br ℕ n0 n1
id_ℕ_iso n0 n1 = adjointify (ℕ_code n0 n1) (Br ℕ n0 n1)
      (m2 ↦
       match n0, n1 [
       | zero, zero ↦ zero
       | zero, suc n1 ↦ match m2 [ ]
       | suc n0, zero ↦ match m2 [ ]
       | suc n0, suc n1 ↦ suc (id_ℕ_iso n0 n1 to m2)])
      (λ { zero ⤇ (); suc m ⤇ id_ℕ_iso m⟨0⟩ m⟨1⟩ fro m⟨2⟩ })
      (m2 ↦
       match n0, n1 [
       | zero, zero ↦ eq.rfl
       | zero, suc n1 ↦ match m2 [ ]
       | suc n0, zero ↦ match m2 [ ]
       | suc n0, suc n1 ↦ id_ℕ_iso n0 n1 fro_to m2])
      (λ {
       zero ⤇ eq.rfl;
       suc m ⤇
         eq.ap (Br ℕ m⟨0⟩ m⟨1⟩) (Br ℕ (suc m⟨0⟩) (suc m⟨1⟩)) (x ↦ suc x)
             (id_ℕ_iso m⟨0⟩ m⟨1⟩ to (id_ℕ_iso m⟨0⟩ m⟨1⟩ fro m⟨2⟩))
           m⟨2⟩ (id_ℕ_iso m⟨0⟩ m⟨1⟩ to_fro m⟨2⟩) })

𝕗_ℕ_code : (n0 n1 : ℕ) → isFibrant (ℕ_code n0 n1)
𝕗_ℕ_code n0 n1 = match n0, n1 [
| zero, zero ↦ 𝕗⊤
| zero, suc n1 ↦ 𝕗∅
| suc n0, zero ↦ 𝕗∅
| suc n0, suc n1 ↦ 𝕗_ℕ_code n0 n1]

𝕗ℕ : isFibrant ℕ
𝕗ℕ = record {
  trr⟨p⟩ = λ x → x;
  trl⟨p⟩ = λ x → x;
  liftr⟨p⟩ = λ x → rel x;
  liftl⟨p⟩ = λ x → rel x;
  id⟨p⟩ = λ n0 n1 →
    𝕗eqv (ℕ_code n0 n1) (Br ℕ n0 n1) (id_ℕ_iso n0 n1) (𝕗_ℕ_code n0 n1) }

{- W-types -}

{- To prove that general W-types are fibrant, we need function extensionality, since W-types involve functions as inputs. -}

postulate funext (A : Set) (B : A → Set) (f0 f1 : (x : A) → B x) (f2 : (x : A) → eq (B x) (f0 x) (f1 x)) : eq ((x : A) → B x) f0 f1

{- We also need a version of funext for bridges in function types.  Since Id-Π is definitionally isomorphic to a triple Π-type, we can derive this from ordinary funext. -}

funext_refl : (A0 A1 : Set) → (A2 : Br Set A0 A1) → (B0 : A0 → Set) → (B1 : A1 → Set) → (B2 : rel ((X ↦ X → Set) : Set → Set) A2 B0 B1) → (f0 : Π A0 B0) → (f1 : Π A1 B1) → (f20 f21 : rel Π A2 B2 f0 f1) → (f22 : (a0 : A0) (a1 : A1) (a2 : A2 a0 a1)
         → eq⟨eq⟩ (B2 a2 (f0 a0) (f1 a1)) (f20 a2) (f21 a2)) → eq (rel Π A2 B2 f0 f1) f20 f21
funext_refl A0 A1 A2 B0 B1 B2 f0 f1 f20 f21 f22 = eq.ap ((a0 : A0) (a1 : A1) (a2 : A2 a0 a1) → B2 a2 (f0 a0) (f1 a1))
      (rel Π A2 {x ↦ B0 x} {x ↦ B1 x} (x ⤇ B2 x⟨2⟩) f0 f1)
      (g ↦ x ⤇ g x⟨0⟩ x⟨1⟩ x⟨2⟩) (x0 x1 x2 ↦ f20 x2) (x0 x1 x2 ↦ f21 x2)
      (funext A0 (a0 ↦ (a1 : A1) (a2 : A2 a0 a1) → B2 a2 (f0 a0) (f1 a1))
         (x0 x1 x2 ↦ f20 x2) (x0 x1 x2 ↦ f21 x2)
         (a0 ↦
          funext A1 (a1 ↦ (a2 : A2 a0 a1) → B2 a2 (f0 a0) (f1 a1))
            (x1 x2 ↦ f20 x2) (x1 x2 ↦ f21 x2)
            (a1 ↦
             funext (A2 a0 a1) (a2 ↦ B2 a2 (f0 a0) (f1 a1)) (x2 ↦ f20 x2)
               (x2 ↦ f21 x2) (a2 ↦ f22 a0 a1 a2))))

{- Now, there are two ways to characterize the Br types of a W-type.  The firts is that the Id-types of an (indexed) W-type are an indexed W-type, which is properly indexed even if the original W-type was not.  This is not helpful for us, since indexed inductive types in general are *not* fibrant until we fibrantly replace them.  However, we include the encode-decode argument here anyway. -}

section Indexed_𝕎 ≔

  𝕎spec : Set
  𝕎spec = sig (
    I : Set,
    A : Set,
    B : A → Set,
    j : (a : A) → B a → I,
    k : A → I )

  𝕎 : (s : 𝕎spec) → s I → Set
  𝕎 s = data [
  | sup (a : s A) (f : (b : s B a) → 𝕎 s (s j a b)) : 𝕎 s (s k a) ]

  code_spec : (s : 𝕎spec) → 𝕎spec
  code_spec s = (
    I ≔ sig (
      i0 : s I,
      i1 : s I,
      i2 : Br (s I) i0 i1,
      x0 : 𝕎 s i0,
      x1 : 𝕎 s i1 ),
    A ≔ sig (
      a0 : s A,
      a1 : s A,
      a2 : Br (s A) a0 a1,
      f0 : (b0 : s B a0) → 𝕎 s (s j a0 b0),
      f1 : (b1 : s B a1) → 𝕎 s (s j a1 b1) ),
    B ≔ x ↦ sig (
      b0 : s B (x a0),
      b1 : s B (x a1),
      b2 : rel (s B) (x a2) b0 b1 ),
    j ≔ a b ↦ (
      s j (a a0) (b b0),
      s j (a a1) (b b1),
      rel (s j) (a a2) (b b2),
      a f0 (b b0),
      a f1 (b b1)),
    k ≔ a ↦ (
      s k (a a0),
      s k (a a1),
      rel (s k) (a a2),
      sup (a a0) (a f0),
      sup (a a1) (a f1)))

  𝕎_encode : (s : 𝕎spec) → (i0 i1 : s I) → (i2 : Br (s I) i0 i1) → (x0 : 𝕎 s i0) → (x1 : 𝕎 s i1) → (x2 : rel (𝕎 s) i2 x0 x1) → 𝕎 (code_spec s) (i0, i1, i2, x0, x1)
  𝕎_encode s i0 i1 i2 x0 x1 x2 = match x2 [
  | sup a f ⤇
      sup (a.0, a⟨1⟩, a⟨2⟩, f⟨0⟩, f⟨1⟩)
        (b ↦
         𝕎_encode s (s j a⟨0⟩ (b b0)) (s j a⟨1⟩ (b b1))
           (rel (s j) a⟨2⟩ (b b2)) (f.0 (b b0)) (f.1 (b b1)) (f.2 (b b2)))]

  𝕎_decode : (s : 𝕎spec) → (y : code_spec s I) → (y2 : 𝕎 (code_spec s) y) → rel (𝕎 s) (y i2) (y x0) (y x1)
  𝕎_decode s y y2 = match y2 [
  | sup a f ↦
      sup (a a2)
        (b ⤇
         𝕎_decode s
           (s j (a a0) b⟨0⟩,
            s j (a a1) b⟨1⟩,
            rel s j (a a2) b⟨2⟩,
            a f0 b⟨0⟩,
            a f1 b⟨1⟩) (f (b.0, b⟨1⟩, b⟨2⟩)))]

  𝕎_decode_encode : (s : 𝕎spec) → (i0 i1 : s I) → (i2 : Br (s I) i0 i1) → (x0 : 𝕎 s i0) → (x1 : 𝕎 s i1) → (x2 : rel (𝕎 s) i2 x0 x1) → eq (rel (𝕎 s) i2 x0 x1)
        (𝕎_decode s (i0, i1, i2, x0, x1) (𝕎_encode s i0 i1 i2 x0 x1 x2)) x2
  𝕎_decode_encode s i0 i1 i2 x0 x1 x2 = match x2 [
  | sup a f ⤇
      eq.ap
          (rel Π (rel s B a⟨2⟩) {b ↦ 𝕎 s (s j a⟨0⟩ b)}
               {b ↦ 𝕎 s (s j a⟨1⟩ b)}
               (b ⤇ rel 𝕎 (rel s) (rel s j a⟨2⟩ b⟨2⟩))
           f⟨0⟩
           f⟨1⟩)
          (rel 𝕎 (rel s) (rel s k a⟨2⟩) (sup a⟨0⟩ f⟨0⟩) (sup a⟨1⟩ f⟨1⟩))
          (H ↦ sup a⟨2⟩ H)
          (b ⤇
           𝕎_decode s
             (s j a⟨0⟩ b⟨0⟩,
              s j a⟨1⟩ b⟨1⟩,
              rel s j a⟨2⟩ b⟨2⟩,
              f⟨0⟩ b⟨0⟩,
              f⟨1⟩ b⟨1⟩)
             (𝕎_encode s (s j a⟨0⟩ b⟨0⟩) (s j a⟨1⟩ b⟨1⟩)
                (rel s j a⟨2⟩ b⟨2⟩) (f.0 b⟨0⟩) (f.1 b⟨1⟩) (f.2 b⟨2⟩)))
        f⟨2⟩
          (funext_refl (s B a⟨0⟩) (s B a⟨1⟩) (rel s B a⟨2⟩)
               (x ↦ 𝕎 s (s j a⟨0⟩ x)) (x ↦ 𝕎 s (s j a⟨1⟩ x))
               (x ⤇ rel 𝕎 (rel s) (rel s j a⟨2⟩ x⟨2⟩))
           f⟨0⟩
           f⟨1⟩
             (b ⤇
              𝕎_decode s
                (s j a⟨0⟩ b⟨0⟩,
                 s j a⟨1⟩ b⟨1⟩,
                 rel s j a⟨2⟩ b⟨2⟩,
                 f⟨0⟩ b⟨0⟩,
                 f⟨1⟩ b⟨1⟩)
                (𝕎_encode s (s j a⟨0⟩ b⟨0⟩) (s j a⟨1⟩ b⟨1⟩)
                   (rel s j a⟨2⟩ b⟨2⟩) (f.0 b⟨0⟩) (f.1 b⟨1⟩) (f.2 b⟨2⟩)))
           f⟨2⟩
             (a0 a1 a2 ↦
              𝕎_decode_encode s (s j a⟨0⟩ a0) (s j a⟨1⟩ a1)
                (rel s j a⟨2⟩ a2) (f.0 a0) (f.1 a1) (f.2 a2)))]

  𝕎_encode_decode : (s : 𝕎spec) → (y : code_spec s I) → (y2 : 𝕎 (code_spec s) y) → eq (𝕎 (code_spec s) y)
        (𝕎_encode s (y i0) (y i1) (y i2) (y x0) (y x1) (𝕎_decode s y y2))
        y2
  𝕎_encode_decode s y y2 = match y2 [
  | sup a f ↦
      eq.ap ((b : code_spec s B a) → 𝕎 (code_spec s) (code_spec s j a b))
        (𝕎 (code_spec s) (code_spec s k a)) (g ↦ sup a g)
        (b ↦
         𝕎_encode s (s j (a a0) (b b0)) (s j (a a1) (b b1))
           (rel s j (a a2) (b b2)) (a f0 (b b0)) (a f1 (b b1))
           (𝕎_decode s
              (s j (a a0) (b b0),
               s j (a a1) (b b1),
               rel s j (a a2) (b b2),
               a f0 (b b0),
               a f1 (b b1)) (f (b b0, b b1, b b2)))) f
        (funext (code_spec s B a) (b ↦ 𝕎 (code_spec s) (code_spec s j a b))
           (b ↦
            𝕎_encode s (s j (a a0) (b b0)) (s j (a a1) (b b1))
              (rel s j (a a2) (b b2)) (a f0 (b b0)) (a f1 (b b1))
              (𝕎_decode s
                 (s j (a a0) (b b0),
                  s j (a a1) (b b1),
                  rel s j (a a2) (b b2),
                  a f0 (b b0),
                  a f1 (b b1)) (f (b b0, b b1, b b2)))) f
           (x ↦ 𝕎_encode_decode s (code_spec s j a x) (f x)))]

  id_𝕎_iso : (s : 𝕎spec) → (i0 i1 : s I) → (i2 : Br (s I) i0 i1) → (x0 : 𝕎 s i0) → (x1 : 𝕎 s i1) → rel (𝕎 s) i2 x0 x1 ≅ 𝕎 (code_spec s) (i0, i1, i2, x0, x1)
  id_𝕎_iso s i0 i1 i2 x0 x1 = adjointify (rel (𝕎 s) i2 x0 x1)
        (𝕎 (code_spec s) (i0, i1, i2, x0, x1)) (𝕎_encode s i0 i1 i2 x0 x1)
        (𝕎_decode s (i0, i1, i2, x0, x1))
        (x2 ↦ 𝕎_decode_encode s i0 i1 i2 x0 x1 x2)
        (y2 ↦ 𝕎_encode_decode s (i0, i1, i2, x0, x1) y2)

end

{- The characterization of Id-types of W-types that is useful to us is recursive, analogous to that for the Id-types of ℕ above. -}

𝕎 : (A : Set) → (B : A → Set) → Set
𝕎 A B = data [
| sup (a : A) (f : B a → 𝕎 A B) ]

{- We need to characterize the *dependent* Id-types over bridges of A and B. -}

𝕎_code : (A0 A1 : Set) → (A2 : Br Set A0 A1) → (B0 : A0 → Set) → (B1 : A1 → Set) → (B2 : rel ((X ↦ X → Set) : Set → Set) A2 B0 B1) → (x0 : 𝕎 A0 B0) → (x1 : 𝕎 A1 B1) → Set
𝕎_code A0 A1 A2 B0 B1 B2 x0 x1 = match x0, x1 [
| sup a0 f0, sup a1 f1 ↦
    Σ (A2 a0 a1)
      (a2 ↦
       (b0 : B0 a0) (b1 : B1 a1) (b2 : B2 a2 b0 b1)
       → 𝕎_code A0 A1 A2 B0 B1 B2 (f0 b0) (f1 b1))]

{- The encode-decode argument is straightforward, and only long because of the multiple applications of funext and because we lack implicit arguments. -}

𝕎_encode : (A0 A1 : Set) → (A2 : Br Set A0 A1) → (B0 : A0 → Set) → (B1 : A1 → Set) → (B2 : rel ((X ↦ X → Set) : Set → Set) A2 B0 B1) → (x0 : 𝕎 A0 B0) → (x1 : 𝕎 A1 B1) → (x2 : rel 𝕎 A2 B2 x0 x1) → 𝕎_code A0 A1 A2 B0 B1 B2 x0 x1
𝕎_encode A0 A1 A2 B0 B1 B2 x0 x1 x2 = match x2 [
| sup a f ⤇ (
    fst ≔ a⟨2⟩,
    snd ≔ b0 b1 b2 ↦ 𝕎_encode A0 A1 A2 B0 B1 B2 (f.0 b0) (f.1 b1) (f.2 b2))]

𝕎_decode : (A0 A1 : Set) → (A2 : Br Set A0 A1) → (B0 : A0 → Set) → (B1 : A1 → Set) → (B2 : rel ((X ↦ X → Set) : Set → Set) A2 B0 B1) → (x0 : 𝕎 A0 B0) → (x1 : 𝕎 A1 B1) → (y2 : 𝕎_code A0 A1 A2 B0 B1 B2 x0 x1) → rel 𝕎 A2 B2 x0 x1
𝕎_decode A0 A1 A2 B0 B1 B2 x0 x1 y2 = match x0, x1 [
| sup a0 f0, sup a1 f1 ↦
    sup (y2 fst)
      (b ⤇
       𝕎_decode A0 A1 A2 B0 B1 B2 (f0 b⟨0⟩) (f1 b⟨1⟩)
         (y2 snd b⟨0⟩ b⟨1⟩ b⟨2⟩))]

𝕎_decode_encode : (A0 A1 : Set) → (A2 : Br Set A0 A1) → (B0 : A0 → Set) → (B1 : A1 → Set) → (B2 : rel ((X ↦ X → Set) : Set → Set) A2 B0 B1) → (x0 : 𝕎 A0 B0) → (x1 : 𝕎 A1 B1) → (x2 : rel 𝕎 A2 B2 x0 x1) → eq (rel 𝕎 A2 B2 x0 x1)
      (𝕎_decode A0 A1 A2 B0 B1 B2 x0 x1
         (𝕎_encode A0 A1 A2 B0 B1 B2 x0 x1 x2)) x2
𝕎_decode_encode A0 A1 A2 B0 B1 B2 x0 x1 x2 = match x2 [
| sup a f ⤇
    eq.ap
        (rel Π (B2 a⟨2⟩) {_ ↦ 𝕎 A0 B0} {_ ↦ 𝕎 A1 B1} (_ ⤇ rel 𝕎 A2 B2)
         f⟨0⟩
         f⟨1⟩) (rel 𝕎 A2 B2 (sup a⟨0⟩ f⟨0⟩) (sup a⟨1⟩ f⟨1⟩))
        (g ↦ sup a⟨2⟩ g)
        (b ⤇
         𝕎_decode A0 A1 A2 B0 B1 B2 (f.0 b⟨0⟩) (f.1 b⟨1⟩)
           (𝕎_encode A0 A1 A2 B0 B1 B2 (f.0 b⟨0⟩) (f.1 b⟨1⟩) (f.2 b⟨2⟩)))
      f⟨2⟩
        (funext_refl (B0 a⟨0⟩) (B1 a⟨1⟩) (B2 a⟨2⟩) (_ ↦ 𝕎 A0 B0)
             (_ ↦ 𝕎 A1 B1) (_ ⤇ rel 𝕎 A2 B2)
         f⟨0⟩
         f⟨1⟩
           (b ⤇
            𝕎_decode A0 A1 A2 B0 B1 B2 (f.0 b⟨0⟩) (f.1 b⟨1⟩)
              (𝕎_encode A0 A1 A2 B0 B1 B2 (f.0 b⟨0⟩) (f.1 b⟨1⟩) (f.2 b⟨2⟩)))
         f⟨2⟩
           (a0 a1 a2 ↦
            𝕎_decode_encode A0 A1 A2 B0 B1 B2 (f.0 a0) (f.1 a1) (f.2 a2)))]

𝕎_encode_decode : (A0 A1 : Set) → (A2 : Br Set A0 A1) → (B0 : A0 → Set) → (B1 : A1 → Set) → (B2 : rel ((X ↦ X → Set) : Set → Set) A2 B0 B1) → (x0 : 𝕎 A0 B0) → (x1 : 𝕎 A1 B1) → (y2 : 𝕎_code A0 A1 A2 B0 B1 B2 x0 x1) → eq (𝕎_code A0 A1 A2 B0 B1 B2 x0 x1)
      (𝕎_encode A0 A1 A2 B0 B1 B2 x0 x1
         (𝕎_decode A0 A1 A2 B0 B1 B2 x0 x1 y2)) y2
𝕎_encode_decode A0 A1 A2 B0 B1 B2 x0 x1 y2 = match x0, x1 [
| sup a0 f0, sup a1 f1 ↦
    eq.ap
      ((b0 : B0 a0) (b1 : B1 a1) (b2 : B2 (y2 fst) b0 b1)
       → 𝕎_code A0 A1 A2 B0 B1 B2 (f0 b0) (f1 b1))
      (Σ (A2 a0 a1)
         (a2 ↦
          (b0 : B0 a0) (b1 : B1 a1) (b2 : B2 a2 b0 b1)
          → 𝕎_code A0 A1 A2 B0 B1 B2 (f0 b0) (f1 b1))) (f2 ↦ (y2 fst, f2))
      ((𝕎_encode A0 A1 A2 B0 B1 B2 (sup a0 f0) (sup a1 f1)
          (sup (y2 fst)
             (b ⤇
              𝕎_decode A0 A1 A2 B0 B1 B2 (f0 b⟨0⟩) (f1 b⟨1⟩)
                (y2 snd b⟨0⟩ b⟨1⟩ b⟨2⟩)))) snd) (y2 snd)
      (funext (B0 a0)
         (b0 ↦
          (b1 : B1 a1) (b2 : B2 (y2 fst) b0 b1)
          → 𝕎_code A0 A1 A2 B0 B1 B2 (f0 b0) (f1 b1))
         (𝕎_encode A0 A1 A2 B0 B1 B2 (sup a0 f0) (sup a1 f1)
            (sup (y2 fst)
               (b ⤇
                𝕎_decode A0 A1 A2 B0 B1 B2 (f0 b⟨0⟩) (f1 b⟨1⟩)
                  (y2 snd b⟨0⟩ b⟨1⟩ b⟨2⟩))) snd) (y2 snd)
         (b0 ↦
          funext (B1 a1)
            (b1 ↦
             (b2 : B2 (y2 fst) b0 b1)
             → 𝕎_code A0 A1 A2 B0 B1 B2 (f0 b0) (f1 b1))
            (𝕎_encode A0 A1 A2 B0 B1 B2 (sup a0 f0) (sup a1 f1)
               (sup (y2 fst)
                  (b ⤇
                   𝕎_decode A0 A1 A2 B0 B1 B2 (f0 b⟨0⟩) (f1 b⟨1⟩)
                     (y2 snd b⟨0⟩ b⟨1⟩ b⟨2⟩))) snd b0) (y2 snd b0)
            (b1 ↦
             funext (B2 (y2 fst) b0 b1)
               (_ ↦ 𝕎_code A0 A1 A2 B0 B1 B2 (f0 b0) (f1 b1))
               (𝕎_encode A0 A1 A2 B0 B1 B2 (sup a0 f0) (sup a1 f1)
                  (sup (y2 fst)
                     (b ⤇
                      𝕎_decode A0 A1 A2 B0 B1 B2 (f0 b⟨0⟩) (f1 b⟨1⟩)
                        (y2 snd b⟨0⟩ b⟨1⟩ b⟨2⟩))) snd b0 b1) (y2 snd b0 b1)
               (b2 ↦
                𝕎_encode_decode A0 A1 A2 B0 B1 B2 (f0 b0) (f1 b1)
                  (y2 snd b0 b1 b2)))))]

Id_𝕎_iso : (A0 A1 : Set) → (A2 : Br Set A0 A1) → (B0 : A0 → Set) → (B1 : A1 → Set) → (B2 : rel ((X ↦ X → Set) : Set → Set) A2 B0 B1) → (x0 : 𝕎 A0 B0) → (x1 : 𝕎 A1 B1) → 𝕎_code A0 A1 A2 B0 B1 B2 x0 x1 ≅ rel 𝕎 A2 B2 x0 x1
Id_𝕎_iso A0 A1 A2 B0 B1 B2 x0 x1 = adjointify (𝕎_code A0 A1 A2 B0 B1 B2 x0 x1) (rel 𝕎 A2 B2 x0 x1)
      (𝕎_decode A0 A1 A2 B0 B1 B2 x0 x1) (𝕎_encode A0 A1 A2 B0 B1 B2 x0 x1)
      (𝕎_encode_decode A0 A1 A2 B0 B1 B2 x0 x1)
      (𝕎_decode_encode A0 A1 A2 B0 B1 B2 x0 x1)

{- Next we prove that the codes are fibrant if the inputs are.  This is just putting together 𝕗Σ and 𝕗Π. -}

𝕗_𝕎_code : (A0 A1 : Set) → (A2 : Br Set A0 A1) → (B0 : A0 → Set) → (B1 : A1 → Set) → (B2 : rel ((X ↦ X → Set) : Set → Set) A2 B0 B1) → (𝕗A0 : isFibrant A0) → (𝕗A1 : isFibrant A1) → (𝕗A2 : rel isFibrant A2 𝕗A0 𝕗A1) → (𝕗B0 : (a0 : A0) → isFibrant (B0 a0)) → (𝕗B1 : (a1 : A1) → isFibrant (B1 a1)) → (𝕗B2 : rel Π A2 {x ↦ isFibrant (B0 x)} {x ↦ isFibrant (B1 x)}
           (x ⤇ rel isFibrant (B2 x⟨2⟩)) 𝕗B0 𝕗B1) → (x0 : 𝕎 A0 B0) → (x1 : 𝕎 A1 B1) → isFibrant (𝕎_code A0 A1 A2 B0 B1 B2 x0 x1)
𝕗_𝕎_code A0 A1 A2 B0 B1 B2 𝕗A0 𝕗A1 𝕗A2 𝕗B0 𝕗B1 𝕗B2 x0 x1 = match x0, x1 [
| sup a0 f0, sup a1 f1 ↦
    𝕗Σ (A2 a0 a1)
      (a2 ↦
       (b0 : B0 a0) (b1 : B1 a1) (b2 : B2 a2 b0 b1)
       → 𝕎_code A0 A1 A2 B0 B1 B2 (f0 b0) (f1 b1)) (𝕗A2 id a0 a1)
      (a2 ↦
       𝕗Π (B0 a0)
         (b0 ↦
          (b1 : B1 a1) (b2 : B2 a2 b0 b1)
          → 𝕎_code A0 A1 A2 B0 B1 B2 (f0 b0) (f1 b1)) (𝕗B0 a0)
         (b0 ↦
          𝕗Π (B1 a1)
            (b1 ↦
             (b2 : B2 a2 b0 b1) → 𝕎_code A0 A1 A2 B0 B1 B2 (f0 b0) (f1 b1))
            (𝕗B1 a1)
            (b1 ↦
             𝕗Π (B2 a2 b0 b1)
               (_ ↦ 𝕎_code A0 A1 A2 B0 B1 B2 (f0 b0) (f1 b1))
               (𝕗B2 a2 id b0 b1)
               (b2 ↦
                𝕗_𝕎_code A0 A1 A2 B0 B1 B2 𝕗A0 𝕗A1 𝕗A2 𝕗B0 𝕗B1 𝕗B2 (f0 b0)
                  (f1 b1)))))]

{- Finally, we can prove that W-types are fibrant.  Note that there are "recursive calls" to 𝕗𝕎 in *all* the clauses.  I'm not exactly sure how they are justified in the cases of tr and lift, but note that they are inside matches as well.  -}

𝕗𝕎 : (A : Set) → (B : A → Set) → (𝕗A : isFibrant A) → (𝕗B : (x : A) → isFibrant (B x)) → isFibrant (𝕎 A B)
𝕗𝕎 A B 𝕗A 𝕗B = record {
  trr⟨p⟩ = λ {
  sup a0 f0 →
      sup (𝕗A.2 trr a0)
        (rel 𝕗Π (B.2 (𝕗A.2 liftr a0)) {_ ↦ 𝕎 A.0 B.0} {_ ↦ 𝕎 A.1 B.1}
           (_ ⤇ rel 𝕎 A.2 B.2) (𝕗B.2 (𝕗A.2 liftr a0))
           {_ ↦ 𝕗𝕎 A.0 B.0 𝕗A.0 𝕗B.0} {_ ↦ 𝕗𝕎 A.1 B.1 𝕗A.1 𝕗B.1}
           (_ ⤇ rel 𝕗𝕎 A.2 B.2 𝕗A.2 𝕗B.2) trr f0) };
  trl⟨p⟩ = λ {
  sup a1 f1 →
      sup (𝕗A.2 trl a1)
        (rel 𝕗Π (B.2 (𝕗A.2 liftl a1)) {_ ↦ 𝕎 A.0 B.0} {_ ↦ 𝕎 A.1 B.1}
           (_ ⤇ rel 𝕎 A.2 B.2) (𝕗B.2 (𝕗A.2 liftl a1))
           {_ ↦ 𝕗𝕎 A.0 B.0 𝕗A.0 𝕗B.0} {_ ↦ 𝕗𝕎 A.1 B.1 𝕗A.1 𝕗B.1}
           (_ ⤇ rel 𝕗𝕎 A.2 B.2 𝕗A.2 𝕗B.2) trl f1) };
  liftr⟨p⟩ = λ {
  sup a0 f0 →
      sup (𝕗A.2 liftr a0)
        (rel 𝕗Π (B.2 (𝕗A.2 liftr a0)) {_ ↦ 𝕎 A.0 B.0} {_ ↦ 𝕎 A.1 B.1}
           (_ ⤇ rel 𝕎 A.2 B.2) (𝕗B.2 (𝕗A.2 liftr a0))
           {_ ↦ 𝕗𝕎 A.0 B.0 𝕗A.0 𝕗B.0} {_ ↦ 𝕗𝕎 A.1 B.1 𝕗A.1 𝕗B.1}
           (_ ⤇ rel 𝕗𝕎 A.2 B.2 𝕗A.2 𝕗B.2) liftr f0) };
  liftl⟨p⟩ = λ {
  sup a1 f1 →
      sup (𝕗A.2 liftl a1)
        (rel 𝕗Π (B.2 (𝕗A.2 liftl a1)) {_ ↦ 𝕎 A.0 B.0} {_ ↦ 𝕎 A.1 B.1}
           (_ ⤇ rel 𝕎 A.2 B.2) (𝕗B.2 (𝕗A.2 liftl a1))
           {_ ↦ 𝕗𝕎 A.0 B.0 𝕗A.0 𝕗B.0} {_ ↦ 𝕗𝕎 A.1 B.1 𝕗A.1 𝕗B.1}
           (_ ⤇ rel 𝕗𝕎 A.2 B.2 𝕗A.2 𝕗B.2) liftl f1) };
  id⟨p⟩ = λ x0 x1 →
    𝕗eqv (𝕎_code A.0 A.1 A.2 B.0 B.1 B.2 x0 x1) (rel 𝕎 A.2 B.2 x0 x1)
      (Id_𝕎_iso A.0 A.1 A.2 B.0 B.1 B.2 x0 x1)
      (𝕗_𝕎_code A.0 A.1 A.2 B.0 B.1 B.2 𝕗A.0 𝕗A.1 𝕗A.2 𝕗B.0 𝕗B.1 𝕗B.2 x0 x1) }

{- The Id-types of a W-type can also be characterized by a W-type with non-uniform parameters. We can prove they are fibrant as there is no need to fibrantly replace them. -}

section Parametrized_W ≔

  𝕎_spec : Set
  𝕎_spec = sig (
    R : Set,
    A : R → Fib,
    B : (r : R) → A r t → Fib,
    k : (r : R) (a : A r t) → B r a t → R )

  𝕎 : (s : 𝕎_spec) → (r : s R) → Set
  𝕎 s r = data [
  | sup (a : s A r t) (f : (b : s B r a t) → 𝕎 s (s k r a b)) ]

  𝕎_proj1 : (s : 𝕎_spec) → (r : s R) → (x : 𝕎 s r) → s A r t
  𝕎_proj1 s r x = match x [
  | sup a f ↦ a]

  𝕎_proj2 : (s : 𝕎_spec) → (r : s R) → (x : 𝕎 s r) → (b : s B r (𝕎_proj1 s r x) t) → 𝕎 s (s k r (𝕎_proj1 s r x) b)
  𝕎_proj2 s r x = match x [ sup a f ↦ f ]

  𝕎_code_spec : (s0 s1 : 𝕎_spec) → (s2 : Br 𝕎_spec s0 s1) → 𝕎_spec
  𝕎_code_spec s0 s1 s2 = (
    R ≔ sig (
      r0 : s0 R,
      r1 : s1 R,
      r2 : s2 R r0 r1,
      x0 : 𝕎 s0 r0,
      x1 : 𝕎 s1 r1 ),
    A ≔ r ↦
      Idd𝕗 (s0 A (r r0)) (s1 A (r r1)) (s2 A (r r2))
        (𝕎_proj1 s0 (r r0) (r x0)) (𝕎_proj1 s1 (r r1) (r x1)),
    B ≔ r a2 ↦
      Σ𝕗 (s0 B (r r0) (𝕎_proj1 s0 (r r0) (r x0)))
        (b0 ↦
         Σ𝕗 (s1 B (r r1) (𝕎_proj1 s1 (r r1) (r x1)))
           (b1 ↦
            Idd𝕗 (s0 B (r r0) (𝕎_proj1 s0 (r r0) (r x0)))
              (s1 B (r r1) (𝕎_proj1 s1 (r r1) (r x1))) (s2 B (r r2) a2) b0
              b1)),
    k ≔ r a2 b ↦ (
      r0 ≔ s0 k (r r0) (𝕎_proj1 s0 (r r0) (r x0)) (b .0),
      r1 ≔ s1 k (r r1) (𝕎_proj1 s1 (r r1) (r x1)) (b .1 .0),
      r2 ≔ s2 k (r r2) a2 (b .1 .1),
      x0 ≔ 𝕎_proj2 s0 (r r0) (r x0) (b .0),
      x1 ≔ 𝕎_proj2 s1 (r r1) (r x1) (b .1 .0)))

  𝕎_encode : (s0 s1 : 𝕎_spec) → (s2 : Br 𝕎_spec s0 s1) → (r0 : s0 R) → (r1 : s1 R) → (r2 : s2 R r0 r1) → (x0 : 𝕎 s0 r0) → (x1 : 𝕎 s1 r1) → (x2 : Br 𝕎 s2 r2 x0 x1) → 𝕎 (𝕎_code_spec s0 s1 s2) (r0, r1, r2, x0, x1)
  𝕎_encode s0 s1 s2 r0 r1 r2 x0 x1 x2 = match x2 [
  | sup a f ⤇
      sup a⟨2⟩
        (b ↦
         𝕎_encode s0 s1 s2 (s0 k r0 a⟨0⟩ (b .0)) (s1 k r1 a⟨1⟩ (b .1 .0))
           (s2 k r2 a⟨2⟩ (b .1 .1)) (f.0 (b .0)) (f.1 (b .1 .0))
           (f.2 (b .1 .1)))]

  𝕎_decode : (s0 s1 : 𝕎_spec) → (s2 : Br 𝕎_spec s0 s1) → (r0 : s0 R) → (r1 : s1 R) → (r2 : s2 R r0 r1) → (x0 : 𝕎 s0 r0) → (x1 : 𝕎 s1 r1) → (y2 : 𝕎 (𝕎_code_spec s0 s1 s2) (r0, r1, r2, x0, x1)) → Br 𝕎 s2 r2 x0 x1
  𝕎_decode s0 s1 s2 r0 r1 r2 x0 x1 y2 = match x0, x1, y2 [
  | sup a0 f0, sup a1 f1, sup a2 f2 ↦
      sup a2
        (b ⤇
         𝕎_decode s0 s1 s2 (s0 k r0 a0 b⟨0⟩) (s1 k r1 a1 b⟨1⟩)
           (s2 k r2 a2 b⟨2⟩) (f0 b⟨0⟩) (f1 b⟨1⟩) (f2 (b.0, (b.1, b⟨2⟩))))]

  𝕎_decode_encode : (s0 s1 : 𝕎_spec) → (s2 : Br 𝕎_spec s0 s1) → (r0 : s0 R) → (r1 : s1 R) → (r2 : s2 R r0 r1) → (x0 : 𝕎 s0 r0) → (x1 : 𝕎 s1 r1) → (x2 : Br 𝕎 s2 r2 x0 x1) → eq (Br 𝕎 s2 r2 x0 x1)
        (𝕎_decode s0 s1 s2 r0 r1 r2 x0 x1
           (𝕎_encode s0 s1 s2 r0 r1 r2 x0 x1 x2)) x2
  𝕎_decode_encode s0 s1 s2 r0 r1 r2 x0 x1 x2 = match x2 [
  | sup a f ⤇
      eq.ap
          (rel Π (s2 B r2 a⟨2⟩ t) {b0 ↦ 𝕎 s0 (s0 k r0 a⟨0⟩ b0)}
               {b1 ↦ 𝕎 s1 (s1 k r1 a⟨1⟩ b1)}
               (b ⤇ rel 𝕎 s2 (s2 k r2 a⟨2⟩ b⟨2⟩))
           f⟨0⟩
           f⟨1⟩) (Br 𝕎 s2 r2 (sup a⟨0⟩ f⟨0⟩) (sup a⟨1⟩ f⟨1⟩))
          (f2 ↦ sup a⟨2⟩ f2)
          (b ⤇
           𝕎_decode s0 s1 s2 (s0 k r0 a⟨0⟩ b⟨0⟩) (s1 k r1 a⟨1⟩ b⟨1⟩)
             (s2 k r2 a⟨2⟩ b⟨2⟩) (f.0 b⟨0⟩) (f.1 b⟨1⟩)
             (𝕎_encode s0 s1 s2 (s0 k r0 a⟨0⟩ b⟨0⟩) (s1 k r1 a⟨1⟩ b⟨1⟩)
                (s2 k r2 a⟨2⟩ b⟨2⟩) (f.0 b⟨0⟩) (f.1 b⟨1⟩) (f.2 b⟨2⟩)))
        f⟨2⟩
          (funext_refl (s0 B r0 a⟨0⟩ t) (s1 B r1 a⟨1⟩ t) (s2 B r2 a⟨2⟩ t)
               (b0 ↦ 𝕎 s0 (s0 k r0 a⟨0⟩ b0)) (b1 ↦ 𝕎 s1 (s1 k r1 a⟨1⟩ b1))
               (b ⤇ rel 𝕎 s2 (s2 k r2 a⟨2⟩ b⟨2⟩))
           f⟨0⟩
           f⟨1⟩
             (b ⤇
              𝕎_decode s0 s1 s2 (s0 k r0 a⟨0⟩ b⟨0⟩) (s1 k r1 a⟨1⟩ b⟨1⟩)
                (s2 k r2 a⟨2⟩ b⟨2⟩) (f.0 b⟨0⟩) (f.1 b⟨1⟩)
                (𝕎_encode s0 s1 s2 (s0 k r0 a⟨0⟩ b⟨0⟩) (s1 k r1 a⟨1⟩ b⟨1⟩)
                   (s2 k r2 a⟨2⟩ b⟨2⟩) (f.0 b⟨0⟩) (f.1 b⟨1⟩) (f.2 b⟨2⟩)))
           f⟨2⟩
             (b0 b1 b2 ↦
              𝕎_decode_encode s0 s1 s2 (s0 k r0 a⟨0⟩ b0) (s1 k r1 a⟨1⟩ b1)
                (s2 k r2 a⟨2⟩ b2) (f.0 b0) (f.1 b1) (f.2 b2)))]

  𝕎_encode_decode : (s0 s1 : 𝕎_spec) → (s2 : Br 𝕎_spec s0 s1) → (r0 : s0 R) → (r1 : s1 R) → (r2 : s2 R r0 r1) → (x0 : 𝕎 s0 r0) → (x1 : 𝕎 s1 r1) → (y2 : 𝕎 (𝕎_code_spec s0 s1 s2) (r0, r1, r2, x0, x1)) → eq (𝕎 (𝕎_code_spec s0 s1 s2) (r0, r1, r2, x0, x1))
        (𝕎_encode s0 s1 s2 r0 r1 r2 x0 x1
           (𝕎_decode s0 s1 s2 r0 r1 r2 x0 x1 y2)) y2
  𝕎_encode_decode s0 s1 s2 r0 r1 r2 x0 x1 y2 = match x0, x1, y2 [
  | sup a0 f0, sup a1 f1, sup a2 f2 ↦
      eq.ap
        ((b2
         : 𝕎_code_spec s0 s1 s2 B (r0, r1, r2, sup a0 f0, sup a1 f1) a2 t)
         → 𝕎 (𝕎_code_spec s0 s1 s2)
             (𝕎_code_spec s0 s1 s2 k (r0, r1, r2, sup a0 f0, sup a1 f1) a2
                b2)) (𝕎 (𝕎_code_spec s0 s1 s2) (r0, r1, r2, x0, x1))
        (f2 ↦ sup a2 f2)
        (b ↦
         𝕎_encode s0 s1 s2 (s0 k r0 a0 (b .0)) (s1 k r1 a1 (b .1 .0))
           (s2 k r2 a2 (b .1 .1)) (f0 (b .0)) (f1 (b .1 .0))
           (𝕎_decode s0 s1 s2 (s0 k r0 a0 (b .0)) (s1 k r1 a1 (b .1 .0))
              (s2 k r2 a2 (b .1 .1)) (f0 (b .0)) (f1 (b .1 .0)) (f2 b))) f2
        (funext
           (𝕎_code_spec s0 s1 s2 B (r0, r1, r2, sup a0 f0, sup a1 f1) a2 t)
           (b ↦
            𝕎 (𝕎_code_spec s0 s1 s2)
              (𝕎_code_spec s0 s1 s2 k (r0, r1, r2, sup a0 f0, sup a1 f1) a2
                 b))
           (b ↦
            𝕎_encode s0 s1 s2 (s0 k r0 a0 (b .0)) (s1 k r1 a1 (b .1 .0))
              (s2 k r2 a2 (b .1 .1)) (f0 (b .0)) (f1 (b .1 .0))
              (𝕎_decode s0 s1 s2 (s0 k r0 a0 (b .0)) (s1 k r1 a1 (b .1 .0))
                 (s2 k r2 a2 (b .1 .1)) (f0 (b .0)) (f1 (b .1 .0)) (f2 b)))
           f2
           (b ↦
            𝕎_encode_decode s0 s1 s2 (s0 k r0 a0 (b .0))
              (s1 k r1 a1 (b .1 .0)) (s2 k r2 a2 (b .1 .1)) (f0 (b .0))
              (f1 (b .1 .0)) (f2 b)))]

  Id_𝕎_iso : (s0 s1 : 𝕎_spec) → (s2 : Br 𝕎_spec s0 s1) → (r0 : s0 R) → (r1 : s1 R) → (r2 : s2 R r0 r1) → (x0 : 𝕎 s0 r0) → (x1 : 𝕎 s1 r1) → 𝕎 (𝕎_code_spec s0 s1 s2) (r0, r1, r2, x0, x1) ≅ Br 𝕎 s2 r2 x0 x1
  Id_𝕎_iso s0 s1 s2 r0 r1 r2 x0 x1 = adjointify (𝕎 (𝕎_code_spec s0 s1 s2) (r0, r1, r2, x0, x1))
        (Br 𝕎 s2 r2 x0 x1) (𝕎_decode s0 s1 s2 r0 r1 r2 x0 x1)
        (𝕎_encode s0 s1 s2 r0 r1 r2 x0 x1)
        (𝕎_encode_decode s0 s1 s2 r0 r1 r2 x0 x1)
        (𝕎_decode_encode s0 s1 s2 r0 r1 r2 x0 x1)

  {- The same caveat holds here as in the proof that W-types are fibrant using the recursive characterization of Id-types. -}

  𝕗𝕎 : (s : 𝕎_spec) → (r : s R) → isFibrant (𝕎 s r)
  𝕗𝕎 s r = record {
    trr⟨p⟩ = λ {
    sup a0 f0 →
        sup (s.2 A r⟨2⟩ f trr a0)
          (rel 𝕗Π (s.2 B r⟨2⟩ (s.2 A r⟨2⟩ f liftr a0) t)
             {b0 ↦ 𝕎 s⟨0⟩ (s.0 k r⟨0⟩ a0 b0)}
             {b1 ↦ 𝕎 s⟨1⟩ (s.1 k r⟨1⟩ (s.2 A r⟨2⟩ f trr a0) b1)}
             (b ⤇ rel 𝕎 s⟨2⟩ (s.2 k r⟨2⟩ (s.2 A r⟨2⟩ f liftr a0) b⟨2⟩))
             (s.2 B r⟨2⟩ (s.2 A r⟨2⟩ f liftr a0) f)
             {b0 ↦ 𝕗𝕎 s⟨0⟩ (s.0 k r⟨0⟩ a0 b0)}
             {b1 ↦ 𝕗𝕎 s⟨1⟩ (s.1 k r⟨1⟩ (s.2 A r⟨2⟩ f trr a0) b1)}
             (b ⤇ rel 𝕗𝕎 s⟨2⟩ (s.2 k r⟨2⟩ (s.2 A r⟨2⟩ f liftr a0) b⟨2⟩))
             trr f0) };
    trl⟨p⟩ = λ {
    sup a1 f1 →
        sup (s.2 A r⟨2⟩ f trl a1)
          (rel 𝕗Π (s.2 B r⟨2⟩ (s.2 A r⟨2⟩ f liftl a1) t)
             {b0 ↦ 𝕎 s⟨0⟩ (s.0 k r⟨0⟩ (s.2 A r⟨2⟩ f trl a1) b0)}
             {b1 ↦ 𝕎 s⟨1⟩ (s.1 k r⟨1⟩ a1 b1)}
             (b ⤇ rel 𝕎 s⟨2⟩ (s.2 k r⟨2⟩ (s.2 A r⟨2⟩ f liftl a1) b⟨2⟩))
             (s.2 B r⟨2⟩ (s.2 A r⟨2⟩ f liftl a1) f)
             {b0 ↦ 𝕗𝕎 s⟨0⟩ (s.0 k r⟨0⟩ (s.2 A r⟨2⟩ f trl a1) b0)}
             {b1 ↦ 𝕗𝕎 s⟨1⟩ (s.1 k r⟨1⟩ a1 b1)}
             (b ⤇ rel 𝕗𝕎 s⟨2⟩ (s.2 k r⟨2⟩ (s.2 A r⟨2⟩ f liftl a1) b⟨2⟩))
             trl f1) };
    liftr⟨p⟩ = λ {
    sup a0 f0 →
        sup (s.2 A r⟨2⟩ f liftr a0)
          (rel 𝕗Π (s.2 B r⟨2⟩ (s.2 A r⟨2⟩ f liftr a0) t)
             {b0 ↦ 𝕎 s⟨0⟩ (s.0 k r⟨0⟩ a0 b0)}
             {b1 ↦ 𝕎 s⟨1⟩ (s.1 k r⟨1⟩ (s.2 A r⟨2⟩ f trr a0) b1)}
             (b ⤇ rel 𝕎 s⟨2⟩ (s.2 k r⟨2⟩ (s.2 A r⟨2⟩ f liftr a0) b⟨2⟩))
             (s.2 B r⟨2⟩ (s.2 A r⟨2⟩ f liftr a0) f)
             {b0 ↦ 𝕗𝕎 s⟨0⟩ (s.0 k r⟨0⟩ a0 b0)}
             {b1 ↦ 𝕗𝕎 s⟨1⟩ (s.1 k r⟨1⟩ (s.2 A r⟨2⟩ f trr a0) b1)}
             (b ⤇ rel 𝕗𝕎 s⟨2⟩ (s.2 k r⟨2⟩ (s.2 A r⟨2⟩ f liftr a0) b⟨2⟩))
             liftr f0) };
    liftl⟨p⟩ = λ {
    sup a1 f1 →
        sup (s.2 A r⟨2⟩ f liftl a1)
          (rel 𝕗Π (s.2 B r⟨2⟩ (s.2 A r⟨2⟩ f liftl a1) t)
             {b0 ↦ 𝕎 s⟨0⟩ (s.0 k r⟨0⟩ (s.2 A r⟨2⟩ f trl a1) b0)}
             {b1 ↦ 𝕎 s⟨1⟩ (s.1 k r⟨1⟩ a1 b1)}
             (b ⤇ rel 𝕎 s⟨2⟩ (s.2 k r⟨2⟩ (s.2 A r⟨2⟩ f liftl a1) b⟨2⟩))
             (s.2 B r⟨2⟩ (s.2 A r⟨2⟩ f liftl a1) f)
             {b0 ↦ 𝕗𝕎 s⟨0⟩ (s.0 k r⟨0⟩ (s.2 A r⟨2⟩ f trl a1) b0)}
             {b1 ↦ 𝕗𝕎 s⟨1⟩ (s.1 k r⟨1⟩ a1 b1)}
             (b ⤇ rel 𝕗𝕎 s⟨2⟩ (s.2 k r⟨2⟩ (s.2 A r⟨2⟩ f liftl a1) b⟨2⟩))
             liftl f1) };
    id⟨p⟩ = λ x0 x1 →
      𝕗eqv (𝕎 (𝕎_code_spec s⟨0⟩ s⟨1⟩ s⟨2⟩) (r.0, r⟨1⟩, r⟨2⟩, x0, x1))
        (Br 𝕎 s⟨2⟩ r⟨2⟩ x0 x1)
        (Id_𝕎_iso s⟨0⟩ s⟨1⟩ s⟨2⟩ r⟨0⟩ r⟨1⟩ r⟨2⟩ x0 x1)
        (𝕗𝕎 (𝕎_code_spec s⟨0⟩ s⟨1⟩ s⟨2⟩) (r.0, r⟨1⟩, r⟨2⟩, x0, x1)) }

end

{- M-types -}

{- The bridge types of an M-type are M-types with non-uniform parameters, so we need to treat those in generality. -}

𝕄_spec : Set
𝕄_spec = sig (
  R : Set,
  A : R → Fib,
  B : (r : R) → A r t → Fib,
  k : (r : R) (a : A r t) → B r a t → R )

𝕄 : (s : 𝕄_spec) → (r : s R) → Set
𝕄 s r = codata [
| recv x : s A r t
| send x : (b : s B r (x recv) t) → 𝕄 s (s k r (x recv) b) ]

𝕄_code_spec : (s0 s1 : 𝕄_spec) → (s2 : Br 𝕄_spec s0 s1) → 𝕄_spec
𝕄_code_spec s0 s1 s2 = (
  R ≔ sig (
    r0 : s0 R,
    r1 : s1 R,
    r2 : s2 R r0 r1,
    x0 : 𝕄 s0 r0,
    x1 : 𝕄 s1 r1 ),
  A ≔ r ↦
    Idd𝕗 (s0 A (r r0)) (s1 A (r r1)) (s2 A (r r2)) (r x0 recv) (r x1 recv),
  B ≔ r a2 ↦
    Σ𝕗 (s0 B (r r0) (r x0 recv))
      (b0 ↦
       Σ𝕗 (s1 B (r r1) (r x1 recv))
         (b1 ↦
          Idd𝕗 (s0 B (r r0) (r x0 recv)) (s1 B (r r1) (r x1 recv))
            (s2 B (r r2) a2) b0 b1)),
  k ≔ r a2 b ↦ (
    r0 ≔ s0 k (r r0) (r x0 recv) (b .0),
    r1 ≔ s1 k (r r1) (r x1 recv) (b .1 .0),
    r2 ≔ s2 k (r r2) a2 (b .1 .1),
    x0 ≔ r x0 send (b .0),
    x1 ≔ r x1 send (b .1 .0)))

𝕄_encode : (s0 s1 : 𝕄_spec) → (s2 : Br 𝕄_spec s0 s1) → (r0 : s0 R) → (r1 : s1 R) → (r2 : s2 R r0 r1) → (x0 : 𝕄 s0 r0) → (x1 : 𝕄 s1 r1) → (x2 : rel 𝕄 s2 r2 x0 x1) → 𝕄 (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1)
𝕄_encode s0 s1 s2 r0 r1 r2 x0 x1 x2 = record {
  recv = x2 recv;
  send = λ b →
    𝕄_encode s0 s1 s2 (s0 k r0 (x0 recv) (b .0))
      (s1 k r1 (x1 recv) (b .1 .0)) (s2 k r2 (x2 recv) (b .1 .1))
      (x0 send (b .0)) (x1 send (b .1 .0)) (x2 send (b .1 .1)) }

𝕄_decode : (s0 s1 : 𝕄_spec) → (s2 : Br 𝕄_spec s0 s1) → (r0 : s0 R) → (r1 : s1 R) → (r2 : s2 R r0 r1) → (x0 : 𝕄 s0 r0) → (x1 : 𝕄 s1 r1) → (y2 : 𝕄 (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1)) → rel 𝕄 s2 r2 x0 x1
𝕄_decode s0 s1 s2 r0 r1 r2 x0 x1 y2 = record {
  recv = y2 recv;
  send = b ⤇
    𝕄_decode s0 s1 s2 (s0 k r0 (x0 recv) b⟨0⟩) (s1 k r1 (x1 recv) b⟨1⟩)
      (s2 k r2 (y2 recv) b⟨2⟩) (x0 send b⟨0⟩) (x1 send b⟨1⟩)
      (y2 send (b.0, (b.1, b⟨2⟩))) }

{- We need "coinductive extensionality" for eq.  The version we need says that the eq-types of 𝕄, dependent over an equality of indices, are again an 𝕄-type, similar to the codes for Br but without changing the spec.  In the application we only use this over a fixed index, but we can't *define* it in general without passing to a non-rfl equality of indices. -}

𝕄_bisim : (s : 𝕄_spec) → (r0 : s R) → (r1 : s R) → (r2 : eq (s R) r0 r1) → (x0 : 𝕄 s r0) → (x1 : 𝕄 s r1) → Set
𝕄_bisim s r0 r1 r2 x0 x1 = codata [
| recv x2 : eqd (s R) (r ↦ s A r t) r0 r1 r2 (x0 recv) (x1 recv)
| send x2
  : (b0 : s B r0 (x0 recv) t) (b1 : s B r1 (x1 recv) t)
    (b2
    : eqdd (s R) (r ↦ s A r t) (r a ↦ s B r a t) r0 r1 r2 (x0 recv)
        (x1 recv) (x2 recv) b0 b1)
    → 𝕄_bisim s (s k r0 (x0 recv) b0) (s k r1 (x1 recv) b1)
        (ap3d (s R) (r ↦ s A r t) (r a ↦ s B r a t) (s R) (s k) r0 r1 r2
           (x0 recv) (x1 recv) (x2 recv) b0 b1 b2) (x0 send b0)
        (x1 send b1) ]

postulate 𝕄_ext (s : 𝕄_spec) (r : s R) (x0 x1 : 𝕄 s r) (y2 : 𝕄_bisim s r r eq.rfl x0 x1) : eq (𝕄 s r) x0 x1

𝕄_encode_decode_bisim : (s0 s1 : 𝕄_spec) → (s2 : Br 𝕄_spec s0 s1) → (r0 : s0 R) → (r1 : s1 R) → (r2 : s2 R r0 r1) → (x0 : 𝕄 s0 r0) → (x1 : 𝕄 s1 r1) → (y2 : 𝕄 (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1)) → 𝕄_bisim (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1)
      (r0, r1, r2, x0, x1) eq.rfl
      (𝕄_encode s0 s1 s2 r0 r1 r2 x0 x1
         (𝕄_decode s0 s1 s2 r0 r1 r2 x0 x1 y2)) y2
𝕄_encode_decode_bisim s0 s1 s2 r0 r1 r2 x0 x1 y2 = record {
  recv = eq.rfl;
  send = λ b0 b1 b2 → match b2 [
  | eq.rfl ↦
      𝕄_encode_decode_bisim s0 s1 s2 (s0 k r0 (x0 recv) (b0 .0))
        (s1 k r1 (x1 recv) (b0 .1 .0)) (s2 k r2 (y2 recv) (b0 .1 .1))
        (x0 send (b0 .0)) (x1 send (b0 .1 .0)) (y2 send b0)] }

𝕄_encode_decode : (s0 s1 : 𝕄_spec) → (s2 : Br 𝕄_spec s0 s1) → (r0 : s0 R) → (r1 : s1 R) → (r2 : s2 R r0 r1) → (x0 : 𝕄 s0 r0) → (x1 : 𝕄 s1 r1) → (y2 : 𝕄 (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1)) → eq (𝕄 (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1))
      (𝕄_encode s0 s1 s2 r0 r1 r2 x0 x1
         (𝕄_decode s0 s1 s2 r0 r1 r2 x0 x1 y2)) y2
𝕄_encode_decode s0 s1 s2 r0 r1 r2 x0 x1 y2 = 𝕄_ext (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1)
      (𝕄_encode s0 s1 s2 r0 r1 r2 x0 x1
         (𝕄_decode s0 s1 s2 r0 r1 r2 x0 x1 y2)) y2
      (𝕄_encode_decode_bisim s0 s1 s2 r0 r1 r2 x0 x1 y2)

{- For the other direction we need a version of this for rel 𝕄. -}

refl_𝕄_bisim : (s0 s1 : 𝕄_spec) → (s2 : Br 𝕄_spec s0 s1) → (r0 : s0 R) → (r1 : s1 R) → (r20 : s2 R r0 r1) → (r21 : s2 R r0 r1) → (r22 : eq (s2 R r0 r1) r20 r21) → (x0 : 𝕄 s0 r0) → (x1 : 𝕄 s1 r1) → (x20 : rel 𝕄 s2 r20 x0 x1) → (x21 : rel 𝕄 s2 r21 x0 x1) → Set
refl_𝕄_bisim s0 s1 s2 r0 r1 r20 r21 r22 x0 x1 x20 x21 = codata [
| recv y2
  : eqd (s2 R r0 r1) (r2 ↦ s2 A r2 t (x0 recv) (x1 recv)) r20 r21 r22
      (x20 recv) (x21 recv)
| send y2
  : (b0 : s0 B r0 (x0 recv) t) (b1 : s1 B r1 (x1 recv) t)
    (b20 : s2 B r20 (x20 recv) t b0 b1) (b21 : s2 B r21 (x21 recv) t b0 b1)
    (b22
    : eqdd (s2 R r0 r1) (r2 ↦ s2 A r2 t (x0 recv) (x1 recv))
        (r2 a2 ↦ s2 B r2 a2 t b0 b1) r20 r21 r22 (x20 recv) (x21 recv)
        (y2 recv) b20 b21)
    → refl_𝕄_bisim s0 s1 s2 (s0 k r0 (x0 recv) b0) (s1 k r1 (x1 recv) b1)
        (s2 k r20 (x20 recv) b20) (s2 k r21 (x21 recv) b21)
        (ap3d (s2 R r0 r1) (r2 ↦ s2 A r2 t (x0 recv) (x1 recv))
           (r2 a2 ↦ s2 B r2 a2 t b0 b1)
           (s2 R (s0 k r0 (x0 recv) b0) (s1 k r1 (x1 recv) b1))
           (r2 a2 b2 ↦ s2 k r2 a2 b2) r20 r21 r22 (x20 recv) (x21 recv)
           (y2 recv) b20 b21 b22) (x0 send b0) (x1 send b1) (x20 send b20)
        (x21 send b21) ]

postulate refl_𝕄_ext (s0 s1 : 𝕄_spec) (s2 : Br 𝕄_spec s0 s1) (r0 : s0 R) (r1 : s1 R) (r2 : s2 R r0 r1) (x0 : 𝕄 s0 r0) (x1 : 𝕄 s1 r1) (x20 : rel 𝕄 s2 r2 x0 x1) (x21 : rel 𝕄 s2 r2 x0 x1) (y22 : refl_𝕄_bisim s0 s1 s2 r0 r1 r2 r2 eq.rfl x0 x1 x20 x21) : eq (rel 𝕄 s2 r2 x0 x1) x20 x21

𝕄_decode_encode_bisim : (s0 s1 : 𝕄_spec) → (s2 : Br 𝕄_spec s0 s1) → (r0 : s0 R) → (r1 : s1 R) → (r2 : s2 R r0 r1) → (x0 : 𝕄 s0 r0) → (x1 : 𝕄 s1 r1) → (x2 : rel 𝕄 s2 r2 x0 x1) → refl_𝕄_bisim s0 s1 s2 r0 r1 r2 r2 eq.rfl x0 x1
      (𝕄_decode s0 s1 s2 r0 r1 r2 x0 x1
         (𝕄_encode s0 s1 s2 r0 r1 r2 x0 x1 x2)) x2
𝕄_decode_encode_bisim s0 s1 s2 r0 r1 r2 x0 x1 x2 = record {
  recv = eq.rfl;
  send = λ b0 b1 b20 b21 b22 → match b22 [
  | eq.rfl ↦
      𝕄_decode_encode_bisim s0 s1 s2 (s0 k r0 (x0 recv) b0)
        (s1 k r1 (x1 recv) b1) (s2 k r2 (x2 recv) b20) (x0 send b0)
        (x1 send b1) (x2 send b20)] }

𝕄_decode_encode : (s0 s1 : 𝕄_spec) → (s2 : Br 𝕄_spec s0 s1) → (r0 : s0 R) → (r1 : s1 R) → (r2 : s2 R r0 r1) → (x0 : 𝕄 s0 r0) → (x1 : 𝕄 s1 r1) → (x2 : rel 𝕄 s2 r2 x0 x1) → eq (rel 𝕄 s2 r2 x0 x1)
      (𝕄_decode s0 s1 s2 r0 r1 r2 x0 x1
         (𝕄_encode s0 s1 s2 r0 r1 r2 x0 x1 x2)) x2
𝕄_decode_encode s0 s1 s2 r0 r1 r2 x0 x1 x2 = refl_𝕄_ext s0 s1 s2 r0 r1 r2 x0 x1
      (𝕄_decode s0 s1 s2 r0 r1 r2 x0 x1
         (𝕄_encode s0 s1 s2 r0 r1 r2 x0 x1 x2)) x2
      (𝕄_decode_encode_bisim s0 s1 s2 r0 r1 r2 x0 x1 x2)

Id_𝕄_iso : (s0 s1 : 𝕄_spec) → (s2 : Br 𝕄_spec s0 s1) → (r0 : s0 R) → (r1 : s1 R) → (r2 : s2 R r0 r1) → (x0 : 𝕄 s0 r0) → (x1 : 𝕄 s1 r1) → 𝕄 (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1) ≅ rel 𝕄 s2 r2 x0 x1
Id_𝕄_iso s0 s1 s2 r0 r1 r2 x0 x1 = adjointify (𝕄 (𝕄_code_spec s0 s1 s2) (r0, r1, r2, x0, x1))
      (rel 𝕄 s2 r2 x0 x1) (𝕄_decode s0 s1 s2 r0 r1 r2 x0 x1)
      (𝕄_encode s0 s1 s2 r0 r1 r2 x0 x1)
      (𝕄_encode_decode s0 s1 s2 r0 r1 r2 x0 x1)
      (𝕄_decode_encode s0 s1 s2 r0 r1 r2 x0 x1)

{- And finally we can prove that 𝕄-types are fibrant.  Again we have "recursive calls" to 𝕗𝕄 in each of the clauses, presumably justified by some kind of productivity. -}

𝕗𝕄 : (s : 𝕄_spec) → (r : s R) → isFibrant (𝕄 s r)
𝕗𝕄 s r = record {
  trr⟨p⟩ = λ x0 → record {
  recv = s⟨2⟩ A r⟨2⟩ f trr (x0 recv);
  send =
      rel 𝕗Π (s.2 B r⟨2⟩ (s.2 A r⟨2⟩ f liftr (x0 recv)) t)
        {b0 ↦ 𝕄 s⟨0⟩ (s.0 k r⟨0⟩ (x0 recv) b0)}
        {b1 ↦ 𝕄 s⟨1⟩ (s.1 k r⟨1⟩ (s.2 A r⟨2⟩ f trr (x0 recv)) b1)}
        (b ⤇ rel 𝕄 s⟨2⟩ (s.2 k r⟨2⟩ (s.2 A r⟨2⟩ f liftr (x0 recv)) b⟨2⟩))
        (s.2 B r⟨2⟩ (s.2 A r⟨2⟩ f liftr (x0 recv)) f)
        {b0 ↦ 𝕗𝕄 s⟨0⟩ (s.0 k r⟨0⟩ (x0 recv) b0)}
        {b1 ↦ 𝕗𝕄 s⟨1⟩ (s.1 k r⟨1⟩ (s.2 A r⟨2⟩ f trr (x0 recv)) b1)}
        (b ⤇ rel 𝕗𝕄 s⟨2⟩ (s.2 k r⟨2⟩ (s.2 A r⟨2⟩ f liftr (x0 recv)) b⟨2⟩))
        trr (b0 ↦ x0 send b0) };
  trl⟨p⟩ = λ x1 → record {
  recv = s⟨2⟩ A r⟨2⟩ f trl (x1 recv);
  send =
      rel 𝕗Π (s.2 B r⟨2⟩ (s.2 A r⟨2⟩ f liftl (x1 recv)) t)
        {b0 ↦ 𝕄 s⟨0⟩ (s.0 k r⟨0⟩ (s.2 A r⟨2⟩ f trl (x1 recv)) b0)}
        {b1 ↦ 𝕄 s⟨1⟩ (s.1 k r⟨1⟩ (x1 recv) b1)}
        (b ⤇ rel 𝕄 s⟨2⟩ (s.2 k r⟨2⟩ (s.2 A r⟨2⟩ f liftl (x1 recv)) b⟨2⟩))
        (s.2 B r⟨2⟩ (s.2 A r⟨2⟩ f liftl (x1 recv)) f)
        {b0 ↦ 𝕗𝕄 s⟨0⟩ (s.0 k r⟨0⟩ (s.2 A r⟨2⟩ f trl (x1 recv)) b0)}
        {b1 ↦ 𝕗𝕄 s⟨1⟩ (s.1 k r⟨1⟩ (x1 recv) b1)}
        (b ⤇ rel 𝕗𝕄 s⟨2⟩ (s.2 k r⟨2⟩ (s.2 A r⟨2⟩ f liftl (x1 recv)) b⟨2⟩))
        trl (b1 ↦ x1 send b1) };
  liftr⟨p⟩ = λ x0 → record {
  recv = s⟨2⟩ A r⟨2⟩ f liftr (x0 recv);
  send =
      rel 𝕗Π (s.2 B r⟨2⟩ (s.2 A r⟨2⟩ f liftr (x0 recv)) t)
        {b0 ↦ 𝕄 s⟨0⟩ (s.0 k r⟨0⟩ (x0 recv) b0)}
        {b1 ↦ 𝕄 s⟨1⟩ (s.1 k r⟨1⟩ (s.2 A r⟨2⟩ f trr (x0 recv)) b1)}
        (b ⤇ rel 𝕄 s⟨2⟩ (s.2 k r⟨2⟩ (s.2 A r⟨2⟩ f liftr (x0 recv)) b⟨2⟩))
        (s.2 B r⟨2⟩ (s.2 A r⟨2⟩ f liftr (x0 recv)) f)
        {b0 ↦ 𝕗𝕄 s⟨0⟩ (s.0 k r⟨0⟩ (x0 recv) b0)}
        {b1 ↦ 𝕗𝕄 s⟨1⟩ (s.1 k r⟨1⟩ (s.2 A r⟨2⟩ f trr (x0 recv)) b1)}
        (b ⤇ rel 𝕗𝕄 s⟨2⟩ (s.2 k r⟨2⟩ (s.2 A r⟨2⟩ f liftr (x0 recv)) b⟨2⟩))
        liftr (b0 ↦ x0 send b0) };
  liftl⟨p⟩ = λ x1 → record {
  recv = s⟨2⟩ A r⟨2⟩ f liftl (x1 recv);
  send =
      rel 𝕗Π (s.2 B r⟨2⟩ (s.2 A r⟨2⟩ f liftl (x1 recv)) t)
        {b0 ↦ 𝕄 s⟨0⟩ (s.0 k r⟨0⟩ (s.2 A r⟨2⟩ f trl (x1 recv)) b0)}
        {b1 ↦ 𝕄 s⟨1⟩ (s.1 k r⟨1⟩ (x1 recv) b1)}
        (b ⤇ rel 𝕄 s⟨2⟩ (s.2 k r⟨2⟩ (s.2 A r⟨2⟩ f liftl (x1 recv)) b⟨2⟩))
        (s.2 B r⟨2⟩ (s.2 A r⟨2⟩ f liftl (x1 recv)) f)
        {b0 ↦ 𝕗𝕄 s⟨0⟩ (s.0 k r⟨0⟩ (s.2 A r⟨2⟩ f trl (x1 recv)) b0)}
        {b1 ↦ 𝕗𝕄 s⟨1⟩ (s.1 k r⟨1⟩ (x1 recv) b1)}
        (b ⤇ rel 𝕗𝕄 s⟨2⟩ (s.2 k r⟨2⟩ (s.2 A r⟨2⟩ f liftl (x1 recv)) b⟨2⟩))
        liftl (b1 ↦ x1 send b1) };
  id⟨p⟩ = λ x0 x1 →
    𝕗eqv (𝕄 (𝕄_code_spec s⟨0⟩ s⟨1⟩ s⟨2⟩) (r.0, r⟨1⟩, r⟨2⟩, x0, x1))
      (rel 𝕄 s⟨2⟩ r⟨2⟩ x0 x1)
      (Id_𝕄_iso s⟨0⟩ s⟨1⟩ s⟨2⟩ r⟨0⟩ r⟨1⟩ r⟨2⟩ x0 x1)
      (𝕗𝕄 (𝕄_code_spec s⟨0⟩ s⟨1⟩ s⟨2⟩) (r.0, r⟨1⟩, r⟨2⟩, x0, x1)) }
