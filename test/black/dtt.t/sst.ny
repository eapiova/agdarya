 {- -*- agdarya-prog-args: ("-proofgeneral" "-dtt") -*- -}

{- Unary Gel-types -}
Gel : (A : Set) → (A' : A → Set) → Set⁽ᵈ⁾ A

Gel A A' = sig x ↦ ( ungel : A' x ) {- The definition of semi-simplicial types -}

SST : Set

SST = codata [ z X : Set | s X : (X z) → SST⁽ᵈ⁾ X ] -- Extracting some low-dimensional simplices

0s : (X : SST) → Set

0s X = X z

1s : (X : SST) → (x₀ x₁ : 0s X) → Set

1s X x₀ x₁ = X s x₀ z x₁

2s : (X : SST) → (x₀ x₁ : 0s X) → (x₀₁ : 1s X x₀ x₁) → (x₂ : 0s X) →
     (x₀₂ : 1s X x₀ x₂) → (x₁₂ : 1s X x₁ x₂)
     → Set

2s X x₀ x₁ x₀₁ x₂ x₀₂ x₁₂ = X s x₀ s {x₁} x₀₁ z {x₂} x₀₂ x₁₂

3s : (X : SST) → (x₀ x₁ : 0s X) → (x₀₁ : 1s X x₀ x₁) → (x₂ : 0s X) →
     (x₀₂ : 1s X x₀ x₂) → (x₁₂ : 1s X x₁ x₂) →
     (x₀₁₂ : 2s X x₀ x₁ x₀₁ x₂ x₀₂ x₁₂) → (x₃ : 0s X) → (x₀₃ : 1s X x₀ x₃) →
     (x₁₃ : 1s X x₁ x₃) → (x₀₁₃ : 2s X x₀ x₁ x₀₁ x₃ x₀₃ x₁₃) →
     (x₂₃ : 1s X x₂ x₃) → (x₀₂₃ : 2s X x₀ x₂ x₀₂ x₃ x₀₃ x₂₃) →
     (x₁₂₃ : 2s X x₁ x₂ x₁₂ x₃ x₁₃ x₂₃)
     → Set

3s X x₀ x₁ x₀₁ x₂ x₀₂ x₁₂ x₀₁₂ x₃ x₀₃ x₁₃ x₀₁₃ x₂₃ x₀₂₃ x₁₂₃
=
  X s x₀ s {x₁} x₀₁ s {x₂} {x₀₂} {x₁₂} x₀₁₂ z {x₃} {x₀₃} {x₁₃} x₀₁₃ {x₂₃}
    x₀₂₃ x₁₂₃ {- Singular SSTs, based on the Martin-Lof jdentity type for now. -}

eq : (A : Set) → (x : A) → A → Set

eq A x = data [ rfl : eq A x x ]

Sing : (A : Set) → SST

Sing A = record { z = A; s = λ x → Sing⁽ᵈ⁾ (Gel A (y ↦ eq A x y)) } {- We normalize some low-dimensional simplex types of singular SSTs. -}

postulate A : Set

echo 0s (Sing A)

postulate a₀ : 0s (Sing A)

postulate a₁ : 0s (Sing A)

echo 1s (Sing A) a₀ a₁

postulate a₀₁ : 1s (Sing A) a₀ a₁

postulate a₂ : 0s (Sing A)

postulate a₀₂ : 1s (Sing A) a₀ a₂

postulate a₁₂ : 1s (Sing A) a₁ a₂

echo 2s (Sing A) a₀ a₁ a₀₁ a₂ a₀₂ a₁₂

postulate a₀₁₂ : 2s (Sing A) a₀ a₁ a₀₁ a₂ a₀₂ a₁₂

postulate a₃ : 0s (Sing A)

postulate a₀₃ : 1s (Sing A) a₀ a₃

postulate a₁₃ : 1s (Sing A) a₁ a₃

postulate a₀₁₃ : 2s (Sing A) a₀ a₁ a₀₁ a₃ a₀₃ a₁₃

postulate a₂₃ : 1s (Sing A) a₂ a₃

postulate a₀₂₃ : 2s (Sing A) a₀ a₂ a₀₂ a₃ a₀₃ a₂₃

postulate a₁₂₃ : 2s (Sing A) a₁ a₂ a₁₂ a₃ a₁₃ a₂₃

echo 3s (Sing A) a₀ a₁ a₀₁ a₂ a₀₂ a₁₂ a₀₁₂ a₃ a₀₃ a₁₃ a₀₁₃ a₂₃ a₀₂₃ a₁₂₃ {- The empty SST -}

sst.∅ : SST

sst.∅ = record { z = data []; s = λ { } } {- The unit SST -}

sst.𝟙 : SST

sst.𝟙 = record { z = sig (); s = λ _ → sst.𝟙⁽ᵈ⁾ } {- Binary products of SSTs -}

sst_prod : (X Y : SST) → SST

sst_prod X Y
=
  record {
z = sig (
    fst : X z,
    snd : Y z );
s = λ xy → sst_prod⁽ᵈ⁾ (X s (xy fst)) (Y s (xy snd)) } {- Dependent Σ-SSTs require symmetry! -}

sst.Σ : (X : SST) → (Y : SST⁽ᵈ⁾ X) → SST

sst.Σ X Y
=
  record {
z = sig (
    fst : X z,
    snd : Y z fst );
s = λ xy → sst.Σ⁽ᵈ⁾ (X s (xy fst)) (sym (Y s {xy fst} (xy snd))) } {-
We can check this by hand too:

sst.Σ⁽ᵈ⁾ : (X : SST) (X' : SST⁽ᵈ⁾ X) (Y : SST⁽ᵈ⁾ X) (Y' : SST⁽ᵈᵈ⁾ X X' Y) : SST⁽ᵈ⁾ (sst.Σ X Y)
sst.Σ⁽ᵈ⁾ X (X s (xy fst)) Y : SST⁽ᵈᵈ⁾ X (X s (xy fst)) Y → SST⁽ᵈ⁾ (sst.Σ X Y)
X : SST
xy fst : X z
X s (xy fst) : SST⁽ᵈ⁾ X
Y : SST⁽ᵈ⁾ X
xy snd : Y z (xy fst)
− s : (X : SST) → X z → SST⁽ᵈ⁾ X
− s⁽ᵈ⁾ : {X : SST} (X' : SST⁽ᵈ⁾ X) (x : X z) (x' : X' z x) → SST⁽ᵈᵈ⁾ X X' (X s x)
Y s⁽ᵈ⁾ (xy fst) (xy snd) : SST⁽ᵈᵈ⁾ X Y (X s (xy fst))

So the type of "Y s⁽ᵈ⁾ (xy fst) (xy snd)" is indeed symmetrized from what "sst.Σ⁽ᵈ⁾ X (X s (xy fst)) Y" expects for its argument.  (Note that ".s⁽ᵈ⁾" is not Agdarya syntax; the field projection has the same syntax at every dimension, I just wrote this for clarity in the by-hand version.)
-}

{- Constant displayed SSTs also require symmetry, as noted in the paper. -}
sst.const : (X Y : SST) → SST⁽ᵈ⁾ X

sst.const X Y
=
  record {
z = sig _ ↦ (
    ungel : Y z );
s = {x} y ↦ sym (sst.const⁽ᵈ⁾ (X s x) (Y s (y ungel))) } {- Using constant displayed SSTs, we can define binary sum SSTs. -}

sst.sum : (X Y : SST) → SST

sst.sum X Y
=
  record {
z = data [
  | inl (_ : X z)
  | inr (_ : Y z) ];
s = λ {
  inl x → sst.sum⁽ᵈ⁾ (X s x) (sst.const Y sst.∅);
  inr y → sst.sum⁽ᵈ⁾ (sst.const X sst.∅) (Y s y)} } {- Augmented SSTs are another displayed coinductive. -}

ASST : Set

ASST = codata [ z X : Set | s X : ASST⁽ᵈ⁾ X ] {- As is pointedness of an SST. -}

sst_pt : (X : SST) → Set

sst_pt X = codata [ z p : X z | s p : sst_pt⁽ᵈ⁾ (X s (p z)) p ] {- And maps of SSTs. -}

sst.hom : (X Y : SST) → Set

sst.hom X Y
=
  codata [
| z f : X z → Y z
| s f : (x : X z) → sst.hom⁽ᵈ⁾ (X s x) (Y s (f z x)) f ] {- Identities and composition for maps -}

sst.id : (X : SST) → sst.hom X X

sst.id X = record { z = λ x → x; s = λ x → sst.id⁽ᵈ⁾ (X s x) }

sst.comp : (X Y Z : SST) → (g : sst.hom Y Z) → (f : sst.hom X Y)
           → sst.hom X Z

sst.comp X Y Z g f
=
  record {
z = λ x → g z (f z x);
s = λ x →
    sst.comp⁽ᵈ⁾ (X s x) (Y s (f z x)) (Z s (g z (f z x))) (g s (f z x))
      (f s x) } {- Universal maps -}

sst.abort : (X : SST) → sst.hom sst.∅ X

sst.abort X = record { z = λ { }; s = λ { } }

sst.uniq : (X : SST) → sst.hom X sst.𝟙

sst.uniq X = record { z = λ _ → (); s = λ x → sst.uniq⁽ᵈ⁾ (X s x) }

sst_pair : (X Y Z : SST) → (f : sst.hom X Y) → (g : sst.hom X Z)
           → sst.hom X (sst_prod Y Z)

sst_pair X Y Z f g
=
  record {
z = λ x → (f z x, g z x);
s = λ x → sst_pair⁽ᵈ⁾ (X s x) (Y s (f z x)) (Z s (g z x)) (f s x) (g s x) } {- Copairing requires a displayed version of abort.  And for that, we can't match directly against (x' ungel) since it isn't a variable, so we have to define a helper function first. -}

sst.abortz : (X : Set) → sst.∅ z → X

sst.abortz X = λ { }

sst.const_abort : (X Y : SST) → (Y' : SST⁽ᵈ⁾ Y) → (f : sst.hom X Y)
                  → sst.hom⁽ᵈ⁾ (sst.const X sst.∅) Y' f

sst.const_abort X Y Y' f
=
  record {
z = {x} x' ↦ sst.abortz (Y' z (f z x)) (x' ungel);
s = {x} x' ↦
    sst.abortz
      {- Ideally, this big long argument should be obtainable by unification. -}
      (sst.hom⁽ᵈᵈ⁾ {X} {sst.const X sst.∅} {X s x}
         (sym (sst.const⁽ᵈ⁾ (X s x) (sst.∅ s (x' ungel)))) {Y} {Y'}
         {Y s (f z x)}
         (Y' s {f z x} (sst.abortz (Y' z (f z x)) (x' ungel))) {f}
         (sst.const_abort X Y Y' f) (f s x)) (x' ungel) }

sst.copair : (X Y Z : SST) → (f : sst.hom X Z) → (g : sst.hom Y Z)
             → sst.hom (sst.sum X Y) Z

sst.copair X Y Z f g
=
  record {
z = λ {
  inl x → f z x;
  inr y → g z y};
s = λ {
  inl x →

    sst.copair⁽ᵈ⁾ (X s x) (sst.const Y sst.∅) (Z s (f z x)) (f s x)
      (sst.const_abort Y Z (Z s (f z x)) g);
  inr y →

    sst.copair⁽ᵈ⁾ (sst.const X sst.∅) (Y s y) (Z s (g z y))
      (sst.const_abort X Z (Z s (g z y)) f) (g s y)} }
