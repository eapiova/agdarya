postulate A : Set
postulate B : A → Set
postulate a : A
postulate f : (x : A) → B x

synth (x ↦ f x) a
echo (x ↦ f x) a

unit : Set
unit = sig ()

synth (x ↦ ()) a : unit
echo (x ↦ ()) a : unit

postulate a₀ : A
postulate a₁ : A
postulate a₂ : Id A a₀ a₁

synth ap (x ↦ f x) a₂
echo ap (x ↦ f x) a₂

synth ap (x ↦ ()) a₂ : Id unit () ()
echo ap (x ↦ ()) a₂ : Id unit () ()

postulate a00 : A
postulate a01 : A
postulate a02 : Id A a00 a01
postulate a10 : A
postulate a11 : A
postulate a12 : Id A a10 a11
postulate a20 : Id A a00 a10
postulate a21 : Id A a01 a11
postulate a22 : Id (Id A) a02 a12 a20 a21

synth refl (refl (x ↦ f x)) a22
echo refl (refl (x ↦ f x)) a22

synth refl (refl (x ↦ ())) a22 : unit⁽ᵉᵉ⁾ {()} {()} () {()} {()} () () ()
echo refl (refl (x ↦ ())) a22 : unit⁽ᵉᵉ⁾ {()} {()} () {()} {()} () () ()

postulate g : (x : A) → unit → B x

synth (x (y : unit) ↦ g x y) a ()
echo (x (y : unit) ↦ g x y) a ()

synth (x (y : unit) ↦ ()) a () : unit
echo (x (y : unit) ↦ ()) a () : unit

synth ((y : unit) x ↦ g x y) () a
echo ((y : unit) x ↦ g x y) () a

synth ((y : unit) x ↦ ()) () a : unit
echo ((y : unit) x ↦ ()) () a : unit

synth refl (x (y : unit) ↦ g x y) a₂ {()} {()} ()
echo refl (x (y : unit) ↦ g x y) a₂ {()} {()} ()

synth refl ((y : unit) x ↦ g x y) {()} {()} () a₂
echo refl ((y : unit) x ↦ g x y) {()} {()} () a₂

synth refl (x (y : unit) ↦ ()) a₂ {()} {()} () : Id unit () ()
echo refl (x (y : unit) ↦ ()) a₂ {()} {()} () : Id unit () () 

synth refl ((y : unit) x ↦ ()) {()} {()} () a₂ : Id unit () ()
echo refl ((y : unit) x ↦ ()) {()} {()} () a₂ : Id unit () ()

dunit : (x : A) → Set
dunit x = sig ()
postulate h : (x : A) → dunit x → B x

synth (x (y : dunit x) ↦ h x y) a ()
echo (x (y : dunit x) ↦ h x y) a ()

synth (x (y : dunit x) ↦ ()) a () : unit
echo (x (y : dunit x) ↦ ()) a () : unit

synth refl (x (y : dunit x) ↦ h x y) a₂ {()} {()} ()
echo refl (x (y : dunit x) ↦ h x y) a₂ {()} {()} ()

synth refl (x (y : dunit x) ↦ ()) a₂ {()} {()} () : Id unit () () 
echo refl (x (y : dunit x) ↦ ()) a₂ {()} {()} () : Id unit () () 
