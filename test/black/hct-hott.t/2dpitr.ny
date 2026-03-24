 {- -*- agdarya-prog-args: ("-proofgeneral" "-parametric" "-direction" "p,rel,Br") -*- -}

import "isfibrant"
import "fibrant_types"
import "bookhott"
import "hott_bookhott"
import "homotopy"

postulate A00 : Fib

postulate A01 : Fib

postulate A02 : Br Fib A00 A01

postulate A10 : Fib

postulate A11 : Fib

postulate A12 : Br Fib A10 A11

postulate A20 : Br Fib A00 A10

postulate A21 : Br Fib A01 A11

postulate A22 : Fib⁽ᵖᵖ⁾ A02 A12 A20 A21

postulate B00 : A00 t → Fib

postulate B01 : A01 t → Fib

postulate B02 : Br ((X ↦ X → Fib) : Set → Set) (A02 t) B00 B01

postulate B10 : A10 t → Fib

postulate B11 : A11 t → Fib

postulate B12 : Br ((X ↦ X → Fib) : Set → Set) (A12 t) B10 B11

postulate B20 : Br ((X ↦ X → Fib) : Set → Set) (A20 t) B00 B10

postulate B21 : Br ((X ↦ X → Fib) : Set → Set) (A21 t) B01 B11

postulate B22 : ((X ↦ X → Fib) : Set → Set)⁽ᵖᵖ⁾ (A22 t) B02 B12 B20 B21

postulate f00 : (x00 : A00 t) → B00 x00 t

postulate f01 : (x01 : A01 t) → B01 x01 t

postulate f02
  : Br ((λ X Y → Π𝕗 X Y) : ((X : Fib) (Y : X t → Fib) → Fib)) A02 B02 t f00
      f01

postulate a10 : A10 t

postulate a11 : A11 t

postulate a12 : A12 t a10 a11

echo ((λ X Y → Π𝕗 X Y) : ((X : Fib) (Y : X t → Fib) → Fib))⁽ᵖᵖ⁾ A22 B22 f
       trr⟨1⟩ f02 a12

postulate f10 : (x10 : A10 t) → B10 x10 t

postulate f11 : (x11 : A11 t) → B11 x11 t

postulate f12
  : Br ((λ X Y → Π𝕗 X Y) : ((X : Fib) (Y : X t → Fib) → Fib)) A12 B12 t f10
      f11

postulate f20
  : Br ((λ X Y → Π𝕗 X Y) : ((X : Fib) (Y : X t → Fib) → Fib)) A20 B20 t f00
      f10

postulate f21
  : Br ((λ X Y → Π𝕗 X Y) : ((X : Fib) (Y : X t → Fib) → Fib)) A21 B21 t f01
      f11

postulate a01 : A01 t

postulate a21 : A21 t a01 a11

echo ((λ X Y → Π𝕗 X Y) : ((X : Fib) (Y : X t → Fib) → Fib))⁽ᵖᵖ⁾ A22 B22 f
       id⟨1⟩ f02 f12 trr f20 a21 {- Double-check that the computed result indeed has the correct type. -}

echo B22 (A22 f id⟨1⟩ (A02 f liftl a01) (A12 f liftl a11) liftl a21) f
       id⟨1⟩ (f02 (A02 f liftl a01)) (f12 (A12 f liftl a11)) trr⟨1⟩
       (f20 (A22 f id⟨1⟩ (A02 f liftl a01) (A12 f liftl a11) trl a21)) {- That is, these have the same type: -}

echo (A22 f id⟨1⟩ (A02 f liftl a01) (A12 f liftl a11) trl a21)

echo (A22 f trl⟨2⟩ a21)

echo (A22 f id⟨1⟩ (A02 f liftl a01) (A12 f liftl a11) liftl a21)

echo (sym (A22 f liftl⟨2⟩ a21))

echo B22 (sym (A22 f liftl⟨2⟩ a21)) f id⟨1⟩ (f02 (A02 f liftl a01))
       (f12 (A12 f liftl a11)) trr (f20 ((A22 f trl⟨2⟩ a21)))

echo sym B22 (A22 f liftl⟨2⟩ a21) f trr⟨1⟩ (f20 (A22 f trl⟨2⟩ a21))
{- sym B22 (sym A22 f liftl⟨1⟩ a21) f trr⟨1⟩ (f20 (sym A22 f trl⟨1⟩ a21))

: B21 a21
t (B02 (A02 f liftl a01) f trr (f00 (A02 f trl a01)))
(B12 (A12 f liftl a11) f trr (f10 (A12 f trl a11)))
-}
