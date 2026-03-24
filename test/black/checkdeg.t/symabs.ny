postulate A : Set
postulate a00 : A
postulate a01 : A
postulate a02 : Id A a00 a01
postulate a10 : A
postulate a11 : A
postulate a12 : Id A a10 a11
postulate a20 : Id A a00 a10
postulate a21 : Id A a01 a11
postulate a22 : refl (Id A) a02 a12 a20 a21

postulate B : Set
postulate b00 : B
postulate b01 : B
postulate b02 : Id B b00 b01
postulate b10 : B
postulate b11 : B
postulate b12 : Id B b10 b11
postulate b20 : Id B b00 b10
postulate b21 : Id B b01 b11
postulate b22 : refl (Id B) b02 b12 b20 b21

prod : (X Y : Set) → Set
prod X Y = sig ( fst : X, snd : Y )

ab22 : Id (Id (prod A B)) {(a00, b00)} {(a01, b01)} (a02, b02) {(a10, b10)}
      {(a11, b11)} (a12, b12) (a20, b20) (a21, b21)
ab22 = (a22, b22)

sym_ab22 : Id (Id (prod A B)) {(a00, b00)} {(a10, b10)} (a20, b20) {(a01, b01)}
      {(a11, b11)} (a21, b21) (a02, b02) (a12, b12)
sym_ab22 = (sym a22, sym b22)

{- This one requires symmetry to check in addition to synthesize, although it could also work with degeneracies applied to tuples. -}
sym_ab22' : Id (Id (prod A B)) {(a00, b00)} {(a10, b10)} (a20, b20) {(a01, b01)}
      {(a11, b11)} (a21, b21) (a02, b02) (a12, b12)
sym_ab22' = sym (a22, b22)

{- To make sure we're testing that symmetry checks, we do one with abstractions too, which degeneracies don't push through. -}

postulate f00 : A → B
postulate f01 : A → B
postulate f02 : Id (A → B) f00 f01
postulate f10 : A → B
postulate f11 : A → B
postulate f12 : Id (A → B) f10 f11
postulate f20 : Id (A → B) f00 f10
postulate f21 : Id (A → B) f01 f11
postulate f22 : Id (Id (A → B)) f02 f12 f20 f21

etaf22 : Id (Id (A → B)) f02 f12 f20 f21
etaf22 = (x ⤇ f22 x⟨22⟩)
eta_symf22 : Id (Id (A → B)) f20 f21 f02 f12
eta_symf22 = (x ⤇ sym (f22 (sym x⟨22⟩)))

eta_symf22' : Id (Id (A → B)) f20 f21 f02 f12
eta_symf22' = sym (x ⤇ f22 x⟨22⟩)
