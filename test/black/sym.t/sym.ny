postulate A : Set
postulate a00 : A
postulate a01 : A
postulate a02 : Id A a00 a01
postulate a10 : A
postulate a11 : A
postulate a12 : Id A a10 a11
postulate a20 : Id A a00 a10
postulate a21 : Id A a01 a11
postulate a22 : Id (Id A) a02 a12 a20 a21

echo sym a22

echo sym (sym a22)

{- Symmetry is an involution -}
sym_involution : Id (Id (Id A) a02 a12 a20 a21) a22 (sym (sym a22))
sym_involution = refl a22

{- ap-ap preserves symmetry -}
postulate B : Set
postulate f : A → B

echo sym (refl (refl f) {a00} {a01} {a02} {a10} {a11} {a12} {a20} {a21} a22)
echo refl (refl f) {a00} {a10} {a20} {a01} {a11} {a21} {a02} {a12} (sym a22)

ap_sym : Id
      (B⁽ᵉᵉ⁾ {f a00} {f a10} (refl f {a00} {a10} a20) {f a01} {f a11}
         (refl f {a01} {a11} a21) (refl f {a00} {a01} a02)
         (refl f {a10} {a11} a12))
      (sym
         (refl (refl f) {a00} {a01} {a02} {a10} {a11} {a12} {a20} {a21} a22))
      (refl (refl f) {a00} {a10} {a20} {a01} {a11} {a21} {a02} {a12}
         (sym a22))
ap_sym = refl
      (sym
         (refl (refl f) {a00} {a01} {a02} {a10} {a11} {a12} {a20} {a21} a22))
