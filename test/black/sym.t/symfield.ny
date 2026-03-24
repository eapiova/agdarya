postulate B : Set
A : Set
A = sig ( unwrap : B )
postulate a00 : A
postulate a01 : A
postulate a02 : Id A a00 a01
postulate a10 : A
postulate a11 : A
postulate a12 : Id A a10 a11
postulate a20 : Id A a00 a10
postulate a21 : Id A a01 a11
postulate a22 : refl (Id A) a02 a12 a20 a21

echo (sym a22) unwrap
echo sym (a22 unwrap)

Jd : (X : Set) → (x : X) → X → Set
Jd X x = data [ rfl : Jd X x x ]

test : Jd (refl (Id B) (a20 unwrap) (a21 unwrap) (a02 unwrap) (a12 unwrap))
      ((sym a22) unwrap) (sym (a22 unwrap))
test = rfl
