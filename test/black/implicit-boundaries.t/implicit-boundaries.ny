

postulate A : Set

postulate B : Set

postulate f : A → B

postulate a0 : A

postulate a1 : A

postulate a2 : Id A a0 a1 {- Since function boundaries are implicit, we don't give a0 and a1. -}

echo refl f a2 {- Similarly for cubes -}

postulate a00 : A

postulate a01 : A

postulate a02 : Id A a00 a01

postulate a10 : A

postulate a11 : A

postulate a12 : Id A a10 a11

postulate a20 : Id A a00 a10

postulate a21 : Id A a01 a11

postulate a22 : Id (Id A) a02 a12 a20 a21

echo refl (refl f) a22 {- Similarly for types *of* cubes -}

echo Id (Id A) a02 a12 a20 a21

echo Id (Id A) {a00} {a01} a02 a12 a20 a21

echo Id (Id A) {a00} {a01} a02 {a10} {a11} a12 a20 a21

echo Id (Id A) a02 {a10} {a11} a12 a20 a21 {- The dimension of the argument can be greater than the dimension of the application (this is a 1-dimensional application). -}

postulate g : (x0 : A) (x1 : A) (x2 : Id A x0 x1) → B

echo refl g a02 a12 a22 {- Even when printing implicit arguments is off, they are included if the corresponding primary argument doesn't synthesize. -}

postulate C : Set

A×B : Set

A×B = sig ( fst : A, snd : B )

postulate h : A×B → C

postulate b0 : B

postulate b1 : B

postulate b2 : Id B b0 b1

echo refl h {(a0, b0)} {(a1, b1)} (a2, b2)

postulate b00 : B

postulate b01 : B

postulate b02 : Id B b00 b01

postulate b10 : B

postulate b11 : B

postulate b12 : Id B b10 b11

postulate b20 : Id B b00 b10

postulate b21 : Id B b01 b11

postulate b22 : Id (Id B) b02 b12 b20 b21

echo refl (refl h) {(a00, b00)} {(a01, b01)} {(a02, b02)} {(a10, b10)}
       {(a11, b11)} {(a12, b12)} {(a20, b20)} {(a21, b21)} (a22, b22)

echo refl (refl h) {(a00, b00)} {(a01, b01)} {(a02, b02)} {(a10, b10)}
       {(a11, b11)} {(a12, b12)} {(a20, b20)} {(a21, b21)} (a22, b22)

postulate ab10 : A×B

postulate ab11 : A×B

postulate ab12 : Id A×B ab10 ab11

postulate ab20 : Id A×B (a00, b00) ab10

postulate ab21 : Id A×B (a01, b01) ab11

postulate ab22 : Id (Id A×B) {(a00, b00)} {(a01, b01)} (a02, b02) {ab10} {ab11} ab12 ab20 ab21

echo ab22

echo refl (refl h) {(a00, b00)} {(a01, b01)} {(a02, b02)} {ab10} {ab11}
       {ab12} {ab20} {ab21} ab22
