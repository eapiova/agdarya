postulate A : Set

{- Bottom face -}
postulate a000 : A
postulate a001 : A
postulate a002 : Id A a000 a001
postulate a010 : A
postulate a011 : A
postulate a012 : Id A a010 a011
postulate a020 : Id A a000 a010
postulate a021 : Id A a001 a011
postulate a022 : Id (Id A) a002 a012 a020 a021

{- Top face -}
postulate a100 : A
postulate a101 : A
postulate a102 : Id A a100 a101
postulate a110 : A
postulate a111 : A
postulate a112 : Id A a110 a111
postulate a120 : Id A a100 a110
postulate a121 : Id A a101 a111
postulate a122 : Id (Id A) a102 a112 a120 a121

{- Front face -}
postulate a200 : Id A a000 a100
postulate a201 : Id A a001 a101
postulate a202 : Id (Id A) a002 a102 a200 a201

{- Back face -}
postulate a210 : Id A a010 a110
postulate a211 : Id A a011 a111
postulate a212 : Id (Id A) a012 a112 a210 a211

{- Left face -}
postulate a220 : Id (Id A) a020 a120 a200 a210

{- Right face -}
postulate a221 : Id (Id A) a021 a121 a201 a211

{- Center -}
postulate a222 : Id (Id (Id A)) a022 a122 a202 a212 a220 a221

{- Nothing -}
echo a222
echo a222⁽¹²³⁾

{- One transposition -}
echo sym a222
echo a222⁽¹³²⁾

{- The other transposition -}
sym2 : (x00 x01 : A) → (x02 : Id A x00 x01) → (x10 x11 : A) → (x12 : Id A x10 x11) → (x20 : Id A x00 x10) → (x21 : Id A x01 x11) → (x22 : Id (Id A) x02 x12 x20 x21) → Id (Id A) x20 x21 x02 x12
sym2 x00 x01 x02 x10 x11 x12 x20 x21 x22 = sym x22
echo refl sym2 {a000} {a001} a002 {a010} {a011} a012 {a020} {a021} a022
       {a100} {a101} a102 {a110} {a111} a112 {a120} {a121} a122 {a200} {a201}
       a202 {a210} {a211} a212 {a220} {a221} a222
echo a222⁽²¹³⁾

{- The two sides of the braid equation, in stages -}

{- apsym-sym -}
echo refl sym2 {a000} {a010} a020 {a001} {a011} a021 {a002} {a012} (sym a022)
       {a100} {a110} a120 {a101} {a111} a121 {a102} {a112} (sym a122) {a200}
       {a210} a220 {a201} {a211} a221 {a202} {a212} (sym a222)
echo a222⁽³¹²⁾

{- sym-apsym-sym -}
echo sym
       (refl sym2 {a000} {a010} a020 {a001} {a011} a021 {a002} {a012}
          (sym a022) {a100} {a110} a120 {a101} {a111} a121 {a102} {a112}
          (sym a122) {a200} {a210} a220 {a201} {a211} a221 {a202} {a212}
          (sym a222))
echo a222⁽³²¹⁾

{- sym-apsym -}
echo sym
       (refl sym2 {a000} {a001} a002 {a010} {a011} a012 {a020} {a021} a022
          {a100} {a101} a102 {a110} {a111} a112 {a120} {a121} a122 {a200}
          {a201} a202 {a210} {a211} a212 {a220} {a221} a222)
echo a222⁽²³¹⁾

{- apsym-sym-apsym -}
echo refl sym2 {a000} {a100} a200 {a001} {a101} a201 {a002} {a102} (sym a202)
       {a010} {a110} a210 {a011} {a111} a211 {a012} {a112} (sym a212) {a020}
       {a120} (sym a220) {a021} {a121} (sym a221) {a022} {a122}
       (sym
          (refl sym2 {a000} {a001} a002 {a010} {a011} a012 {a020} {a021} a022
             {a100} {a101} a102 {a110} {a111} a112 {a120} {a121} a122 {a200}
             {a201} a202 {a210} {a211} a212 {a220} {a221} a222))
echo a222⁽³²¹⁾

braid : Id
      (A⁽ᵉᵉᵉ⁾ (sym a220) (sym a221) (sym a202) (sym a212) (sym a022)
         (sym a122))
      (sym
         (refl sym2 a020 a021 (sym a022) a120 a121 (sym a122) a220 a221
            (sym a222)))
      (refl sym2 a200 a201 (sym a202) a210 a211 (sym a212) (sym a220)
         (sym a221)
         (sym (refl sym2 a002 a012 a022 a102 a112 a122 a202 a212 a222)))
braid = refl a222⁽³²¹⁾

{- Alternative notation for the braid equation -}

braid2 : Id
      (A⁽ᵉᵉᵉ⁾ (sym a220) (sym a221) (sym a202) (sym a212) (sym a022)
         (sym a122)) a222⁽²¹³⁾⁽¹³²⁾⁽²¹³⁾ a222⁽¹³²⁾⁽²¹³⁾⁽¹³²⁾
braid2 = refl a222⁽³²¹⁾
