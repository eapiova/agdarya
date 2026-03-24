{- The "double square root", a higher coinductive type with a 2-dimensional field. -}
postulate A : Set

√√A : Set
√√A = codata [ rroot⟨ee⟩ x : A ]

{- To project this out, we need a doubly degenerated instance.  With a triply degenerated instance, we can project out all six fields. -}
postulate s000 : √√A

postulate s001 : √√A

postulate s002 : Id √√A s000 s001

postulate s010 : √√A

postulate s011 : √√A

postulate s012 : Id √√A s010 s011

postulate s020 : Id √√A s000 s010

postulate s021 : Id √√A s001 s011

postulate s022 : √√A⁽ᵉᵉ⁾ s002 s012 s020 s021

postulate s100 : √√A

postulate s101 : √√A

postulate s102 : Id √√A s100 s101

postulate s110 : √√A

postulate s111 : √√A

postulate s112 : Id √√A s110 s111

postulate s120 : Id √√A s100 s110

postulate s121 : Id √√A s101 s111

postulate s122 : √√A⁽ᵉᵉ⁾ s102 s112 s120 s121

postulate s200 : Id √√A s000 s100

postulate s201 : Id √√A s001 s101

postulate s202 : √√A⁽ᵉᵉ⁾ s002 s102 s200 s201

postulate s210 : Id √√A s010 s110

postulate s211 : Id √√A s011 s111

postulate s212 : √√A⁽ᵉᵉ⁾ s012 s112 s210 s211

postulate s220 : √√A⁽ᵉᵉ⁾ s020 s120 s200 s210

postulate s221 : √√A⁽ᵉᵉ⁾ s021 s121 s201 s211

postulate s222 : √√A⁽ᵉᵉᵉ⁾ s022 s122 s202 s212 s220 s221

{- Here are the six fields, with their six different types.  Note that they all compute to rroot⟨12⟩ of a symmetrized s222. -}
echo s222 rroot⟨12⟩

echo s222 rroot⟨13⟩

echo s222 rroot⟨23⟩

echo s222 rroot⟨21⟩

echo s222 rroot⟨32⟩

echo s222 rroot⟨31⟩

{- To compute with concrete instances, let's consider instead the double square root of a type of squares, to make it easier to define elements. -}
ID2 : (X : Set) → Set
ID2 X = sig (
  x00 : X,
  x01 : X,
  x02 : Id X x00 x01,
  x10 : X,
  x11 : X,
  x12 : Id X x10 x11,
  x20 : Id X x00 x10,
  x21 : Id X x01 x11,
  x22 : X⁽ᵉᵉ⁾ x02 x12 x20 x21 )

√√ID2A : Set
√√ID2A = codata [ rroot⟨ee⟩ x : ID2 A ]

t : (a : A) → √√ID2A
t a = record {
  rroot⟨ee⟩ = (
    a.00,
    a⟨01⟩,
    a⟨02⟩,
    a⟨10⟩,
    a⟨11⟩,
    a⟨12⟩,
    a⟨20⟩,
    a⟨21⟩,
    a⟨22⟩) }

postulate a00 : A

postulate a01 : A

postulate a02 : Id A a00 a01

postulate a10 : A

postulate a11 : A

postulate a12 : Id A a10 a11

postulate a20 : Id A a00 a10

postulate a21 : Id A a01 a11

postulate a22 : A⁽ᵉᵉ⁾ a02 a12 a20 a21

ta = t⁽ᵉᵉ⁾ a22

{- ta has two projectable fields, rroot⟨12⟩ and rroot⟨2⟩1. -}
echo ta rroot⟨12⟩

echo ta rroot⟨21⟩

{- They are transposed -}
echo ta rroot⟨12⟩ x00

echo ta rroot⟨21⟩ x00

echo ta rroot⟨12⟩ x01

echo ta rroot⟨21⟩ x01

echo ta rroot⟨12⟩ x02

echo ta rroot⟨21⟩ x02

echo ta rroot⟨12⟩ x10

echo ta rroot⟨21⟩ x10

echo ta rroot⟨12⟩ x11

echo ta rroot⟨21⟩ x11

echo ta rroot⟨12⟩ x12

echo ta rroot⟨21⟩ x12

echo ta rroot⟨12⟩ x20

echo ta rroot⟨21⟩ x20

echo ta rroot⟨12⟩ x21

echo ta rroot⟨21⟩ x21

echo ta rroot⟨12⟩ x22

echo ta rroot⟨21⟩ x22

{- They are related by symmetry -}
echo ta rroot⟨21⟩

echo (sym ta) rroot⟨12⟩

{- ...and so are their fields. -}
echo ta rroot⟨21⟩ x01

echo (sym ta) rroot⟨12⟩ x01

echo ta rroot⟨21⟩ x02

echo (sym ta) rroot⟨12⟩ x02
