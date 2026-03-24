{- Degeneracy notations -}

{- Simple refl -}

postulate A : Set

postulate a : A

echo refl a

{- refl of types is Id -}

postulate a0 : A

postulate a1 : A

echo Id A a0 a1

{- refl of functions is ap -}

postulate C : Set

postulate f : A → C

echo refl f

{- refl of type families is also Id -}

postulate B : A → Set

echo Id B

postulate a2 : A

{- refl of canonical types is ⁽ᵉ⁾ -}

Unit : Set
Unit = sig ()

postulate u0 : Unit

postulate u1 : Unit

echo Id Unit u0 u1
