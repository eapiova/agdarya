{- -*- agdarya-prog-args: ("-proofgeneral" "-parametric") -*- -}

Gel : (A B : Set) → (R : A → B → Set) → Id Set A B
Gel A B R = sig a b ↦ ( ungel : R a b )

{- First we define an equality type -}
eq : (X:Set) → (x:X) → X → Set
eq X x = data [ rfl : eq X x x ]

{- Now we prove a first application of parametricity: anything in the type of the polymorphic identity function is pointwise equal to the identity.  (This doesn't actually require the computation laws for gel/ungel, and it only uses unary parametricity.) -}
postulate f : (X:Set) → X → X

f_is_id : (X:Set) → (x:X) → eq X x (f X x)
f_is_id X x = refl f (Gel X X (a b ↦ eq X x b)) {x} {x} (_ ≔ rfl) ungel
