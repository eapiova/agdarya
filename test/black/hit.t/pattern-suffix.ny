def S1 : Type ≔ data [
| base.
| loop.e. : refl S1 base. base.]

def badpat (x : S1) : Id S1 base. x ≔ match x [
| base. ↦ refl base.
| loop.e. ↦ loop.
]
