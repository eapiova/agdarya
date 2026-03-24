S1 : Set
S1 = data [
| base
| .loop.e. : refl S1 base base]

badpat : (x : S1) → Id S1 base x
badpat x = match x [
| base ↦ refl base
| .loop.e. ↦ loop
]
