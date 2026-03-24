postulate X : Set
postulate x0 : X
postulate x1 : X
postulate x2 : Id X x0 x1

{-Identity types are equivalently instantiations of refl of a type -}
equiv_id : Id Set (Id X x0 x1) (refl X x0 x1)
equiv_id = refl (Id X x0 x1)

{-We also have a standard degeneracy notation-}
equiv_id' : Id Set (Id X x0 x1) (X⁽ᵉ⁾ x0 x1)
equiv_id' = refl (Id X x0 x1)

{-The identity function acts as the identity-}
id_map_act : Id X (((x ↦ x) : X → X) x0) x0
id_map_act = refl x0

{-refl of the identity function acts as the identity on identifications-}
refl_id_map_act : Id (Id X x0 x1) (refl ((x ↦ x) : (X → X)) x2) x2
refl_id_map_act = refl x2

{--}
postulate Y : Set
postulate Z : Set
postulate f : X → Y
postulate g : Y → Z
gof : X → Z
gof x = g (f x)

{-Identity types of pi-types don't *compute* to the expected thing, but they are isomorphic, by eta-expansion in both directions.-}
postulate f' : X → Y
idff : Set
idff = Id (X → Y) f f'
idff' : Set
idff' = (x : X) (x' : X) (x'' : Id X x x') → Id Y (f x) (f' x')

idff_to_idff' : idff → idff'
idff_to_idff' h x x' x'' = h x''
idff'_to_idff : idff' → idff
idff'_to_idff k {x} {x'} x'' = k x x' x''

idff_roundtrip : (p : idff) → Id idff (idff'_to_idff (idff_to_idff' p)) p
idff_roundtrip p = refl p

idff'_roundtrip : (q : idff') → Id idff' (idff_to_idff' (idff'_to_idff q)) q
idff'_roundtrip q = refl q

{-Identity types are invariant under eta-expansion-}
idff_eta : Set
idff_eta = Id (X → Y) (x ↦ f x) (f')
id_inv_under_eta : Id Set idff idff_eta
id_inv_under_eta = refl idff

{-Ap is functorial-}
ap_is_functorial : Id (Id Z (g (f x0)) (g (f x1))) (refl g (refl f x2))
      (refl ((x ↦ g (f x)) : X → Z) x2)
ap_is_functorial = refl (refl ((x ↦ g (f x)) : X → Z) x2)

{-The two degenerate squares associated to an identification have unequal types, although each has a standard degeneracy notation.-}
r1x2 = refl x2
r1x2' = x2⁽¹ᵉ⁾
r1x2_eq_r1x2' : Id (X⁽ᵉᵉ⁾ (refl x0) (refl x1) x2 x2) r1x2 r1x2'
r1x2_eq_r1x2' = refl r1x2

r2x2 = (refl ((x ↦ refl x) : (x : X) → Id X x x) x2)
r2x2' = x2⁽ᵉ¹⁾
r2x2_eq_r2x2' : Id (X⁽ᵉᵉ⁾ x2 x2 (refl x0) (refl x1)) r2x2 r2x2'
r2x2_eq_r2x2' = refl r2x2

{-But applying symmetry identifies both their types and values.-}
sr1x2_eq_r2x2 : Id (X⁽ᵉᵉ⁾ x2 x2 (refl x0) (refl x1)) (sym r1x2) r2x2
sr1x2_eq_r2x2 = refl r2x2

sr1x2'_eq_r2x2' : Id (X⁽ᵉᵉ⁾ x2 x2 (refl x0) (refl x1)) (x2⁽ᵉ⁾⁽²¹⁾) r2x2'
sr1x2'_eq_r2x2' = refl r2x2'

{-But the two degenerate squares associated to a reflexivity *are* equal.-}
r1reflx0 = refl (refl x0)
r2reflx0 = refl ((x ↦ refl x) : (x : X) → Id X x x) (refl x0)
r1reflx0_eq_r2reflx0 : Id (X⁽ᵉᵉ⁾ (refl x0) (refl x0) (refl x0) (refl x0)) r1reflx0 r2reflx0
r1reflx0_eq_r2reflx0 = refl r1reflx0

r1reflx0' = x0⁽ᵉᵉ⁾
r1reflx0_eq_r1reflx0' : Id (X⁽ᵉᵉ⁾ (refl x0) (refl x0) (refl x0) (refl x0)) r1reflx0 r1reflx0'
r1reflx0_eq_r1reflx0' = refl r1reflx0

{-Doubly-degenerate squares are also fixed by symmetry-}
sr1reflx0 = sym (refl (refl x0))
r1reflx0_eq_sr1reflx0 : Id (X⁽ᵉᵉ⁾ (refl x0) (refl x0) (refl x0) (refl x0)) r1reflx0 sr1reflx0
r1reflx0_eq_sr1reflx0 = refl r1reflx0
