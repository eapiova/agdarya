postulate A : Set

{- There are two ways of defining a double square root: directly with a 2-dimensional field, or by iterating ordinary square roots.  Here we prove that those are equivalent. -}

√A : Set
√A = codata [ r⟨e⟩ x : A ]

√√A : Set
√√A = codata [ rr⟨ee⟩ x : A ]

√_√A : Set
√_√A = codata [ r_r⟨e⟩ x : √A ]

f : (x : √√A) → √_√A
f x = record { r_r⟨e⟩ = record { r⟨e⟩ = x⟨22⟩ rr⟨12⟩ } }

g : (x : √_√A) → √√A
g x = record { rr⟨ee⟩ = x⟨22⟩ r_r⟨1⟩ r⟨1⟩ }

{- This depends on the characterization of the identity types of higher coinductive types as other higher coinductive types. -}

fg : (x : √_√A) → Id √_√A (f (g x)) x
fg x = record {
  r_r⟨1⟩ = refl x r_r⟨1⟩;
  r_r⟨e⟩ = record {
    r⟨1⟩ = refl x⟨2⟩ r_r⟨1⟩ r⟨1⟩;
    r⟨e⟩ = refl (x.22 r_r⟨1⟩ r⟨1⟩) } }

gf : (x : √√A) → Id √√A (g (f x)) x
gf x = record {
  rr⟨1e⟩ = refl x⟨2⟩ rr⟨12⟩;
  rr⟨e1⟩ = refl x⟨2⟩ rr⟨21⟩;
  rr⟨ee⟩ = refl (x.22 rr⟨12⟩) }
