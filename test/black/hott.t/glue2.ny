

postulate A₀ : Set

postulate A₁ : Set

postulate A₂ : Id Set A₀ A₁

postulate B₀ : Set

postulate B₁ : Set

postulate B₂ : Id Set B₀ B₁

postulate R₀ : A₀ → B₀ → Set

postulate Rb₀ : isBisim A₀ B₀ R₀

postulate R₁ : A₁ → B₁ → Set

postulate Rb₁ : isBisim A₁ B₁ R₁

postulate R₂ : ((x : A₂) (y : B₂) ⇒ Id Set) R₀ R₁

postulate Rb₂ : refl isBisim A₂ B₂ R₂ Rb₀ Rb₁

postulate a₀ : A₀

postulate a₁ : A₁

postulate a₂ : A₂ a₀ a₁

postulate b₀ : B₀

postulate b₁ : B₁

postulate b₂ : B₂ b₀ b₁

postulate r₀ : R₀ a₀ b₀

postulate r₁ : R₁ a₁ b₁

postulate r₂ : R₂ a₂ b₂ r₀ r₁

G₀ : Id Set A₀ B₀

G₀ = glue A₀ B₀ R₀ Rb₀

G₁ : Id Set A₁ B₁

G₁ = glue A₁ B₁ R₁ Rb₁

G₂ : Id (Id Set) A₂ B₂ G₀ G₁

G₂ = refl glue A₂ B₂ R₂ Rb₂

g₀ : G₀ a₀ b₀

g₀ = (r₀,)

g₁ : G₁ a₁ b₁

g₁ = (r₁,)

g₂ : G₂ a₂ b₂ g₀ g₁

g₂ = (r₂,)

echo G₂ trr⟨1⟩

trr1 : Id (B₂ (Rb₀ trr a₀) (Rb₁ trr a₁)) (G₂ trr⟨1⟩ a₂) (Rb₂ trr a₂)

trr1 = refl _

echo G₂ trl⟨1⟩

trl1 : Id (A₂ (Rb₀ trl b₀) (Rb₁ trl b₁)) (G₂ trl⟨1⟩ b₂) (Rb₂ trl b₂)

trl1 = refl _

echo G₂ liftr⟨1⟩

liftr1 : Id
           (glue⁽ᵉ⁾ A₂ B₂ R₂ Rb₂ a₂ (Rb₂ trr a₂) (_ ≔ Rb₀ liftr a₀)
              (_ ≔ Rb₁ liftr a₁)) (G₂ liftr⟨1⟩ a₂) (_ ≔ Rb₂ liftr a₂)

liftr1 = refl _

echo G₂ liftl⟨1⟩

liftl1 : Id
           (glue⁽ᵉ⁾ A₂ B₂ R₂ Rb₂ (Rb₂ trl b₂) b₂ (_ ≔ Rb₀ liftl b₀)
              (_ ≔ Rb₁ liftl b₁)) (G₂ liftl⟨1⟩ b₂) (_ ≔ Rb₂ liftl b₂)

liftl1 = refl _

echo G₂ trr⟨2⟩

trr2 : Id (G₁ (A₂ trr a₀) (B₂ trr b₀)) (G₂ trr⟨2⟩ g₀)
         (_ ≔ R₂ (A₂ liftr a₀) (B₂ liftr b₀) trr r₀)

trr2 = refl _

echo G₂ trl⟨2⟩

trl2 : Id (G₀ (A₂ trl a₁) (B₂ trl b₁)) (G₂ trl⟨2⟩ g₁)
         (_ ≔ R₂ (A₂ liftl a₁) (B₂ liftl b₁) trl r₁)

trl2 = refl _

echo G₂ liftr⟨2⟩

liftr2 : Id
           (sym (glue⁽ᵉ⁾ A₂ B₂ R₂ Rb₂) g₀ {A₂ trr a₀} {B₂ trr b₀}
              (_ ≔ R₂ (A₂ liftr a₀) (B₂ liftr b₀) trr r₀) (A₂ liftr a₀)
              (B₂ liftr b₀)) (G₂ liftr⟨2⟩ g₀)
           (sym (_ ≔ R₂ (A₂ liftr a₀) (B₂ liftr b₀) liftr r₀))

liftr2 = refl _

echo G₂ liftl⟨2⟩

liftl2 : Id
           (sym (glue⁽ᵉ⁾ A₂ B₂ R₂ Rb₂) {A₂ trl a₁} {B₂ trl b₁}
              (_ ≔ R₂ (A₂ liftl a₁) (B₂ liftl b₁) trl r₁) g₁ (A₂ liftl a₁)
              (B₂ liftl b₁)) (G₂ liftl⟨2⟩ g₁)
           (sym (_ ≔ R₂ (A₂ liftl a₁) (B₂ liftl b₁) liftl r₁))

liftl2 = refl _

echo G₂ a₂ b₂ trr

abtrr : Id (G₁ a₁ b₁) (G₂ a₂ b₂ trr g₀) (_ ≔ R₂ a₂ b₂ trr r₀)

abtrr = refl _

echo G₂ a₂ b₂ trl

abtrl : Id (G₀ a₀ b₀) (G₂ a₂ b₂ trl g₁) (_ ≔ R₂ a₂ b₂ trl r₁)

abtrl = refl _

echo G₂ a₂ b₂ liftr

abliftr : Id (G₂ a₂ b₂ g₀ (_ ≔ R₂ a₂ b₂ trr r₀)) (G₂ a₂ b₂ liftr g₀)
            ((_ ≔ R₂ a₂ b₂ liftr r₀))

abliftr = refl _

echo G₂ a₂ b₂ liftl

abliftl : Id (G₂ a₂ b₂ (_ ≔ R₂ a₂ b₂ trl r₁) g₁) (G₂ a₂ b₂ liftl g₁)
            ((_ ≔ R₂ a₂ b₂ liftl r₁))

abliftl = refl _

echo sym G₂ g₀ g₁ trr

ggtrr : Id (B₂ b₀ b₁) (sym G₂ g₀ g₁ trr a₂)
          (Rb₂ id a₀ b₀ r₀ a₁ b₁ r₁ trr a₂)

ggtrr = refl _

echo sym G₂ g₀ g₁ trl

ggtrl : Id (A₂ a₀ a₁) (sym G₂ g₀ g₁ trl b₂)
          (Rb₂ id a₀ b₀ r₀ a₁ b₁ r₁ trl b₂)

ggtrl = refl _

echo sym G₂ g₀ g₁ liftr

ggliftr : Id
            (sym (glue⁽ᵉ⁾ A₂ B₂ R₂ Rb₂) g₀ g₁ a₂
               (Rb₂ id a₀ b₀ r₀ a₁ b₁ r₁ trr a₂)) (sym G₂ g₀ g₁ liftr a₂)
            (sym (_ ≔ Rb₂ id a₀ b₀ r₀ a₁ b₁ r₁ liftr a₂))

ggliftr = refl _

echo sym G₂ g₀ g₁ liftl

ggliftl : Id
            (sym (glue⁽ᵉ⁾ A₂ B₂ R₂ Rb₂) g₀ g₁
               (Rb₂ id a₀ b₀ r₀ a₁ b₁ r₁ trl b₂) b₂)
            (sym G₂ g₀ g₁ liftl b₂)
            (sym (_ ≔ Rb₂ id a₀ b₀ r₀ a₁ b₁ r₁ liftl b₂))

ggliftl = refl _
