{- Transport and lifting compute on Π-types -}

Π : (A : Set) → (B : A → Set) → Set
Π A B = (x : A) → B x

postulate A₀ : Set

postulate A₁ : Set

postulate A₂ : Id Set A₀ A₁

postulate a₀ : A₀

postulate a₁ : A₁

postulate B₀ : A₀ → Set

postulate B₁ : A₁ → Set

postulate B₂ : Id ((X ↦ X → Set) : Set → Set) A₂ B₀ B₁

postulate f₀ : (x₀ : A₀) → B₀ x₀

postulate f₁ : (x₁ : A₁) → B₁ x₁

echo refl Π A₂ B₂ trr f₀ a₁

synth B₂ (A₂ liftl⟨1⟩ a₁) trr⟨1⟩ (f₀ (A₂ trl⟨1⟩ a₁))

Πtrr : Id (B₁ a₁) (refl Π A₂ B₂ trr f₀ a₁)
      (B₂ {A₂ trl⟨1⟩ a₁} {a₁} (A₂ liftl⟨1⟩ a₁) trr⟨1⟩ (f₀ (A₂ trl⟨1⟩ a₁)))
Πtrr = refl _

echo refl Π A₂ B₂ trl f₁ a₀

synth B₂ (A₂ liftr⟨1⟩ a₀) trl⟨1⟩ (f₁ (A₂ trr⟨1⟩ a₀))

Πtrl : Id (B₀ a₀) (refl Π A₂ B₂ trl f₁ a₀)
      (B₂ {a₀} {A₂ trr⟨1⟩ a₀} (A₂ liftr⟨1⟩ a₀) trl⟨1⟩ (f₁ (A₂ trr⟨1⟩ a₀)))
Πtrl = refl _

postulate a₂ : A₂ a₀ a₁

echo refl Π A₂ B₂ liftr f₀ a₂

synth B₂⁽¹ᵉ⁾ {a₀} {A₂ trl⟨1⟩ a₁}
          {A₂⁽ᵉ¹⁾ {a₀} {a₁} a₂ {A₂ trl⟨1⟩ a₁} {a₁} (A₂ liftl⟨1⟩ a₁)
          trl⟨1⟩ (refl a₁)} {a₁} {a₁} {refl a₁} {a₂} {A₂ liftl⟨1⟩ a₁}
          (sym
             (A₂⁽ᵉ¹⁾ {a₀} {a₁} a₂ {A₂ trl⟨1⟩ a₁} {a₁} (A₂ liftl⟨1⟩ a₁)
              liftl⟨1⟩ (refl a₁))) {f₀ a₀} {f₀ (A₂ trl⟨1⟩ a₁)}
          (refl f₀ {a₀} {A₂ trl⟨1⟩ a₁}
             (A₂⁽ᵉ¹⁾ {a₀} {a₁} a₂ {A₂ trl⟨1⟩ a₁} {a₁} (A₂ liftl⟨1⟩ a₁)
              trl⟨1⟩ (refl a₁)))
          {B₂ {A₂ trl⟨1⟩ a₁} {a₁} (A₂ liftl⟨1⟩ a₁)
          trr⟨1⟩ (f₀ (A₂ trl⟨1⟩ a₁))}
          {B₂ {A₂ trl⟨1⟩ a₁} {a₁} (A₂ liftl⟨1⟩ a₁)
          trr⟨1⟩ (f₀ (A₂ trl⟨1⟩ a₁))}
          (B₂⁽¹ᵉ⁾ {A₂ trl⟨1⟩ a₁} {A₂ trl⟨1⟩ a₁}
               {A₂⁽¹ᵉ⁾ trl⟨1⟩ {a₁} {a₁} (refl a₁)} {a₁} {a₁} {refl a₁}
               {A₂ liftl⟨1⟩ a₁} {A₂ liftl⟨1⟩ a₁}
               (A₂⁽¹ᵉ⁾ liftl⟨1⟩ {a₁} {a₁} (refl a₁))
           trr⟨1⟩ {f₀ (A₂ trl⟨1⟩ a₁)} {f₀ (A₂ trl⟨1⟩ a₁)}
             (refl f₀ {A₂ trl⟨1⟩ a₁} {A₂ trl⟨1⟩ a₁}
                (A₂⁽¹ᵉ⁾ trl⟨1⟩ {a₁} {a₁} (refl a₁))))
  trl⟨1⟩
    (B₂ {A₂ trl⟨1⟩ a₁} {a₁} (A₂ liftl⟨1⟩ a₁) liftr⟨1⟩ (f₀ (A₂ trl⟨1⟩ a₁)))

Πliftr : Id
      (B₂ {a₀} {a₁} a₂ (f₀ a₀)
         (B₂ {A₂ trl⟨1⟩ a₁} {a₁} (A₂ liftl⟨1⟩ a₁)
          trr⟨1⟩ (f₀ (A₂ trl⟨1⟩ a₁)))) (refl Π A₂ B₂ liftr f₀ a₂)
      (B₂⁽¹ᵉ⁾ {a₀} {A₂ trl⟨1⟩ a₁}
           {A₂⁽ᵉ¹⁾ {a₀} {a₁} a₂ {A₂ trl⟨1⟩ a₁} {a₁} (A₂ liftl⟨1⟩ a₁)
           trl⟨1⟩ (refl a₁)} {a₁} {a₁} {refl a₁} {a₂} {A₂ liftl⟨1⟩ a₁}
           (sym
              (A₂⁽ᵉ¹⁾ {a₀} {a₁} a₂ {A₂ trl⟨1⟩ a₁} {a₁} (A₂ liftl⟨1⟩ a₁)
               liftl⟨1⟩ (refl a₁))) {f₀ a₀} {f₀ (A₂ trl⟨1⟩ a₁)}
           (refl f₀ {a₀} {A₂ trl⟨1⟩ a₁}
              (A₂⁽ᵉ¹⁾ {a₀} {a₁} a₂ {A₂ trl⟨1⟩ a₁} {a₁} (A₂ liftl⟨1⟩ a₁)
               trl⟨1⟩ (refl a₁)))
           {B₂ {A₂ trl⟨1⟩ a₁} {a₁} (A₂ liftl⟨1⟩ a₁)
           trr⟨1⟩ (f₀ (A₂ trl⟨1⟩ a₁))}
           {B₂ {A₂ trl⟨1⟩ a₁} {a₁} (A₂ liftl⟨1⟩ a₁)
           trr⟨1⟩ (f₀ (A₂ trl⟨1⟩ a₁))}
           (B₂⁽¹ᵉ⁾ {A₂ trl⟨1⟩ a₁} {A₂ trl⟨1⟩ a₁}
                {A₂⁽¹ᵉ⁾ trl⟨1⟩ {a₁} {a₁} (refl a₁)} {a₁} {a₁} {refl a₁}
                {A₂ liftl⟨1⟩ a₁} {A₂ liftl⟨1⟩ a₁}
                (A₂⁽¹ᵉ⁾ liftl⟨1⟩ {a₁} {a₁} (refl a₁))
            trr⟨1⟩ {f₀ (A₂ trl⟨1⟩ a₁)} {f₀ (A₂ trl⟨1⟩ a₁)}
              (refl f₀ {A₂ trl⟨1⟩ a₁} {A₂ trl⟨1⟩ a₁}
                 (A₂⁽¹ᵉ⁾ trl⟨1⟩ {a₁} {a₁} (refl a₁))))
       trl⟨1⟩
         (B₂ {A₂ trl⟨1⟩ a₁} {a₁} (A₂ liftl⟨1⟩ a₁)
          liftr⟨1⟩ (f₀ (A₂ trl⟨1⟩ a₁))))
Πliftr = refl _

echo refl Π A₂ B₂ liftl f₁ a₂

synth B₂⁽¹ᵉ⁾ {a₀} {a₀} {refl a₀} {a₁} {A₂ trr⟨1⟩ a₀}
          {A₂⁽ᵉ¹⁾ {a₀} {a₁} a₂ {a₀} {A₂ trr⟨1⟩ a₀} (A₂ liftr⟨1⟩ a₀)
          trr⟨1⟩ (refl a₀)} {a₂} {A₂ liftr⟨1⟩ a₀}
          (sym
             (A₂⁽ᵉ¹⁾ {a₀} {a₁} a₂ {a₀} {A₂ trr⟨1⟩ a₀} (A₂ liftr⟨1⟩ a₀)
              liftr⟨1⟩ (refl a₀)))
          {B₂ {a₀} {A₂ trr⟨1⟩ a₀} (A₂ liftr⟨1⟩ a₀)
          trl⟨1⟩ (f₁ (A₂ trr⟨1⟩ a₀))}
          {B₂ {a₀} {A₂ trr⟨1⟩ a₀} (A₂ liftr⟨1⟩ a₀)
          trl⟨1⟩ (f₁ (A₂ trr⟨1⟩ a₀))}
          (B₂⁽¹ᵉ⁾ {a₀} {a₀} {refl a₀} {A₂ trr⟨1⟩ a₀} {A₂ trr⟨1⟩ a₀}
               {A₂⁽¹ᵉ⁾ trr⟨1⟩ {a₀} {a₀} (refl a₀)} {A₂ liftr⟨1⟩ a₀}
               {A₂ liftr⟨1⟩ a₀} (A₂⁽¹ᵉ⁾ liftr⟨1⟩ {a₀} {a₀} (refl a₀))
           trl⟨1⟩ {f₁ (A₂ trr⟨1⟩ a₀)} {f₁ (A₂ trr⟨1⟩ a₀)}
             (refl f₁ {A₂ trr⟨1⟩ a₀} {A₂ trr⟨1⟩ a₀}
                (A₂⁽¹ᵉ⁾ trr⟨1⟩ {a₀} {a₀} (refl a₀)))) {f₁ a₁}
          {f₁ (A₂ trr⟨1⟩ a₀)}
          (refl f₁ {a₁} {A₂ trr⟨1⟩ a₀}
             (A₂⁽ᵉ¹⁾ {a₀} {a₁} a₂ {a₀} {A₂ trr⟨1⟩ a₀} (A₂ liftr⟨1⟩ a₀)
              trr⟨1⟩ (refl a₀)))
  trl⟨1⟩
    (B₂ {a₀} {A₂ trr⟨1⟩ a₀} (A₂ liftr⟨1⟩ a₀) liftl⟨1⟩ (f₁ (A₂ trr⟨1⟩ a₀)))

Πliftl : Id
      (B₂ {a₀} {a₁} a₂
         (B₂ {a₀} {A₂ trr⟨1⟩ a₀} (A₂ liftr⟨1⟩ a₀)
          trl⟨1⟩ (f₁ (A₂ trr⟨1⟩ a₀))) (f₁ a₁)) (refl Π A₂ B₂ liftl f₁ a₂)
      (B₂⁽¹ᵉ⁾ {a₀} {a₀} {refl a₀} {a₁} {A₂ trr⟨1⟩ a₀}
           {A₂⁽ᵉ¹⁾ {a₀} {a₁} a₂ {a₀} {A₂ trr⟨1⟩ a₀} (A₂ liftr⟨1⟩ a₀)
           trr⟨1⟩ (refl a₀)} {a₂} {A₂ liftr⟨1⟩ a₀}
           (sym
              (A₂⁽ᵉ¹⁾ {a₀} {a₁} a₂ {a₀} {A₂ trr⟨1⟩ a₀} (A₂ liftr⟨1⟩ a₀)
               liftr⟨1⟩ (refl a₀)))
           {B₂ {a₀} {A₂ trr⟨1⟩ a₀} (A₂ liftr⟨1⟩ a₀)
           trl⟨1⟩ (f₁ (A₂ trr⟨1⟩ a₀))}
           {B₂ {a₀} {A₂ trr⟨1⟩ a₀} (A₂ liftr⟨1⟩ a₀)
           trl⟨1⟩ (f₁ (A₂ trr⟨1⟩ a₀))}
           (B₂⁽¹ᵉ⁾ {a₀} {a₀} {refl a₀} {A₂ trr⟨1⟩ a₀} {A₂ trr⟨1⟩ a₀}
                {A₂⁽¹ᵉ⁾ trr⟨1⟩ {a₀} {a₀} (refl a₀)} {A₂ liftr⟨1⟩ a₀}
                {A₂ liftr⟨1⟩ a₀} (A₂⁽¹ᵉ⁾ liftr⟨1⟩ {a₀} {a₀} (refl a₀))
            trl⟨1⟩ {f₁ (A₂ trr⟨1⟩ a₀)} {f₁ (A₂ trr⟨1⟩ a₀)}
              (refl f₁ {A₂ trr⟨1⟩ a₀} {A₂ trr⟨1⟩ a₀}
                 (A₂⁽¹ᵉ⁾ trr⟨1⟩ {a₀} {a₀} (refl a₀)))) {f₁ a₁}
           {f₁ (A₂ trr⟨1⟩ a₀)}
           (refl f₁ {a₁} {A₂ trr⟨1⟩ a₀}
              (A₂⁽ᵉ¹⁾ {a₀} {a₁} a₂ {a₀} {A₂ trr⟨1⟩ a₀} (A₂ liftr⟨1⟩ a₀)
               trr⟨1⟩ (refl a₀)))
       trl⟨1⟩
         (B₂ {a₀} {A₂ trr⟨1⟩ a₀} (A₂ liftr⟨1⟩ a₀)
          liftl⟨1⟩ (f₁ (A₂ trr⟨1⟩ a₀))))
Πliftl = refl _
