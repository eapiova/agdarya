import "univalence"

𝔹 : Set
𝔹 = data [ t | f ]

flip : 𝔹 → 𝔹
flip = λ { t → f; f → t }

flips : (x y : 𝔹) → Set
flips x y = match x, y [
| t, f ↦ sig #(transparent) ()
| t, t ↦ data []
| f, f ↦ data []
| f, t ↦ sig #(transparent) ()]

flips_tb : (b : 𝔹) → (f : flips t b) → refl Σ 𝔹⁽ᵉ⁾ {b ↦ flips t b} {b ↦ flips t b}
      (b ⤇ Id flips {t} {t} t b⟨2⟩) (b, f) (𝔹.f, ())
flips_tb b f = match b [ t ↦ match f [ ] | f ↦ (𝔹.f, ()) ]

flips_fb : (b : 𝔹) → (f : flips f b) → refl Σ 𝔹⁽ᵉ⁾ {b ↦ flips 𝔹.f b} {b ↦ flips 𝔹.f b}
      (b ⤇ Id flips {𝔹.f} {𝔹.f} 𝔹.f b⟨2⟩) (b, f) (t, ())
flips_fb b f = match b [ f ↦ match f [ ] | t ↦ (t, ()) ]

flips_bt : (b : 𝔹) → (f : flips b t) → refl Σ 𝔹⁽ᵉ⁾ {b ↦ flips b t} {b ↦ flips b t}
      (b ⤇ Id flips b⟨2⟩ {t} {t} t) (b, f) (𝔹.f, ())
flips_bt b f = match b [ t ↦ match f [ ] | f ↦ (𝔹.f, ()) ]

flips_bf : (b : 𝔹) → (f : flips b f) → refl Σ 𝔹⁽ᵉ⁾ {b ↦ flips b 𝔹.f} {b ↦ flips b 𝔹.f}
      (b ⤇ Id flips b⟨2⟩ {𝔹.f} {𝔹.f} 𝔹.f) (b, f) (t, ())
flips_bf b f = match b [ f ↦ match f [ ] | t ↦ (t, ()) ]

flips11 : is11 𝔹 𝔹 flips
flips11 = (
  contrr ≔ λ {
  t → ((f, ()), a ↦ flips_tb (a fst) (a snd));
  f → ((t, ()), a ↦ flips_fb (a fst) (a snd))},
  contrl ≔ λ {
  t → ((f, ()), a ↦ flips_bt (a fst) (a snd));
  f → ((t, ()), a ↦ flips_bf (a fst) (a snd))})

𝔽 : Id Set 𝔹 𝔹
𝔽 = glue 𝔹 𝔹 flips (bisim_of_11 𝔹 𝔹 flips flips11)

echo 𝔽 trr t

𝔽t : Id 𝔹 (𝔽 trr t) f
𝔽t = refl _

echo 𝔽 trl f

𝔽f : Id 𝔹 (𝔽 trr f) t
𝔽f = refl _

echo 𝔽 liftr t

𝔽lt : Id (𝔽 t f) (𝔽 liftr t) ((),)
𝔽lt = refl _

echo 𝔽 liftr f

𝔽lf : Id (𝔽 f t) (𝔽 liftr f) ((),)
𝔽lf = refl _
