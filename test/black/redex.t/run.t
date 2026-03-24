  $ agdarya redex.ny
  (λ x → f x) a
    : B a
  
  f a
    : B a
  
  (λ x → ()) a
    : unit
  
  ()
    : unit
  
  ap (λ x → f x) a₂
    : Id B a₂ (f a₀) (f a₁)
  
  refl f a₂
    : Id B a₂ (f a₀) (f a₁)
  
  ap (λ x → ()) a₂
    : unit⁽ᵉ⁾ () ()
  
  ()
    : unit⁽ᵉ⁾ () ()
  
  (λ x → f x)⁽ᵉᵉ⁾ a22
    : B⁽ᵉᵉ⁾ a22 (refl f a02) (refl f a12) (refl f a20) (refl f a21)
  
  f⁽ᵉᵉ⁾ a22
    : B⁽ᵉᵉ⁾ a22 (refl f a02) (refl f a12) (refl f a20) (refl f a21)
  
  (λ x → ())⁽ᵉᵉ⁾ a22
    : unit⁽ᵉᵉ⁾ {()} {()} () {()} {()} () () ()
  
  ()
    : unit⁽ᵉᵉ⁾ {()} {()} () {()} {()} () () ()
  
  (λ x y → g x y) a ()
    : B a
  
  g a ()
    : B a
  
  (λ x y → ()) a ()
    : unit
  
  ()
    : unit
  
  (λ y x → g x y) () a
    : B a
  
  g a ()
    : B a
  
  (λ y x → ()) () a
    : unit
  
  ()
    : unit
  
  ap (λ x y → g x y) a₂ {()} {()} ()
    : Id B a₂ (g a₀ ()) (g a₁ ())
  
  refl g a₂ {()} {()} ()
    : Id B a₂ (g a₀ ()) (g a₁ ())
  
  ap (λ y x → g x y) {()} {()} () a₂
    : Id B a₂ (g a₀ ()) (g a₁ ())
  
  refl g a₂ {()} {()} ()
    : Id B a₂ (g a₀ ()) (g a₁ ())
  
  ap (λ x y → ()) a₂ {()} {()} ()
    : unit⁽ᵉ⁾ () ()
  
  ()
    : unit⁽ᵉ⁾ () ()
  
  ap (λ y x → ()) {()} {()} () a₂
    : unit⁽ᵉ⁾ () ()
  
  ()
    : unit⁽ᵉ⁾ () ()
  
  (λ x y → h x y) a ()
    : B a
  
  h a ()
    : B a
  
  (λ x y → ()) a ()
    : unit
  
  ()
    : unit
  
  ap (λ x y → h x y) a₂ {()} {()} ()
    : Id B a₂ (h a₀ ()) (h a₁ ())
  
  refl h a₂ {()} {()} ()
    : Id B a₂ (h a₀ ()) (h a₁ ())
  
  ap (λ x y → ()) a₂ {()} {()} ()
    : unit⁽ᵉ⁾ () ()
  
  ()
    : unit⁽ᵉ⁾ () ()
  

