{- Transport and lifting have the right type -}

postulate A₀ : Set
postulate A₁ : Set
postulate A₂ : Id Set A₀ A₁

synth A₂ trr⟨1⟩
synth A₂ trl⟨1⟩
synth A₂ liftr⟨1⟩
synth A₂ liftl⟨1⟩

postulate a₀ : A₀
synth A₂ trr⟨1⟩ a₀
synth A₂ liftr⟨1⟩ a₀

postulate a₁ : A₁
synth A₂ trl⟨1⟩ a₁
synth A₂ liftl⟨1⟩ a₁
