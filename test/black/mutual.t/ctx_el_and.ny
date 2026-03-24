 {- A version of ctx_el_sig that uses mutual definition syntax. -}

ctx : Set

ctx = data [ empty | ext (Γ : ctx) (A : ty Γ) ]

ty : (Γ : ctx) → Set

ty Γ = data [ base | pi (A : ty Γ) (B : ty (ext Γ A)) ]
