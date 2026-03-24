

data bool : Set where { true : bool ; false : bool }

uu : Set

uu = data [ bool | pi (A : uu) (B : el A → uu) ]

el : uu → Set

el = λ { bool → bool; pi A B → (x : el A) → el (B x) }
