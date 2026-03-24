⊤ : Set
⊤ = data [ star ]

test : (m : ⊤) → match m [ star ↦ sig () ]
test m = ?
