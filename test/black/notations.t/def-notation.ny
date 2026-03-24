postulate A : Set
twos : Set
twos = data [
| foo (_ : A) (_ : A)
]
_+_ : A → A → twos
_+_ x y = foo x y
infixl 1 _+_
postulate a : A
synth a + a
