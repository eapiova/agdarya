postulate A : Set
twos : Set
twos = data [
| foo (_:A) (_:A)
]
notation(1) x "+" y := foo x y
threes : Set
threes = data [
| foo (_:A) (_:A) (_:A)
]
notation(1) x "*" y "*" z := foo x y z
postulate a:A
a2 : twos
a2 = a + a
echo a2
a3 : threes
a3 = a * a * a
echo a3
