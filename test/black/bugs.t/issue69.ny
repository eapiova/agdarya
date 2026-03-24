postulate A : Set
postulate B : A → Set
postulate C : A → Set

D : Set
D = data [ con (a : A) (f : B a → C a) ]

get_a : (d : D) → A
get_a d = match d [ con a f ↦ a ]

get_f : (d : D) → (b : B (get_a d)) → C (get_a d)
get_f d b = match d [
| con a f ↦ f b]
