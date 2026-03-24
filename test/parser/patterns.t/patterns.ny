

Sum : (A B : Set) → Set

Sum A B = data [ left (_ : A) | right (_ : B) ]

notation(0) "$" x ≔ left x

notation(0) y "@" ≔ right y

swap : (A : Set) → (x : Sum A A) → Sum A A

swap A x = case x of λ { $ x → x @; y @ → $ y}

Triple : (A : Set) → Set

Triple A = data [ foo (_ : A) (_ : A) (_ : A) ]

notation(0) x "+" y "+" z ≔ foo x y z

flop : (A : Set) → (x : Triple A) → Triple A

flop A x = case x of λ { a + b + c → c + a + b}

postulate A : Set

postulate a : A

postulate b : A

postulate c : A

echo flop A (a + c + b)

assoc : (A B C : Set) → (x : Sum (Sum A B) C) → Sum A (Sum B C)

assoc A B C x
=
  case x of λ { $ ($ a) → $ a; $ (b @) → ($ b) @; c @ → (c @) @}
