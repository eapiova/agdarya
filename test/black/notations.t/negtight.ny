postulate A : Set
f : A → A → A
f a b = b
postulate g : A → A → A
h : A → A → A
h a b = a
notation(0) x "+" y ≔ f x y
notation(1) x "*" y ≔ g x y
notation(-1) x "%" y ≔ h x y
postulate a : A
postulate b : A
postulate c : A
echo a + b * c
echo a * b + c
echo a % b + c
echo a + b % c
echo a * b % c
echo a % b * c
