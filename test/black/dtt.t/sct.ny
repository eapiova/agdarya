{- -*- agdarya-prog-args: ("-proofgeneral" "-parametric" "-arity" "2" "-direction" "p" "-external") -*- -}

-- (Binary) semi-cubical types
SCT : Set
SCT = codata [ z X : Set | s X : SCT⁽ᵖ⁾ X X ]

0s : (X : SCT) → Set
0s X = X z

1s : (X : SCT) → (x0 x1 : 0s X) → Set
1s X x0 x1 = X s z x0 x1

2s : (X : SCT) → (x00 x01 : 0s X) → (x02 : 1s X x00 x01) → (x10 x11 : 0s X) → (x12 : 1s X x10 x11) → (x20 : 1s X x00 x10) → (x21 : 1s X x01 x11) → Set
2s X x00 x01 x02 x10 x11 x12 x20 x21 = X s s z x02 x12 x20 x21
