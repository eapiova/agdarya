Transparency and translucency

  $ agdarya - <<EOF
  > postulate A : Set
  > postulate a : A
  > postulate B : Set
  > postulate b : B
  > prod1 : Set
  > prod1 = sig ( fst : A, snd : B)
  > postulate x1 : prod1
  > echo x1
  > y1 : prod1
  > y1 = (a,b)
  > echo y1
  > prod2a : Set
  > prod2a = sig #(transparent) ( fst : A, snd : B)
  > postulate x2a : prod2a
  > echo x2a
  > y2a : prod2a
  > y2a = (a,b)
  > echo y2a
  > prod2b : Set
  > prod2b = sig #(transparent positional) ( fst : A, snd : B)
  > postulate x2b : prod2b
  > echo x2b
  > y2b : prod2b
  > y2b = (a,b)
  > echo y2b
  > prod3a : Set
  > prod3a = sig #(translucent) ( fst : A, snd : B)
  > postulate x3a : prod3a
  > echo x3a
  > y3a : prod3a
  > y3a = (a,b)
  > echo y3a
  > prod3b : Set
  > prod3b = sig #(translucent positional) ( fst : A, snd : B)
  > postulate x3b : prod3b
  > echo x3b
  > y3b : prod3b
  > y3b = (a,b)
  > echo y3b
  > EOF
  x1
    : prod1
  
  y1
    : prod1
  
  (fst ≔ x2a fst, snd ≔ x2a snd)
    : prod2a
  
  (fst ≔ a, snd ≔ b)
    : prod2a
  
  (x2b fst, x2b snd)
    : prod2b
  
  (a, b)
    : prod2b
  
  x3a
    : prod3a
  
  (fst ≔ a, snd ≔ b)
    : prod3a
  
  x3b
    : prod3b
  
  (a, b)
    : prod3b
  
