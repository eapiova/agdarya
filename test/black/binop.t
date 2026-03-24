  $ cat >nat.ny <<EOF
  > data ℕ : Set where { zero : ℕ; suc : ℕ → ℕ }
  > O : ℕ
  > O = zero
  > S : ℕ → ℕ
  > S n = suc n
  > plus : ℕ → ℕ → ℕ
  > plus m n = match n [ | zero ↦ m | suc n ↦ suc (plus m n) ]
  > times : ℕ → ℕ → ℕ
  > times m n = match n [ | zero ↦ zero | suc n ↦ plus (times m n) m ]
  > notation(0) m "+" n … ≔ plus m n
  > notation(1) m "*" n … ≔ times m n
  > echo (S O) + (S (S O)) + (S (S (S O)))
  > echo S (S O) * S (S O) + S (S O)
  > echo S (S O) * (S (S O) + S (S O))
  > six : ℕ
  > six = 6
  > postulate m : ℕ
  > postulate n : ℕ
  > echo m+n
  > echo m+n*n
  > echo m*(m+n*n)
  > echo m + suc n
  > echo (m+n)*(m+n)
  > echo n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n + n
  > echo n + n * n + n * n * n + n * n * n * n + n + n * n * n * n * n * n * n + n * n + n * n * n + n * n * n * n + n + n * n * n * n * n * n * n
  > EOF

  $ agdarya -v nat.ny
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant O defined
  
   ￫ info[I0000]
   ￮ constant S defined
  
   ￫ info[I0000]
   ￮ constant plus defined
  
   ￫ info[I0000]
   ￮ constant times defined
  
   ￫ info[I0002]
   ￮ notation «_ + _» defined
  
   ￫ info[I0002]
   ￮ notation «_ * _» defined
  
  6
    : ℕ
  
  6
    : ℕ
  
  8
    : ℕ
  
   ￫ info[I0000]
   ￮ constant six defined
  
   ￫ info[I0001]
   ￮ postulate m assumed
  
   ￫ info[I0001]
   ￮ postulate n assumed
  
  m + n
    : ℕ
  
  m + n * n
    : ℕ
  
  m * (m + n * n)
    : ℕ
  
  suc (m + n)
    : ℕ
  
  (m + n) * (m + n)
    : ℕ
  
  n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
  + n
    : ℕ
  
  n
  + n * n
  + n * n * n
  + n * n * n * n
  + n
  + n * n * n * n * n * n * n
  + n * n
  + n * n * n
  + n * n * n * n
  + n
  + n * n * n * n * n * n * n
    : ℕ
  
