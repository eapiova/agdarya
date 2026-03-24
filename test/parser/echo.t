  $ agdarya -e 'data Nat : Set where { zero : Nat; suc : Nat → Nat }' -e 'Stream : Set → Set' -e 'Stream A = codata [ head _ : A | tail _ : Stream A ]' -e '' -e 'f : Stream Nat' -e 'f = record { head = 0; tail = f }' -e 'echo f'
  f
    : Stream Nat
  
