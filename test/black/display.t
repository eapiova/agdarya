  $ cat - >display.ny <<EOF
  > echo Set -> Set
  > display chars ≔ ascii
  > echo Set -> Set
  > display chars ≔ unicode
  > echo Set -> Set
  > EOF

  $ agdarya -fake-interact=display.ny
  Set → Set
    : Set
  
   ￫ info[I0101]
   ￮ display set chars to ASCII
  
  Set -> Set
    : Set
  
   ￫ info[I0101]
   ￮ display set chars to unicode
  
  Set → Set
    : Set
  
