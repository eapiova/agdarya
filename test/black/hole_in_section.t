  $ agdarya -fake-interact $'section foo ≔\npostulate A : Set\nB : A\nB = ?\nC : A\nC = ?\nend\nshow hole 0\nshow hole 1'
   ￫ info[I0007]
   ￮ section foo opened
  
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0000]
   ￮ constant B defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     ----------------------------------------------------------------------
     A
  
   ￫ info[I0000]
   ￮ constant C defined, containing 1 hole
  
   ￫ info[I3003]
   ￮ hole ?1:
     
     ----------------------------------------------------------------------
     A
  
   ￫ info[I0008]
   ￮ section foo closed
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     ----------------------------------------------------------------------
     A
  
   ￫ info[I3003]
   ￮ hole ?1:
     
     ----------------------------------------------------------------------
     A
  
