  $ agdarya -fake-interact $'module foo where {\npostulate A : Set;\nB : A;\nB = ?;\nC : A;\nC = ?\n}\nshow hole 0\nshow hole 1'
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
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     ----------------------------------------------------------------------
     foo.A
  
   ￫ info[I3003]
   ￮ hole ?1:
     
     ----------------------------------------------------------------------
     foo.A
  
