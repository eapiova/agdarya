Synthesizing definitions

  $ agdarya -v -e 'postulate A : Set' -e 'postulate f : A -> A' -e 'postulate a : A' -e 'fa = f a'
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate f assumed
  
   ￫ info[I0001]
   ￮ postulate a assumed
  
   ￫ info[I0000]
   ￮ constant fa defined
  

Matches can also synthesize

  $ agdarya -v -e 'data bot : Set where { }' -e 'postulate P : bot → Set' -e 'foo : (e : bot) → P e' -e 'foo e = match e return x ↦ P x [ ]'
   ￫ info[I0000]
   ￮ constant bot defined
  
   ￫ info[I0001]
   ￮ postulate P assumed
  
   ￫ info[I0000]
   ￮ constant foo defined
  
