  $ cat >wrap.ny <<EOF
  > postulate A:Set
  > postulate a:A
  > record wrapA : Set where { field unwrap : A }
  > 
  > wa1 : wrapA
  > wa1 = (unwrap ≔ a)
  > 
  > wa2 : wrapA
  > wa2 = (_ ≔ a)
  > 
  > wa3 : wrapA
  > wa3 = (a,)
  > 
  > wa4 : wrapA
  > wa4 = (a)
  > EOF

  $ agdarya -v wrap.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate a assumed
  
   ￫ info[I0000]
   ￮ constant wrapA defined
  
   ￫ info[I0000]
   ￮ constant wa1 defined
  
   ￫ info[I0000]
   ￮ constant wa2 defined
  
   ￫ info[I0000]
   ￮ constant wa3 defined
  
   ￫ error[E0401]
   ￭ $TESTCASE_ROOT/wrap.ny
   1 | wa4 = (a)
     ^ term synthesized type
         A
       but is being checked against type
         wrapA
       unequal head constants:
         A
       does not equal
         wrapA
  
  [1]
