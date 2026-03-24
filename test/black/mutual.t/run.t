  $ agdarya -v even_odd_rec.ny
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant ⊤ defined
  
   ￫ info[I0000]
   ￮ constant ⊥ defined
  
   ￫ info[I0000]
   ￮ constant even_odd_type defined
  
   ￫ info[I0000]
   ￮ constant even_odd defined
  
  ⊤
    : Set
  
  ⊥
    : Set
  
   ￫ warning[W2305]
   ￮ can't write compiled file: $TESTCASE_ROOT/even_odd_rec.nyo
  

  $ agdarya -v even_odd_sig.ny
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant even_odd_type defined
  
   ￫ info[I0000]
   ￮ constant even_odd defined
  
   ￫ info[I0000]
   ￮ constant even defined
  
   ￫ info[I0000]
   ￮ constant odd defined
  
   ￫ info[I0000]
   ￮ constant sum defined
  
   ￫ info[I0000]
   ￮ constant even_or_odd_suc defined
  
   ￫ info[I0000]
   ￮ constant all_even_or_odd defined
  

  $ agdarya -v even_odd_rec_canonical.ny
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant even_odd_type defined
  
   ￫ info[I0000]
   ￮ constant even_odd defined
  
  even_odd even 8
    : Set
  
  even_odd odd 8
    : Set
  


  $ agdarya -v ctx_ty_sig.ny
   ￫ info[I0000]
   ￮ constant ctx_ty_type defined
  
   ￫ info[I0000]
   ￮ constant ctx_ty defined
  
   ￫ info[I0000]
   ￮ constant ctx_ty_tm_type defined
  
   ￫ info[I0000]
   ￮ constant ctx_ty_tm defined
  

  $ agdarya -v univ_sig.ny
   ￫ info[I0000]
   ￮ constant bool defined
  
   ￫ info[I0000]
   ￮ constant uu_el_type defined
  
   ￫ info[I0000]
   ￮ constant uu_el defined
  

  $ agdarya -v even_odd_and.ny
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constants defined mutually:
       even
       odd
  
   ￫ info[I0000]
   ￮ constant sum defined
  
   ￫ info[I0000]
   ￮ constant even_or_odd_suc defined
  
   ￫ info[I0000]
   ￮ constant all_even_or_odd defined
  
   ￫ warning[W2305]
   ￮ can't write compiled file: $TESTCASE_ROOT/even_odd_and.nyo
  

  $ agdarya -v ctx_el_and.ny
   ￫ info[I0000]
   ￮ constants defined mutually:
       ctx
       ty
  
   ￫ warning[W2305]
   ￮ can't write compiled file: $TESTCASE_ROOT/ctx_el_and.nyo
  
  $ agdarya -v ctx_el_and_tm.ny
   ￫ info[I0000]
   ￮ constants defined mutually:
       ctx
       ty
       tm
  
   ￫ warning[W2305]
   ￮ can't write compiled file: $TESTCASE_ROOT/ctx_el_and_tm.nyo
  

  $ agdarya -v univ_and.ny
   ￫ info[I0000]
   ￮ constant bool defined
  
   ￫ info[I0000]
   ￮ constants defined mutually:
       uu
       el
  
   ￫ warning[W2305]
   ￮ can't write compiled file: $TESTCASE_ROOT/univ_and.nyo
  
