  $ agdarya -v stream.ny
   ￫ info[I0000]
   ￮ constant Stream defined
  
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate s assumed
  
   ￫ info[I0000]
   ￮ constant s0 defined
  
   ￫ info[I0000]
   ￮ constant s0t defined
  
   ￫ info[I0000]
   ￮ constant s1 defined
  
   ￫ info[I0000]
   ￮ constant s2 defined
  
   ￫ info[I0000]
   ￮ constant s' defined
  
   ￫ info[I0000]
   ￮ constant s_is_s' defined
  
   ￫ info[I0000]
   ￮ constant corec defined
  
   ￫ info[I0000]
   ￮ constant s'' defined
  
   ￫ info[I0000]
   ￮ constant ∞eta defined
  
   ￫ info[I0000]
   ￮ constant ∞eta_bisim defined
  
   ￫ info[I0000]
   ￮ constant ℕ defined
  
   ￫ info[I0000]
   ￮ constant nats defined
  
   ￫ info[I0000]
   ￮ constant nats0_eq_0 defined
  
   ￫ info[I0000]
   ￮ constant nats1_eq_1 defined
  
   ￫ info[I0000]
   ￮ constant nats2_eq_2 defined
  
   ￫ info[I0000]
   ￮ constant nats3_eq_3 defined
  
   ￫ info[I0000]
   ￮ constant plus defined
  
   ￫ info[I0000]
   ￮ constant prod defined
  
   ￫ info[I0000]
   ￮ constant fib defined
  
   ￫ info[I0000]
   ￮ constant fib0_eq_1 defined
  
   ￫ info[I0000]
   ￮ constant fib1_eq_1 defined
  
   ￫ info[I0000]
   ￮ constant fib2_eq_2 defined
  
   ￫ info[I0000]
   ￮ constant fib3_eq_3 defined
  
   ￫ info[I0000]
   ￮ constant fib4_eq_5 defined
  
   ￫ info[I0000]
   ￮ constant fib5_eq_8 defined
  
   ￫ warning[W2305]
   ￮ can't write compiled file: $TESTCASE_ROOT/stream.nyo
  

  $ agdarya stream.ny -e "s_eq_s' : Id (Stream A) s s'" -e "s_eq_s' = refl s"
   ￫ warning[W2305]
   ￮ can't write compiled file: $TESTCASE_ROOT/stream.nyo
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | s_eq_s' = refl s
     ^ term synthesized type
         Stream⁽ᵉ⁾ (Id A) s s
       but is being checked against type
         Stream⁽ᵉ⁾ (Id A) s s'
       unequal head constants:
         s
       does not equal
         s'
  
  [1]
  $ agdarya stream.ny -e "s_eq_s'' : Id (Stream A) s s''" -e "s_eq_s'' = refl s"
   ￫ warning[W2305]
   ￮ can't write compiled file: $TESTCASE_ROOT/stream.nyo
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | s_eq_s'' = refl s
     ^ term synthesized type
         Stream⁽ᵉ⁾ (Id A) s s
       but is being checked against type
         Stream⁽ᵉ⁾ (Id A) s (corec A (Stream A) (λ x → x head) (λ x → x tail) s)
       unequal head constants:
         s
       does not equal
         corec
  
  [1]
  $ agdarya stream.ny -e "∞eta_bisim' : Id (Stream A → Stream A) (λ s → s) (λ s → ∞eta s)" -e "∞eta_bisim' = refl (λ s → ∞eta s)"
   ￫ warning[W2305]
   ￮ can't write compiled file: $TESTCASE_ROOT/stream.nyo
  
   ￫ error[E0401]
   ￭ command-line exec string
   1 | ∞eta_bisim' = refl (λ s → ∞eta s)
     ^ term synthesized type
         {𝑥₀ : Stream A} {𝑥₁ : Stream A} (𝑥₂ : Stream⁽ᵉ⁾ (Id A) 𝑥₀ 𝑥₁)
         →⁽ᵉ⁾ Stream⁽ᵉ⁾ (Id A) (∞eta 𝑥₀) (∞eta 𝑥₁)
       but is being checked against type
         {𝑥₀ : Stream A} {𝑥₁ : Stream A} (𝑥₂ : Stream⁽ᵉ⁾ (Id A) 𝑥₀ 𝑥₁)
         →⁽ᵉ⁾ Stream⁽ᵉ⁾ (Id A) 𝑥₀ (∞eta 𝑥₁)
       unequal head terms:
         ∞eta
       does not equal
         𝑥
  
  [1]
