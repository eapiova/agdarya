  $ agdarya -v natarith.ny
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
  
   ￫ info[I0000]
   ￮ constant ℕ_ind defined
  
   ￫ info[I0000]
   ￮ constant zero defined
  
   ￫ info[I0000]
   ￮ constant one defined
  
   ￫ info[I0000]
   ￮ constant two defined
  
   ￫ info[I0000]
   ￮ constant three defined
  
   ￫ info[I0000]
   ￮ constant four defined
  
   ￫ info[I0000]
   ￮ constant id00 defined
  
   ￫ info[I0000]
   ￮ constant id00' defined
  
   ￫ info[I0000]
   ￮ constant id00'' defined
  
   ￫ info[I0000]
   ￮ constant id11 defined
  
   ￫ info[I0000]
   ￮ constant congsuc defined
  
   ￫ info[I0000]
   ￮ constant cong2suc defined
  
   ￫ info[I0000]
   ￮ constant one_plus_one_eq_two defined
  
   ￫ info[I0000]
   ￮ constant one_plus_two_eq_three defined
  
   ￫ info[I0000]
   ￮ constant two_plus_zero_eq_two defined
  
   ￫ info[I0000]
   ￮ constant zero_plus_zero_eq_zero defined
  
   ￫ info[I0000]
   ￮ constant zero_plus_one_eq_one defined
  
   ￫ info[I0000]
   ￮ constant zero_plus_two_eq_two defined
  
   ￫ info[I0000]
   ￮ constant r000 defined
  
   ￫ info[I0000]
   ￮ constant r112 defined
  
   ￫ info[I0000]
   ￮ constant rplus defined
  
   ￫ info[I0000]
   ￮ constant one_plus_one_eq_two' defined
  
   ￫ info[I0000]
   ￮ constant one_plus_two_eq_three' defined
  
   ￫ info[I0000]
   ￮ constant two_plus_zero_eq_two' defined
  
   ￫ info[I0000]
   ￮ constant zero_plus_zero_eq_zero' defined
  
   ￫ info[I0000]
   ￮ constant zero_plus_one_eq_one' defined
  
   ￫ info[I0000]
   ￮ constant zero_plus_two_eq_two' defined
  
   ￫ info[I0000]
   ￮ constant plus_is_rplus defined
  
   ￫ info[I0000]
   ￮ constant one_times_zero_eq_zero defined
  
   ￫ info[I0000]
   ￮ constant zero_times_one_eq_zero defined
  
   ￫ info[I0000]
   ￮ constant one_times_one_eq_one defined
  
   ￫ info[I0000]
   ￮ constant two_times_two_eq_four defined
  
  $ agdarya natarith.ny -e "id01 : Id ℕ zero (suc zero)" -e "id01 = ℕ.zero"
   ￫ error[E1002]
   ￭ command-line exec string
   1 | id01 = ℕ.zero
     ^ instantiation arguments of datatype must be matching constructors:
       expected
         zero
       but got
         suc
  
  [1]
  $ agdarya natarith.ny -e "one_plus_one_eq_one : Id ℕ (plus one one) one" -e "one_plus_one_eq_one = refl one"
   ￫ error[E0401]
   ￭ command-line exec string
   1 | one_plus_one_eq_one = refl one
     ^ term synthesized type
         ℕ⁽ᵉ⁾ 1 1
       but is being checked against type
         ℕ⁽ᵉ⁾ 2 1
       unequal constructors:
         zero
       does not equal
         suc
  
  [1]
  $ agdarya natarith.ny -e "one_plus_one_eq_three : Id ℕ (plus one one) three" -e "one_plus_one_eq_three = refl three"
   ￫ error[E0401]
   ￭ command-line exec string
   1 | one_plus_one_eq_three = refl three
     ^ term synthesized type
         ℕ⁽ᵉ⁾ 3 3
       but is being checked against type
         ℕ⁽ᵉ⁾ 2 3
       unequal constructors:
         suc
       does not equal
         zero
  
  [1]
  $ agdarya natarith.ny -e "one_plus_two_eq_one : Id ℕ (plus one two) one" -e "one_plus_two_eq_one = refl one"
   ￫ error[E0401]
   ￭ command-line exec string
   1 | one_plus_two_eq_one = refl one
     ^ term synthesized type
         ℕ⁽ᵉ⁾ 1 1
       but is being checked against type
         ℕ⁽ᵉ⁾ 3 1
       unequal constructors:
         zero
       does not equal
         suc
  
  [1]
  $ agdarya natarith.ny -e "one_plus_one_eq_one' : Id ℕ (rplus one one) one" -e "one_plus_one_eq_one' = refl one"
   ￫ error[E0401]
   ￭ command-line exec string
   1 | one_plus_one_eq_one' = refl one
     ^ term synthesized type
         ℕ⁽ᵉ⁾ 1 1
       but is being checked against type
         ℕ⁽ᵉ⁾ 2 1
       unequal constructors:
         zero
       does not equal
         suc
  
  [1]
  $ agdarya natarith.ny -e "one_plus_one_eq_three' : Id ℕ (rplus one one) three" -e "one_plus_one_eq_three' = refl three"
   ￫ error[E0401]
   ￭ command-line exec string
   1 | one_plus_one_eq_three' = refl three
     ^ term synthesized type
         ℕ⁽ᵉ⁾ 3 3
       but is being checked against type
         ℕ⁽ᵉ⁾ 2 3
       unequal constructors:
         suc
       does not equal
         zero
  
  [1]
  $ agdarya natarith.ny -e "one_plus_two_eq_one' : Id ℕ (rplus one two) one" -e "one_plus_two_eq_one' = refl one"
   ￫ error[E0401]
   ￭ command-line exec string
   1 | one_plus_two_eq_one' = refl one
     ^ term synthesized type
         ℕ⁽ᵉ⁾ 1 1
       but is being checked against type
         ℕ⁽ᵉ⁾ 3 1
       unequal constructors:
         zero
       does not equal
         suc
  
  [1]
