  $ agdarya -v sym.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate a00 assumed
  
   ￫ info[I0001]
   ￮ postulate a01 assumed
  
   ￫ info[I0001]
   ￮ postulate a02 assumed
  
   ￫ info[I0001]
   ￮ postulate a10 assumed
  
   ￫ info[I0001]
   ￮ postulate a11 assumed
  
   ￫ info[I0001]
   ￮ postulate a12 assumed
  
   ￫ info[I0001]
   ￮ postulate a20 assumed
  
   ￫ info[I0001]
   ￮ postulate a21 assumed
  
   ￫ info[I0001]
   ￮ postulate a22 assumed
  
  sym a22
    : A⁽ᵉᵉ⁾ a20 a21 a02 a12
  
  a22
    : A⁽ᵉᵉ⁾ a02 a12 a20 a21
  
   ￫ info[I0000]
   ￮ constant sym_involution defined
  
   ￫ info[I0001]
   ￮ postulate B assumed
  
   ￫ info[I0001]
   ￮ postulate f assumed
  
  f⁽ᵉᵉ⁾ (sym a22)
    : B⁽ᵉᵉ⁾ (refl f a20) (refl f a21) (refl f a02) (refl f a12)
  
  f⁽ᵉᵉ⁾ (sym a22)
    : B⁽ᵉᵉ⁾ (refl f a20) (refl f a21) (refl f a02) (refl f a12)
  
   ￫ info[I0000]
   ￮ constant ap_sym defined
  

  $ agdarya sym.ny -e "echo sym a00"
  sym a22
    : A⁽ᵉᵉ⁾ a20 a21 a02 a12
  
  a22
    : A⁽ᵉᵉ⁾ a02 a12 a20 a21
  
  f⁽ᵉᵉ⁾ (sym a22)
    : B⁽ᵉᵉ⁾ (refl f a20) (refl f a21) (refl f a02) (refl f a12)
  
  f⁽ᵉᵉ⁾ (sym a22)
    : B⁽ᵉᵉ⁾ (refl f a20) (refl f a21) (refl f a02) (refl f a12)
  
   ￫ error[E0601]
   ￭ command-line exec string
   1 | echo sym a00
     ^ insufficient dimension for argument of degeneracy 'sym':
        0 does not factor through ee
  
  [1]

  $ agdarya sym.ny -e "echo sym a02"
  sym a22
    : A⁽ᵉᵉ⁾ a20 a21 a02 a12
  
  a22
    : A⁽ᵉᵉ⁾ a02 a12 a20 a21
  
  f⁽ᵉᵉ⁾ (sym a22)
    : B⁽ᵉᵉ⁾ (refl f a20) (refl f a21) (refl f a02) (refl f a12)
  
  f⁽ᵉᵉ⁾ (sym a22)
    : B⁽ᵉᵉ⁾ (refl f a20) (refl f a21) (refl f a02) (refl f a12)
  
   ￫ error[E0601]
   ￭ command-line exec string
   1 | echo sym a02
     ^ insufficient dimension for argument of degeneracy 'sym':
        e does not factor through ee
  
  [1]

  $ agdarya -v symsym.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate a000 assumed
  
   ￫ info[I0001]
   ￮ postulate a001 assumed
  
   ￫ info[I0001]
   ￮ postulate a002 assumed
  
   ￫ info[I0001]
   ￮ postulate a010 assumed
  
   ￫ info[I0001]
   ￮ postulate a011 assumed
  
   ￫ info[I0001]
   ￮ postulate a012 assumed
  
   ￫ info[I0001]
   ￮ postulate a020 assumed
  
   ￫ info[I0001]
   ￮ postulate a021 assumed
  
   ￫ info[I0001]
   ￮ postulate a022 assumed
  
   ￫ info[I0001]
   ￮ postulate a100 assumed
  
   ￫ info[I0001]
   ￮ postulate a101 assumed
  
   ￫ info[I0001]
   ￮ postulate a102 assumed
  
   ￫ info[I0001]
   ￮ postulate a110 assumed
  
   ￫ info[I0001]
   ￮ postulate a111 assumed
  
   ￫ info[I0001]
   ￮ postulate a112 assumed
  
   ￫ info[I0001]
   ￮ postulate a120 assumed
  
   ￫ info[I0001]
   ￮ postulate a121 assumed
  
   ￫ info[I0001]
   ￮ postulate a122 assumed
  
   ￫ info[I0001]
   ￮ postulate a200 assumed
  
   ￫ info[I0001]
   ￮ postulate a201 assumed
  
   ￫ info[I0001]
   ￮ postulate a202 assumed
  
   ￫ info[I0001]
   ￮ postulate a210 assumed
  
   ￫ info[I0001]
   ￮ postulate a211 assumed
  
   ￫ info[I0001]
   ￮ postulate a212 assumed
  
   ￫ info[I0001]
   ￮ postulate a220 assumed
  
   ￫ info[I0001]
   ￮ postulate a221 assumed
  
   ￫ info[I0001]
   ￮ postulate a222 assumed
  
  a222
    : A⁽ᵉᵉᵉ⁾ a022 a122 a202 a212 a220 a221
  
  a222
    : A⁽ᵉᵉᵉ⁾ a022 a122 a202 a212 a220 a221
  
  sym a222
    : A⁽ᵉᵉᵉ⁾ (sym a022) (sym a122) a220 a221 a202 a212
  
  a222⁽¹³²⁾
    : A⁽ᵉᵉᵉ⁾ (sym a022) (sym a122) a220 a221 a202 a212
  
   ￫ info[I0000]
   ￮ constant sym2 defined
  
  a222⁽²¹³⁾
    : A⁽ᵉᵉᵉ⁾ a202 a212 a022 a122 (sym a220) (sym a221)
  
  a222⁽²¹³⁾
    : A⁽ᵉᵉᵉ⁾ a202 a212 a022 a122 (sym a220) (sym a221)
  
  a222⁽³¹²⁾
    : A⁽ᵉᵉᵉ⁾ a220 a221 (sym a022) (sym a122) (sym a202) (sym a212)
  
  a222⁽³¹²⁾
    : A⁽ᵉᵉᵉ⁾ a220 a221 (sym a022) (sym a122) (sym a202) (sym a212)
  
  a222⁽³²¹⁾
    : A⁽ᵉᵉᵉ⁾ (sym a220) (sym a221) (sym a202) (sym a212) (sym a022)
        (sym a122)
  
  a222⁽³²¹⁾
    : A⁽ᵉᵉᵉ⁾ (sym a220) (sym a221) (sym a202) (sym a212) (sym a022)
        (sym a122)
  
  a222⁽²³¹⁾
    : A⁽ᵉᵉᵉ⁾ (sym a202) (sym a212) (sym a220) (sym a221) a022 a122
  
  a222⁽²³¹⁾
    : A⁽ᵉᵉᵉ⁾ (sym a202) (sym a212) (sym a220) (sym a221) a022 a122
  
  a222⁽³²¹⁾
    : A⁽ᵉᵉᵉ⁾ (sym a220) (sym a221) (sym a202) (sym a212) (sym a022)
        (sym a122)
  
  a222⁽³²¹⁾
    : A⁽ᵉᵉᵉ⁾ (sym a220) (sym a221) (sym a202) (sym a212) (sym a022)
        (sym a122)
  
   ￫ info[I0000]
   ￮ constant braid defined
  
   ￫ info[I0000]
   ￮ constant braid2 defined
  

  $ agdarya -v symfield.ny
   ￫ info[I0001]
   ￮ postulate B assumed
  
   ￫ info[I0000]
   ￮ constant A defined
  
   ￫ info[I0001]
   ￮ postulate a00 assumed
  
   ￫ info[I0001]
   ￮ postulate a01 assumed
  
   ￫ info[I0001]
   ￮ postulate a02 assumed
  
   ￫ info[I0001]
   ￮ postulate a10 assumed
  
   ￫ info[I0001]
   ￮ postulate a11 assumed
  
   ￫ info[I0001]
   ￮ postulate a12 assumed
  
   ￫ info[I0001]
   ￮ postulate a20 assumed
  
   ￫ info[I0001]
   ￮ postulate a21 assumed
  
   ￫ info[I0001]
   ￮ postulate a22 assumed
  
  sym a22 unwrap
    : B⁽ᵉᵉ⁾ (a20 unwrap) (a21 unwrap) (a02 unwrap) (a12 unwrap)
  
  sym a22 unwrap
    : B⁽ᵉᵉ⁾ (a20 unwrap) (a21 unwrap) (a02 unwrap) (a12 unwrap)
  
   ￫ info[I0000]
   ￮ constant Jd defined
  
   ￫ info[I0000]
   ￮ constant test defined
  
