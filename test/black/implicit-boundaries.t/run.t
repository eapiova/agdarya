  $ agdarya -v -fake-interact=implicit-boundaries.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate B assumed
  
   ￫ info[I0001]
   ￮ postulate f assumed
  
   ￫ info[I0001]
   ￮ postulate a0 assumed
  
   ￫ info[I0001]
   ￮ postulate a1 assumed
  
   ￫ info[I0001]
   ￮ postulate a2 assumed
  
  refl f a2
    : Id B (f a0) (f a1)
  
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
  
  f⁽ᵉᵉ⁾ a22
    : B⁽ᵉᵉ⁾ (refl f a02) (refl f a12) (refl f a20) (refl f a21)
  
  A⁽ᵉᵉ⁾ a02 a12 a20 a21
    : Set
  
  A⁽ᵉᵉ⁾ a02 a12 a20 a21
    : Set
  
  A⁽ᵉᵉ⁾ a02 a12 a20 a21
    : Set
  
  A⁽ᵉᵉ⁾ a02 a12 a20 a21
    : Set
  
   ￫ info[I0001]
   ￮ postulate g assumed
  
  refl g a02 a12 a22
    : Id B (g a00 a10 a20) (g a01 a11 a21)
  
   ￫ info[I0001]
   ￮ postulate C assumed
  
   ￫ info[I0000]
   ￮ constant A×B defined
  
   ￫ info[I0001]
   ￮ postulate h assumed
  
   ￫ info[I0001]
   ￮ postulate b0 assumed
  
   ￫ info[I0001]
   ￮ postulate b1 assumed
  
   ￫ info[I0001]
   ￮ postulate b2 assumed
  
  refl h {(a0, b0)} {(a1, b1)} (a2, b2)
    : Id C (h (a0, b0)) (h (a1, b1))
  
   ￫ info[I0001]
   ￮ postulate b00 assumed
  
   ￫ info[I0001]
   ￮ postulate b01 assumed
  
   ￫ info[I0001]
   ￮ postulate b02 assumed
  
   ￫ info[I0001]
   ￮ postulate b10 assumed
  
   ￫ info[I0001]
   ￮ postulate b11 assumed
  
   ￫ info[I0001]
   ￮ postulate b12 assumed
  
   ￫ info[I0001]
   ￮ postulate b20 assumed
  
   ￫ info[I0001]
   ￮ postulate b21 assumed
  
   ￫ info[I0001]
   ￮ postulate b22 assumed
  
  h⁽ᵉᵉ⁾ {(a00, b00)} {(a01, b01)} {(a02, b02)} {(a10, b10)} {(a11, b11)}
    {(a12, b12)} {(a20, b20)} {(a21, b21)} (a22, b22)
    : C⁽ᵉᵉ⁾ (refl h {(a00, b00)} {(a01, b01)} (a02, b02))
        (refl h {(a10, b10)} {(a11, b11)} (a12, b12))
        (refl h {(a00, b00)} {(a10, b10)} (a20, b20))
        (refl h {(a01, b01)} {(a11, b11)} (a21, b21))
  
  h⁽ᵉᵉ⁾ {(a00, b00)} {(a01, b01)} {(a02, b02)} {(a10, b10)} {(a11, b11)}
    {(a12, b12)} {(a20, b20)} {(a21, b21)} (a22, b22)
    : C⁽ᵉᵉ⁾ (refl h {(a00, b00)} {(a01, b01)} (a02, b02))
        (refl h {(a10, b10)} {(a11, b11)} (a12, b12))
        (refl h {(a00, b00)} {(a10, b10)} (a20, b20))
        (refl h {(a01, b01)} {(a11, b11)} (a21, b21))
  
   ￫ info[I0001]
   ￮ postulate ab10 assumed
  
   ￫ info[I0001]
   ￮ postulate ab11 assumed
  
   ￫ info[I0001]
   ￮ postulate ab12 assumed
  
   ￫ info[I0001]
   ￮ postulate ab20 assumed
  
   ￫ info[I0001]
   ￮ postulate ab21 assumed
  
   ￫ info[I0001]
   ￮ postulate ab22 assumed
  
  ab22
    : A×B⁽ᵉᵉ⁾ {(a00, b00)} {(a01, b01)} (a02, b02) ab12 ab20 ab21
  
  h⁽ᵉᵉ⁾ ab22
    : C⁽ᵉᵉ⁾ (refl h {(a00, b00)} {(a01, b01)} (a02, b02)) (refl h ab12)
        (refl h ab20) (refl h ab21)
  

  $ agdarya -v -show-function-boundaries -fake-interact=implicit-boundaries.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate B assumed
  
   ￫ info[I0001]
   ￮ postulate f assumed
  
   ￫ info[I0001]
   ￮ postulate a0 assumed
  
   ￫ info[I0001]
   ￮ postulate a1 assumed
  
   ￫ info[I0001]
   ￮ postulate a2 assumed
  
  refl f {a0} {a1} a2
    : Id B (f a0) (f a1)
  
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
  
  f⁽ᵉᵉ⁾ {a00} {a01} {a02} {a10} {a11} {a12} {a20} {a21} a22
    : B⁽ᵉᵉ⁾ (refl f {a00} {a01} a02) (refl f {a10} {a11} a12)
        (refl f {a00} {a10} a20) (refl f {a01} {a11} a21)
  
  A⁽ᵉᵉ⁾ a02 a12 a20 a21
    : Set
  
  A⁽ᵉᵉ⁾ a02 a12 a20 a21
    : Set
  
  A⁽ᵉᵉ⁾ a02 a12 a20 a21
    : Set
  
  A⁽ᵉᵉ⁾ a02 a12 a20 a21
    : Set
  
   ￫ info[I0001]
   ￮ postulate g assumed
  
  refl g {a00} {a01} a02 {a10} {a11} a12 {a20} {a21} a22
    : Id B (g a00 a10 a20) (g a01 a11 a21)
  
   ￫ info[I0001]
   ￮ postulate C assumed
  
   ￫ info[I0000]
   ￮ constant A×B defined
  
   ￫ info[I0001]
   ￮ postulate h assumed
  
   ￫ info[I0001]
   ￮ postulate b0 assumed
  
   ￫ info[I0001]
   ￮ postulate b1 assumed
  
   ￫ info[I0001]
   ￮ postulate b2 assumed
  
  refl h {(a0, b0)} {(a1, b1)} (a2, b2)
    : Id C (h (a0, b0)) (h (a1, b1))
  
   ￫ info[I0001]
   ￮ postulate b00 assumed
  
   ￫ info[I0001]
   ￮ postulate b01 assumed
  
   ￫ info[I0001]
   ￮ postulate b02 assumed
  
   ￫ info[I0001]
   ￮ postulate b10 assumed
  
   ￫ info[I0001]
   ￮ postulate b11 assumed
  
   ￫ info[I0001]
   ￮ postulate b12 assumed
  
   ￫ info[I0001]
   ￮ postulate b20 assumed
  
   ￫ info[I0001]
   ￮ postulate b21 assumed
  
   ￫ info[I0001]
   ￮ postulate b22 assumed
  
  h⁽ᵉᵉ⁾ {(a00, b00)} {(a01, b01)} {(a02, b02)} {(a10, b10)} {(a11, b11)}
    {(a12, b12)} {(a20, b20)} {(a21, b21)} (a22, b22)
    : C⁽ᵉᵉ⁾ (refl h {(a00, b00)} {(a01, b01)} (a02, b02))
        (refl h {(a10, b10)} {(a11, b11)} (a12, b12))
        (refl h {(a00, b00)} {(a10, b10)} (a20, b20))
        (refl h {(a01, b01)} {(a11, b11)} (a21, b21))
  
  h⁽ᵉᵉ⁾ {(a00, b00)} {(a01, b01)} {(a02, b02)} {(a10, b10)} {(a11, b11)}
    {(a12, b12)} {(a20, b20)} {(a21, b21)} (a22, b22)
    : C⁽ᵉᵉ⁾ (refl h {(a00, b00)} {(a01, b01)} (a02, b02))
        (refl h {(a10, b10)} {(a11, b11)} (a12, b12))
        (refl h {(a00, b00)} {(a10, b10)} (a20, b20))
        (refl h {(a01, b01)} {(a11, b11)} (a21, b21))
  
   ￫ info[I0001]
   ￮ postulate ab10 assumed
  
   ￫ info[I0001]
   ￮ postulate ab11 assumed
  
   ￫ info[I0001]
   ￮ postulate ab12 assumed
  
   ￫ info[I0001]
   ￮ postulate ab20 assumed
  
   ￫ info[I0001]
   ￮ postulate ab21 assumed
  
   ￫ info[I0001]
   ￮ postulate ab22 assumed
  
  ab22
    : A×B⁽ᵉᵉ⁾ {(a00, b00)} {(a01, b01)} (a02, b02) ab12 ab20 ab21
  
  h⁽ᵉᵉ⁾ {(a00, b00)} {(a01, b01)} {(a02, b02)} {ab10} {ab11} {ab12} {ab20}
    {ab21} ab22
    : C⁽ᵉᵉ⁾ (refl h {(a00, b00)} {(a01, b01)} (a02, b02))
        (refl h {ab10} {ab11} ab12) (refl h {(a00, b00)} {ab10} ab20)
        (refl h {(a01, b01)} {ab11} ab21)
  

  $ agdarya -v implicit-boundaries.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate B assumed
  
   ￫ info[I0001]
   ￮ postulate f assumed
  
   ￫ info[I0001]
   ￮ postulate a0 assumed
  
   ￫ info[I0001]
   ￮ postulate a1 assumed
  
   ￫ info[I0001]
   ￮ postulate a2 assumed
  
  refl f a2
    : Id B (f a0) (f a1)
  
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
  
  f⁽ᵉᵉ⁾ a22
    : B⁽ᵉᵉ⁾ (refl f a02) (refl f a12) (refl f a20) (refl f a21)
  
  A⁽ᵉᵉ⁾ a02 a12 a20 a21
    : Set
  
  A⁽ᵉᵉ⁾ a02 a12 a20 a21
    : Set
  
  A⁽ᵉᵉ⁾ a02 a12 a20 a21
    : Set
  
  A⁽ᵉᵉ⁾ a02 a12 a20 a21
    : Set
  
   ￫ info[I0001]
   ￮ postulate g assumed
  
  refl g a02 a12 a22
    : Id B (g a00 a10 a20) (g a01 a11 a21)
  
   ￫ info[I0001]
   ￮ postulate C assumed
  
   ￫ info[I0000]
   ￮ constant A×B defined
  
   ￫ info[I0001]
   ￮ postulate h assumed
  
   ￫ info[I0001]
   ￮ postulate b0 assumed
  
   ￫ info[I0001]
   ￮ postulate b1 assumed
  
   ￫ info[I0001]
   ￮ postulate b2 assumed
  
  refl h {(a0, b0)} {(a1, b1)} (a2, b2)
    : Id C (h (a0, b0)) (h (a1, b1))
  
   ￫ info[I0001]
   ￮ postulate b00 assumed
  
   ￫ info[I0001]
   ￮ postulate b01 assumed
  
   ￫ info[I0001]
   ￮ postulate b02 assumed
  
   ￫ info[I0001]
   ￮ postulate b10 assumed
  
   ￫ info[I0001]
   ￮ postulate b11 assumed
  
   ￫ info[I0001]
   ￮ postulate b12 assumed
  
   ￫ info[I0001]
   ￮ postulate b20 assumed
  
   ￫ info[I0001]
   ￮ postulate b21 assumed
  
   ￫ info[I0001]
   ￮ postulate b22 assumed
  
  h⁽ᵉᵉ⁾ {(a00, b00)} {(a01, b01)} {(a02, b02)} {(a10, b10)} {(a11, b11)}
    {(a12, b12)} {(a20, b20)} {(a21, b21)} (a22, b22)
    : C⁽ᵉᵉ⁾ (refl h {(a00, b00)} {(a01, b01)} (a02, b02))
        (refl h {(a10, b10)} {(a11, b11)} (a12, b12))
        (refl h {(a00, b00)} {(a10, b10)} (a20, b20))
        (refl h {(a01, b01)} {(a11, b11)} (a21, b21))
  
  h⁽ᵉᵉ⁾ {(a00, b00)} {(a01, b01)} {(a02, b02)} {(a10, b10)} {(a11, b11)}
    {(a12, b12)} {(a20, b20)} {(a21, b21)} (a22, b22)
    : C⁽ᵉᵉ⁾ (refl h {(a00, b00)} {(a01, b01)} (a02, b02))
        (refl h {(a10, b10)} {(a11, b11)} (a12, b12))
        (refl h {(a00, b00)} {(a10, b10)} (a20, b20))
        (refl h {(a01, b01)} {(a11, b11)} (a21, b21))
  
   ￫ info[I0001]
   ￮ postulate ab10 assumed
  
   ￫ info[I0001]
   ￮ postulate ab11 assumed
  
   ￫ info[I0001]
   ￮ postulate ab12 assumed
  
   ￫ info[I0001]
   ￮ postulate ab20 assumed
  
   ￫ info[I0001]
   ￮ postulate ab21 assumed
  
   ￫ info[I0001]
   ￮ postulate ab22 assumed
  
  ab22
    : A×B⁽ᵉᵉ⁾ {(a00, b00)} {(a01, b01)} (a02, b02) ab12 ab20 ab21
  
  h⁽ᵉᵉ⁾ ab22
    : C⁽ᵉᵉ⁾ (refl h {(a00, b00)} {(a01, b01)} (a02, b02)) (refl h ab12)
        (refl h ab20) (refl h ab21)
  
   ￫ warning[W2305]
   ￮ can't write compiled file: $TESTCASE_ROOT/implicit-boundaries.nyo
  

  $ agdarya -v -show-function-boundaries implicit-boundaries.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate B assumed
  
   ￫ info[I0001]
   ￮ postulate f assumed
  
   ￫ info[I0001]
   ￮ postulate a0 assumed
  
   ￫ info[I0001]
   ￮ postulate a1 assumed
  
   ￫ info[I0001]
   ￮ postulate a2 assumed
  
  refl f {a0} {a1} a2
    : Id B (f a0) (f a1)
  
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
  
  f⁽ᵉᵉ⁾ {a00} {a01} {a02} {a10} {a11} {a12} {a20} {a21} a22
    : B⁽ᵉᵉ⁾ (refl f {a00} {a01} a02) (refl f {a10} {a11} a12)
        (refl f {a00} {a10} a20) (refl f {a01} {a11} a21)
  
  A⁽ᵉᵉ⁾ a02 a12 a20 a21
    : Set
  
  A⁽ᵉᵉ⁾ a02 a12 a20 a21
    : Set
  
  A⁽ᵉᵉ⁾ a02 a12 a20 a21
    : Set
  
  A⁽ᵉᵉ⁾ a02 a12 a20 a21
    : Set
  
   ￫ info[I0001]
   ￮ postulate g assumed
  
  refl g {a00} {a01} a02 {a10} {a11} a12 {a20} {a21} a22
    : Id B (g a00 a10 a20) (g a01 a11 a21)
  
   ￫ info[I0001]
   ￮ postulate C assumed
  
   ￫ info[I0000]
   ￮ constant A×B defined
  
   ￫ info[I0001]
   ￮ postulate h assumed
  
   ￫ info[I0001]
   ￮ postulate b0 assumed
  
   ￫ info[I0001]
   ￮ postulate b1 assumed
  
   ￫ info[I0001]
   ￮ postulate b2 assumed
  
  refl h {(a0, b0)} {(a1, b1)} (a2, b2)
    : Id C (h (a0, b0)) (h (a1, b1))
  
   ￫ info[I0001]
   ￮ postulate b00 assumed
  
   ￫ info[I0001]
   ￮ postulate b01 assumed
  
   ￫ info[I0001]
   ￮ postulate b02 assumed
  
   ￫ info[I0001]
   ￮ postulate b10 assumed
  
   ￫ info[I0001]
   ￮ postulate b11 assumed
  
   ￫ info[I0001]
   ￮ postulate b12 assumed
  
   ￫ info[I0001]
   ￮ postulate b20 assumed
  
   ￫ info[I0001]
   ￮ postulate b21 assumed
  
   ￫ info[I0001]
   ￮ postulate b22 assumed
  
  h⁽ᵉᵉ⁾ {(a00, b00)} {(a01, b01)} {(a02, b02)} {(a10, b10)} {(a11, b11)}
    {(a12, b12)} {(a20, b20)} {(a21, b21)} (a22, b22)
    : C⁽ᵉᵉ⁾ (refl h {(a00, b00)} {(a01, b01)} (a02, b02))
        (refl h {(a10, b10)} {(a11, b11)} (a12, b12))
        (refl h {(a00, b00)} {(a10, b10)} (a20, b20))
        (refl h {(a01, b01)} {(a11, b11)} (a21, b21))
  
  h⁽ᵉᵉ⁾ {(a00, b00)} {(a01, b01)} {(a02, b02)} {(a10, b10)} {(a11, b11)}
    {(a12, b12)} {(a20, b20)} {(a21, b21)} (a22, b22)
    : C⁽ᵉᵉ⁾ (refl h {(a00, b00)} {(a01, b01)} (a02, b02))
        (refl h {(a10, b10)} {(a11, b11)} (a12, b12))
        (refl h {(a00, b00)} {(a10, b10)} (a20, b20))
        (refl h {(a01, b01)} {(a11, b11)} (a21, b21))
  
   ￫ info[I0001]
   ￮ postulate ab10 assumed
  
   ￫ info[I0001]
   ￮ postulate ab11 assumed
  
   ￫ info[I0001]
   ￮ postulate ab12 assumed
  
   ￫ info[I0001]
   ￮ postulate ab20 assumed
  
   ￫ info[I0001]
   ￮ postulate ab21 assumed
  
   ￫ info[I0001]
   ￮ postulate ab22 assumed
  
  ab22
    : A×B⁽ᵉᵉ⁾ {(a00, b00)} {(a01, b01)} (a02, b02) ab12 ab20 ab21
  
  h⁽ᵉᵉ⁾ {(a00, b00)} {(a01, b01)} {(a02, b02)} {ab10} {ab11} {ab12} {ab20}
    {ab21} ab22
    : C⁽ᵉᵉ⁾ (refl h {(a00, b00)} {(a01, b01)} (a02, b02))
        (refl h {ab10} {ab11} ab12) (refl h {(a00, b00)} {ab10} ab20)
        (refl h {(a01, b01)} {ab11} ab21)
  
   ￫ warning[W2305]
   ￮ can't write compiled file: $TESTCASE_ROOT/implicit-boundaries.nyo
  

  $ agdarya -v -show-type-boundaries -fake-interact=implicit-boundaries.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0001]
   ￮ postulate B assumed
  
   ￫ info[I0001]
   ￮ postulate f assumed
  
   ￫ info[I0001]
   ￮ postulate a0 assumed
  
   ￫ info[I0001]
   ￮ postulate a1 assumed
  
   ￫ info[I0001]
   ￮ postulate a2 assumed
  
  refl f a2
    : Id B (f a0) (f a1)
  
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
  
  f⁽ᵉᵉ⁾ a22
    : B⁽ᵉᵉ⁾ {f a00} {f a01} (refl f a02) {f a10} {f a11} (refl f a12)
        (refl f a20) (refl f a21)
  
  A⁽ᵉᵉ⁾ {a00} {a01} a02 {a10} {a11} a12 a20 a21
    : Set
  
  A⁽ᵉᵉ⁾ {a00} {a01} a02 {a10} {a11} a12 a20 a21
    : Set
  
  A⁽ᵉᵉ⁾ {a00} {a01} a02 {a10} {a11} a12 a20 a21
    : Set
  
  A⁽ᵉᵉ⁾ {a00} {a01} a02 {a10} {a11} a12 a20 a21
    : Set
  
   ￫ info[I0001]
   ￮ postulate g assumed
  
  refl g a02 a12 a22
    : Id B (g a00 a10 a20) (g a01 a11 a21)
  
   ￫ info[I0001]
   ￮ postulate C assumed
  
   ￫ info[I0000]
   ￮ constant A×B defined
  
   ￫ info[I0001]
   ￮ postulate h assumed
  
   ￫ info[I0001]
   ￮ postulate b0 assumed
  
   ￫ info[I0001]
   ￮ postulate b1 assumed
  
   ￫ info[I0001]
   ￮ postulate b2 assumed
  
  refl h {(a0, b0)} {(a1, b1)} (a2, b2)
    : Id C (h (a0, b0)) (h (a1, b1))
  
   ￫ info[I0001]
   ￮ postulate b00 assumed
  
   ￫ info[I0001]
   ￮ postulate b01 assumed
  
   ￫ info[I0001]
   ￮ postulate b02 assumed
  
   ￫ info[I0001]
   ￮ postulate b10 assumed
  
   ￫ info[I0001]
   ￮ postulate b11 assumed
  
   ￫ info[I0001]
   ￮ postulate b12 assumed
  
   ￫ info[I0001]
   ￮ postulate b20 assumed
  
   ￫ info[I0001]
   ￮ postulate b21 assumed
  
   ￫ info[I0001]
   ￮ postulate b22 assumed
  
  h⁽ᵉᵉ⁾ {(a00, b00)} {(a01, b01)} {(a02, b02)} {(a10, b10)} {(a11, b11)}
    {(a12, b12)} {(a20, b20)} {(a21, b21)} (a22, b22)
    : C⁽ᵉᵉ⁾ {h (a00, b00)} {h (a01, b01)}
        (refl h {(a00, b00)} {(a01, b01)} (a02, b02)) {h (a10, b10)}
        {h (a11, b11)} (refl h {(a10, b10)} {(a11, b11)} (a12, b12))
        (refl h {(a00, b00)} {(a10, b10)} (a20, b20))
        (refl h {(a01, b01)} {(a11, b11)} (a21, b21))
  
  h⁽ᵉᵉ⁾ {(a00, b00)} {(a01, b01)} {(a02, b02)} {(a10, b10)} {(a11, b11)}
    {(a12, b12)} {(a20, b20)} {(a21, b21)} (a22, b22)
    : C⁽ᵉᵉ⁾ {h (a00, b00)} {h (a01, b01)}
        (refl h {(a00, b00)} {(a01, b01)} (a02, b02)) {h (a10, b10)}
        {h (a11, b11)} (refl h {(a10, b10)} {(a11, b11)} (a12, b12))
        (refl h {(a00, b00)} {(a10, b10)} (a20, b20))
        (refl h {(a01, b01)} {(a11, b11)} (a21, b21))
  
   ￫ info[I0001]
   ￮ postulate ab10 assumed
  
   ￫ info[I0001]
   ￮ postulate ab11 assumed
  
   ￫ info[I0001]
   ￮ postulate ab12 assumed
  
   ￫ info[I0001]
   ￮ postulate ab20 assumed
  
   ￫ info[I0001]
   ￮ postulate ab21 assumed
  
   ￫ info[I0001]
   ￮ postulate ab22 assumed
  
  ab22
    : A×B⁽ᵉᵉ⁾ {(a00, b00)} {(a01, b01)} (a02, b02) {ab10} {ab11} ab12 ab20
        ab21
  
  h⁽ᵉᵉ⁾ ab22
    : C⁽ᵉᵉ⁾ {h (a00, b00)} {h (a01, b01)}
        (refl h {(a00, b00)} {(a01, b01)} (a02, b02)) {h ab10} {h ab11}
        (refl h ab12) (refl h ab20) (refl h ab21)
  
