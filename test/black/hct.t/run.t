  $ agdarya -v sqrt.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0000]
   ￮ constant √A defined
  
   ￫ info[I0001]
   ￮ postulate s0 assumed
  
   ￫ info[I0001]
   ￮ postulate s1 assumed
  
   ￫ info[I0001]
   ￮ postulate s2 assumed
  
  s2 root
    : A
  
  s2 root
    : A
  
   ￫ info[I0001]
   ￮ postulate s00 assumed
  
   ￫ info[I0001]
   ￮ postulate s01 assumed
  
   ￫ info[I0001]
   ￮ postulate s10 assumed
  
   ￫ info[I0001]
   ￮ postulate s11 assumed
  
   ￫ info[I0001]
   ￮ postulate s02 assumed
  
   ￫ info[I0001]
   ￮ postulate s12 assumed
  
   ￫ info[I0001]
   ￮ postulate s20 assumed
  
   ￫ info[I0001]
   ￮ postulate s21 assumed
  
   ￫ info[I0001]
   ￮ postulate s22 assumed
  
  s22 root⟨1⟩
    : Id A (s20 root) (s21 root)
  
  sym s22 root⟨1⟩
    : Id A (s02 root) (s12 root)
  
  refl s2 root⟨1⟩
    : Id A (s2 root) (s2 root)
  
  s2⁽ᵉ¹⁾ root⟨1⟩
    : Id A (refl s0 root) (refl s1 root)
  
  refl s2 root⟨1⟩
    : Id A (s2 root) (s2 root)
  
  s0⁽ᵉᵉ⁾ root⟨1⟩
    : Id A (refl s0 root) (refl s0 root)
  
  s0⁽ᵉᵉ⁾ root⟨1⟩
    : Id A (refl s0 root) (refl s0 root)
  
   ￫ info[I0001]
   ￮ postulate B assumed
  
   ￫ info[I0001]
   ￮ postulate f assumed
  
   ￫ info[I0000]
   ￮ constant √f defined
  
   ￫ info[I0001]
   ￮ postulate b0 assumed
  
   ￫ info[I0001]
   ￮ postulate b1 assumed
  
   ￫ info[I0001]
   ￮ postulate b2 assumed
  
  f b0 b1 b2
    : A
  
   ￫ info[I0001]
   ￮ postulate t00 assumed
  
   ￫ info[I0001]
   ￮ postulate t01 assumed
  
   ￫ info[I0001]
   ￮ postulate t10 assumed
  
   ￫ info[I0001]
   ￮ postulate t11 assumed
  
   ￫ info[I0001]
   ￮ postulate t02 assumed
  
   ￫ info[I0001]
   ￮ postulate t12 assumed
  
   ￫ info[I0001]
   ￮ postulate t20 assumed
  
   ￫ info[I0001]
   ￮ postulate t21 assumed
  
   ￫ info[I0001]
   ￮ postulate t22 assumed
  
  refl f t20 t21 (sym t22)
    : Id A (f t00 t01 t02) (f t10 t11 t12)
  
  refl f t02 t12 t22
    : Id A (f t00 t10 t20) (f t01 t11 t21)
  
   ￫ info[I0001]
   ￮ postulate a assumed
  
   ￫ info[I0000]
   ￮ constant √a defined
  
  a
    : A
  
  refl a
    : Id A a a
  
  refl a
    : Id A a a
  
   ￫ info[I0000]
   ￮ constant s2' defined
  
  a
    : A
  
  refl f b2 b2 b2⁽ᵉ¹⁾
    : Id A (f b0 b0 (refl b0)) (f b1 b1 (refl b1))
  
  refl a
    : Id A a a
  
   ￫ info[I0000]
   ￮ constant ID defined
  
   ￫ info[I0000]
   ￮ constant √IDA defined
  
   ￫ info[I0000]
   ￮ constant η defined
  
   ￫ info[I0001]
   ￮ postulate a0 assumed
  
   ￫ info[I0001]
   ￮ postulate a1 assumed
  
   ￫ info[I0001]
   ￮ postulate a2 assumed
  
  a0
    : A
  
  a1
    : A
  
  a2
    : Id A a0 a1
  
   ￫ info[I0001]
   ￮ postulate u0 assumed
  
   ￫ info[I0001]
   ￮ postulate u1 assumed
  
   ￫ info[I0001]
   ￮ postulate u2 assumed
  
  u2 root
    : ID A
  
   ￫ info[I0000]
   ￮ constant u2' defined, containing 2 holes
  
   ￫ info[I3003]
   ￮ hole ?0:
     
     ----------------------------------------------------------------------
     refl ID (Id A) (refl u0 root) (refl u1 root)
  
   ￫ info[I3003]
   ￮ hole ?1:
     
     ----------------------------------------------------------------------
     ID A
  
   ￫ info[I0001]
   ￮ postulate u00 assumed
  
   ￫ info[I0001]
   ￮ postulate u01 assumed
  
   ￫ info[I0001]
   ￮ postulate u02 assumed
  
   ￫ info[I0001]
   ￮ postulate u10 assumed
  
   ￫ info[I0001]
   ￮ postulate u11 assumed
  
   ￫ info[I0001]
   ￮ postulate u12 assumed
  
   ￫ info[I0001]
   ￮ postulate u20 assumed
  
   ￫ info[I0001]
   ￮ postulate u21 assumed
  
   ￫ info[I0001]
   ￮ postulate u22 assumed
  
  u22 root⟨1⟩
    : ID⁽ᵉ⁾ (Id A) (u20 root) (u21 root)
  
  sym u22 root⟨1⟩
    : ID⁽ᵉ⁾ (Id A) (u02 root) (u12 root)
  
   ￫ info[I0000]
   ￮ constant u22' defined, containing 3 holes
  
   ￫ info[I3003]
   ￮ hole ?2:
     
     ----------------------------------------------------------------------
     ID⁽ᵉᵉ⁾ A⁽ᵉᵉ⁾ (u02⁽ᵉ¹⁾ root⟨1⟩) (u12⁽ᵉ¹⁾ root⟨1⟩) (u20⁽ᵉ¹⁾ root⟨1⟩)
       (u21⁽ᵉ¹⁾ root⟨1⟩)
  
   ￫ info[I3003]
   ￮ hole ?3:
     
     ----------------------------------------------------------------------
     refl ID (Id A) (u20 root) (u21 root)
  
   ￫ info[I3003]
   ￮ hole ?4:
     
     ----------------------------------------------------------------------
     refl ID (Id A) (u02 root) (u12 root)
  
   ￫ error[E3002]
   ￮ file sqrt.ny contains open holes
  
  [1]

  $ agdarya -v 2dsqrt.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0000]
   ￮ constant √√A defined
  
   ￫ info[I0001]
   ￮ postulate s000 assumed
  
   ￫ info[I0001]
   ￮ postulate s001 assumed
  
   ￫ info[I0001]
   ￮ postulate s002 assumed
  
   ￫ info[I0001]
   ￮ postulate s010 assumed
  
   ￫ info[I0001]
   ￮ postulate s011 assumed
  
   ￫ info[I0001]
   ￮ postulate s012 assumed
  
   ￫ info[I0001]
   ￮ postulate s020 assumed
  
   ￫ info[I0001]
   ￮ postulate s021 assumed
  
   ￫ info[I0001]
   ￮ postulate s022 assumed
  
   ￫ info[I0001]
   ￮ postulate s100 assumed
  
   ￫ info[I0001]
   ￮ postulate s101 assumed
  
   ￫ info[I0001]
   ￮ postulate s102 assumed
  
   ￫ info[I0001]
   ￮ postulate s110 assumed
  
   ￫ info[I0001]
   ￮ postulate s111 assumed
  
   ￫ info[I0001]
   ￮ postulate s112 assumed
  
   ￫ info[I0001]
   ￮ postulate s120 assumed
  
   ￫ info[I0001]
   ￮ postulate s121 assumed
  
   ￫ info[I0001]
   ￮ postulate s122 assumed
  
   ￫ info[I0001]
   ￮ postulate s200 assumed
  
   ￫ info[I0001]
   ￮ postulate s201 assumed
  
   ￫ info[I0001]
   ￮ postulate s202 assumed
  
   ￫ info[I0001]
   ￮ postulate s210 assumed
  
   ￫ info[I0001]
   ￮ postulate s211 assumed
  
   ￫ info[I0001]
   ￮ postulate s212 assumed
  
   ￫ info[I0001]
   ￮ postulate s220 assumed
  
   ￫ info[I0001]
   ￮ postulate s221 assumed
  
   ￫ info[I0001]
   ￮ postulate s222 assumed
  
  s222 rroot⟨12⟩
    : Id A (s220 rroot⟨12⟩) (s221 rroot⟨12⟩)
  
  s222⁽¹³²⁾ rroot⟨12⟩
    : Id A (s202 rroot⟨12⟩) (s212 rroot⟨12⟩)
  
  s222⁽²³¹⁾ rroot⟨12⟩
    : Id A (s022 rroot⟨12⟩) (s122 rroot⟨12⟩)
  
  s222⁽²¹³⁾ rroot⟨12⟩
    : Id A (sym s220 rroot⟨12⟩) (sym s221 rroot⟨12⟩)
  
  s222⁽³²¹⁾ rroot⟨12⟩
    : Id A (sym s022 rroot⟨12⟩) (sym s122 rroot⟨12⟩)
  
  s222⁽³¹²⁾ rroot⟨12⟩
    : Id A (sym s202 rroot⟨12⟩) (sym s212 rroot⟨12⟩)
  
   ￫ info[I0000]
   ￮ constant ID2 defined
  
   ￫ info[I0000]
   ￮ constant √√ID2A defined
  
   ￫ info[I0000]
   ￮ constant t defined
  
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
  
   ￫ info[I0000]
   ￮ constant ta defined
  
  t⁽ᵉᵉ⁾ a22 rroot⟨12⟩
    : ID2 A
  
  t⁽ᵉᵉ⁾ (sym a22) rroot⟨12⟩
    : ID2 A
  
  a00
    : A
  
  a00
    : A
  
  a01
    : A
  
  a10
    : A
  
  a02
    : Id A a00 a01
  
  a20
    : Id A a00 a10
  
  a10
    : A
  
  a01
    : A
  
  a11
    : A
  
  a11
    : A
  
  a12
    : Id A a10 a11
  
  a21
    : Id A a01 a11
  
  a20
    : Id A a00 a10
  
  a02
    : Id A a00 a01
  
  a21
    : Id A a01 a11
  
  a12
    : Id A a10 a11
  
  a22
    : A⁽ᵉᵉ⁾ a02 a12 a20 a21
  
  sym a22
    : A⁽ᵉᵉ⁾ a20 a21 a02 a12
  
  t⁽ᵉᵉ⁾ (sym a22) rroot⟨12⟩
    : ID2 A
  
  t⁽ᵉᵉ⁾ (sym a22) rroot⟨12⟩
    : ID2 A
  
  a10
    : A
  
  a10
    : A
  
  a20
    : Id A a00 a10
  
  a20
    : Id A a00 a10
  

  $ agdarya -v sqrtsqrt.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0000]
   ￮ constant √A defined
  
   ￫ info[I0000]
   ￮ constant √√A defined
  
   ￫ info[I0000]
   ￮ constant √_√A defined
  
   ￫ info[I0000]
   ￮ constant f defined
  
   ￫ info[I0000]
   ￮ constant g defined
  
   ￫ info[I0000]
   ￮ constant fg defined
  
   ￫ info[I0000]
   ￮ constant gf defined
  
  $ cat >sqrterr.ny <<EOF
  > postulate A : Set
  > √A : Set
  > √A = codata [ root⟨e⟩ x : A ]
  > postulate B : Set
  > postulate f (y0 y1 : B) (y2 : Id B y0 y1) : A
  > √f2 : B → √A
  > √f2 b = record { root⟨e⟩ = f b⟨0⟩ b⟨1⟩ b⟨2⟩; root⟨ee⟩ = f }
  > EOF

  $ agdarya -v sqrterr.ny
   ￫ info[I0001]
   ￮ postulate A assumed
  
   ￫ info[I0000]
   ￮ constant √A defined
  
   ￫ info[I0001]
   ￮ postulate B assumed
  
   ￫ info[I0001]
   ￮ postulate f assumed
  
   ￫ error[E1403]
   ￭ $TESTCASE_ROOT/sqrterr.ny
   1 | √f2 b = record { root⟨e⟩ = f b⟨0⟩ b⟨1⟩ b⟨2⟩; root⟨ee⟩ = f }
     ^ method 'root.ee' in comatch doesn't occur in codata type
  
  [1]

  $ cat >flderr.ny <<EOF
  > record A : Set where { field x : Set }
  > postulate a:A
  > postulate b:A
  > postulate c:Id A a b
  > echo c x⟨1⟩
  > EOF

  $ agdarya flderr.ny
   ￫ error[E0801]
   ￭ $TESTCASE_ROOT/flderr.ny
   1 | echo c x⟨1⟩
     ^ field x of record type
         A⁽ᵉ⁾ a b
       has intrinsic dimension 0 and used at dimension e, can't have suffix .1
  
  [1]
