 {- Transport and lifting compute on 2-dimensional Π-types -}

postulate A00 : Set

postulate A01 : Set

postulate A02 : Id Set A00 A01

postulate A10 : Set

postulate A11 : Set

postulate A12 : Id Set A10 A11

postulate A20 : Id Set A00 A10

postulate A21 : Id Set A01 A11

postulate A22 : Set⁽ᵉᵉ⁾ A02 A12 A20 A21

postulate B00 : A00 → Set

postulate B01 : A01 → Set

postulate B02 : Id ((X ↦ X → Set) : Set → Set) (A02) B00 B01

postulate B10 : A10 → Set

postulate B11 : A11 → Set

postulate B12 : Id ((X ↦ X → Set) : Set → Set) (A12) B10 B11

postulate B20 : Id ((X ↦ X → Set) : Set → Set) (A20) B00 B10

postulate B21 : Id ((X ↦ X → Set) : Set → Set) (A21) B01 B11

postulate B22 : ((X ↦ X → Set) : Set → Set)⁽ᵉᵉ⁾ (A22) B02 B12 B20 B21

postulate f00 : (x00 : A00) → B00 x00

postulate f01 : (x01 : A01) → B01 x01

postulate f02
  : Id ((λ X Y → (x : X) → Y x) : ((X : Set) (Y : X → Set) → Set)) A02 B02
      f00 f01

postulate a10 : A10

postulate a11 : A11

postulate a12 : A12 a10 a11

postulate f10 : (x10 : A10) → B10 x10

postulate f11 : (x11 : A11) → B11 x11

postulate f12
  : Id ((λ X Y → (x : X) → Y x) : ((X : Set) (Y : X → Set) → Set)) A12 B12
      f10 f11

postulate f20
  : Id ((λ X Y → (x : X) → Y x) : ((X : Set) (Y : X → Set) → Set)) A20 B20
      f00 f10

postulate f21
  : Id ((λ X Y → (x : X) → Y x) : ((X : Set) (Y : X → Set) → Set)) A21 B21
      f01 f11

postulate a01 : A01

postulate a21 : A21 a01 a11

echo ((λ X Y → (x : X) → Y x) : ((X : Set) (Y : X → Set) → Set))⁽ᵉᵉ⁾ A22
       B22 f02 f12 trr f20 a21

echo B22 (A22 (A02 liftl a01) (A12 liftl a11) liftl a21)
       (f02 (A02 liftl a01)) (f12 (A12 liftl a11)) trr
       (f20 (A22 (A02 liftl a01) (A12 liftl a11) trl a21))

Πtrr : Id (B21 a21 (f01 a01) (f11 a11))
         (((λ X Y → (x : X) → Y x) : ((X : Set) (Y : X → Set) → Set))⁽ᵉᵉ⁾
            A22 B22 f02 f12 trr⟨1⟩ f20 a21)
         (B22 (A22 (A02 liftl a01) (A12 liftl a11) liftl a21)
            (f02 (A02 liftl a01)) (f12 (A12 liftl a11)) trr
            (f20 (A22 (A02 liftl a01) (A12 liftl a11) trl a21)))

Πtrr = refl _

postulate a00 : A00

postulate a20 : A20 a00 a10

echo ((λ X Y → (x : X) → Y x) : ((X : Set) (Y : X → Set) → Set))⁽ᵉᵉ⁾ A22
       B22 f02 f12 trl f21 a20

echo B22 (A22 (A02 liftr a00) (A12 liftr a10) liftr a20)
       (f02 (A02 liftr a00)) (f12 (A12 liftr a10)) trl
       (f21 (A22 (A02 liftr a00) (A12 liftr a10) trr a20))

Πtrl : Id (B20 a20 (f00 a00) (f10 a10))
         (((λ X Y → (x : X) → Y x) : ((X : Set) (Y : X → Set) → Set))⁽ᵉᵉ⁾
            A22 B22 f02 f12 trl⟨1⟩ f21 a20)
         (B22 (A22 (A02 liftr a00) (A12 liftr a10) liftr a20)
            (f02 (A02 liftr a00)) (f12 (A12 liftr a10)) trl
            (f21 (A22 (A02 liftr a00) (A12 liftr a10) trr a20)))

Πtrl = refl _

postulate a02 : A02 a00 a01

postulate a22 : A22 a02 a12 a20 a21

echo ((λ X Y → (x : X) → Y x) : ((X : Set) (Y : X → Set) → Set))⁽ᵉᵉ⁾ A22
       B22 f02 f12 liftr f20 a22

Πliftr : Id
           (B22 a22 (f02 a02) (f12 a12) (f20 a20)
              (B22 (A22 (A02 liftl a01) (A12 liftl a11) liftl a21)
                 (f02 (A02 liftl a01)) (f12 (A12 liftl a11)) trr
                 (f20 (A22 (A02 liftl a01) (A12 liftl a11) trl a21))))
           (((λ X Y → (x : X) → Y x) : ((X : Set) (Y : X → Set) → Set))⁽ᵉᵉ⁾
              A22 B22 f02 f12 liftr f20 a22)
           (B22⁽¹²ᵉ⁾
              (A22⁽¹²ᵉ⁾
                 (sym (A02⁽ᵉ¹⁾ a02 (A02 liftl a01) liftl (refl a01)))
                 (A12⁽¹ᵉ⁾ (refl A10 liftr a10) (refl A11 liftr a11) liftr
                    a12)
                 (A20⁽¹ᵉ⁾ (A02⁽ᵉ¹⁾ a02 (A02 liftl a01) trl (refl a01))
                    (refl A10 liftr a10) liftr a20)
                 (A21⁽¹ᵉ⁾ (refl a01) (refl A11 liftr a11) liftr a21) liftr
                 a22)
              (f02⁽¹ᵉ⁾ (sym (A02⁽ᵉ¹⁾ a02 (A02 liftl a01) liftl (refl a01))))
              (f12⁽¹ᵉ⁾
                 (A12⁽¹ᵉ⁾ (refl A10 liftr a10) (refl A11 liftr a11) liftr
                    a12))
              (refl f20
                 (A20⁽¹ᵉ⁾ (A02⁽ᵉ¹⁾ a02 (A02 liftl a01) trl (refl a01))
                    (refl A10 liftr a10) liftr a20))
              (B22⁽¹²ᵉ⁾
                 (A22⁽¹²ᵉ⁾ (A02⁽¹ᵉ⁾ liftl⟨1⟩ (refl a01))
                    (A12⁽¹ᵉ⁾ liftl⟨1⟩ (refl A11 liftr a11)) liftl⟨1⟩
                    (A21⁽¹ᵉ⁾ (refl a01) (refl A11 liftr a11) liftr a21))
                 (f02⁽¹ᵉ⁾ (A02⁽¹ᵉ⁾ liftl⟨1⟩ (refl a01)))
                 (f12⁽¹ᵉ⁾ (A12⁽¹ᵉ⁾ liftl⟨1⟩ (refl A11 liftr a11))) trr⟨1⟩
                 (refl f20
                    (A22⁽¹²ᵉ⁾ (A02⁽¹ᵉ⁾ liftl⟨1⟩ (refl a01))
                       (A12⁽¹ᵉ⁾ liftl⟨1⟩ (refl A11 liftr a11)) trl⟨1⟩
                       (A21⁽¹ᵉ⁾ (refl a01) (refl A11 liftr a11) liftr a21))))
              trl
              (B22⁽¹²ᵉ⁾
                 (A22⁽¹²ᵉ⁾ (refl A02 liftl⟨1⟩ (refl a01))
                    (sym
                       (A12⁽ᵉ¹⁾
                          (A12⁽¹ᵉ⁾ (refl A10 liftr a10)
                             (refl A11 liftr a11) trr a12)
                          (A12 liftl (refl A11 trr a11)) liftl
                          (A11⁽ᵉᵉ⁾ trr⟨1⟩ (refl a11))))
                    (A20⁽¹ᵉ⁾ (refl A02 trl⟨1⟩ (refl a01))
                       (A12⁽ᵉ¹⁾
                          (A12⁽¹ᵉ⁾ (refl A10 liftr a10)
                             (refl A11 liftr a11) trr a12)
                          (A12 liftl (refl A11 trr a11)) trl
                          (A11⁽ᵉᵉ⁾ trr⟨1⟩ (refl a11))) liftr
                       (A20⁽¹ᵉ⁾
                          (A02⁽ᵉ¹⁾ a02 (A02 liftl a01) trl (refl a01))
                          (refl A10 liftr a10) trr a20))
                    (A21⁽¹ᵉ⁾ (refl a01) (A11⁽ᵉᵉ⁾ trr⟨1⟩ (refl a11)) liftr
                       (A21⁽¹ᵉ⁾ (refl a01) (refl A11 liftr a11) trr a21))
                    liftr
                    (A22⁽¹²ᵉ⁾
                       (sym (A02⁽ᵉ¹⁾ a02 (A02 liftl a01) liftl (refl a01)))
                       (A12⁽¹ᵉ⁾ (refl A10 liftr a10) (refl A11 liftr a11)
                          liftr a12)
                       (A20⁽¹ᵉ⁾
                          (A02⁽ᵉ¹⁾ a02 (A02 liftl a01) trl (refl a01))
                          (refl A10 liftr a10) liftr a20)
                       (A21⁽¹ᵉ⁾ (refl a01) (refl A11 liftr a11) liftr a21)
                       trr a22)) (f02⁽¹ᵉ⁾ (refl A02 liftl⟨1⟩ (refl a01)))
                 (f12⁽¹ᵉ⁾
                    (sym
                       (A12⁽ᵉ¹⁾
                          (A12⁽¹ᵉ⁾ (refl A10 liftr a10)
                             (refl A11 liftr a11) trr a12)
                          (A12 liftl (refl A11 trr a11)) liftl
                          (A11⁽ᵉᵉ⁾ trr⟨1⟩ (refl a11)))))
                 (refl f20
                    (A20⁽¹ᵉ⁾ (refl A02 trl⟨1⟩ (refl a01))
                       (A12⁽ᵉ¹⁾
                          (A12⁽¹ᵉ⁾ (refl A10 liftr a10)
                             (refl A11 liftr a11) trr a12)
                          (A12 liftl (refl A11 trr a11)) trl
                          (A11⁽ᵉᵉ⁾ trr⟨1⟩ (refl a11))) liftr
                       (A20⁽¹ᵉ⁾
                          (A02⁽ᵉ¹⁾ a02 (A02 liftl a01) trl (refl a01))
                          (refl A10 liftr a10) trr a20)))
                 (B22⁽¹²ᵉ⁾
                    (A22⁽¹²ᵉ⁾ (refl A02 liftl⟨1⟩ (refl a01))
                       (A12⁽¹ᵉ⁾ liftl⟨1⟩ (A11⁽ᵉᵉ⁾ trr⟨1⟩ (refl a11)))
                       liftl⟨1⟩
                       (A21⁽¹ᵉ⁾ (refl a01) (A11⁽ᵉᵉ⁾ trr⟨1⟩ (refl a11))
                          liftr
                          (A21⁽¹ᵉ⁾ (refl a01) (refl A11 liftr a11) trr a21)))
                    (f02⁽¹ᵉ⁾ (refl A02 liftl⟨1⟩ (refl a01)))
                    (f12⁽¹ᵉ⁾ (A12⁽¹ᵉ⁾ liftl⟨1⟩ (A11⁽ᵉᵉ⁾ trr⟨1⟩ (refl a11))))
                    trr⟨1⟩
                    (refl f20
                       (A22⁽¹²ᵉ⁾ (refl A02 liftl⟨1⟩ (refl a01))
                          (A12⁽¹ᵉ⁾ liftl⟨1⟩ (A11⁽ᵉᵉ⁾ trr⟨1⟩ (refl a11)))
                          trl⟨1⟩
                          (A21⁽¹ᵉ⁾ (refl a01) (A11⁽ᵉᵉ⁾ trr⟨1⟩ (refl a11))
                             liftr
                             (A21⁽¹ᵉ⁾ (refl a01) (refl A11 liftr a11) trr
                                a21))))) trl
                 (B22⁽¹²ᵉ⁾
                    (sym
                       (A22⁽ᵉ¹⁾ (sym (refl A02 liftl⟨1⟩ (refl a01)))
                          (sym
                             (refl A12 liftl⟨1⟩ (A11⁽ᵉᵉ⁾ trr⟨1⟩ (refl a11))))
                          (A22⁽¹²ᵉ⁾ (refl A02 liftl⟨1⟩ (refl a01))
                             (sym
                                (A12⁽ᵉ¹⁾
                                   (A12⁽¹ᵉ⁾ (refl A10 liftr a10)
                                      (refl A11 liftr a11) trr a12)
                                   (A12 liftl (refl A11 trr a11)) liftl
                                   (A11⁽ᵉᵉ⁾ trr⟨1⟩ (refl a11))))
                             (A20⁽¹ᵉ⁾ (refl A02 trl⟨1⟩ (refl a01))
                                (A12⁽ᵉ¹⁾
                                   (A12⁽¹ᵉ⁾ (refl A10 liftr a10)
                                      (refl A11 liftr a11) trr a12)
                                   (A12 liftl (refl A11 trr a11)) trl
                                   (A11⁽ᵉᵉ⁾ trr⟨1⟩ (refl a11))) liftr
                                (A20⁽¹ᵉ⁾
                                   (A02⁽ᵉ¹⁾ a02 (A02 liftl a01) trl
                                      (refl a01)) (refl A10 liftr a10) trr
                                   a20))
                             (A21⁽¹ᵉ⁾ (refl a01)
                                (A11⁽ᵉᵉ⁾ trr⟨1⟩ (refl a11)) liftr
                                (A21⁽¹ᵉ⁾ (refl a01) (refl A11 liftr a11)
                                   trr a21)) trr
                             (A22⁽¹²ᵉ⁾
                                (sym
                                   (A02⁽ᵉ¹⁾ a02 (A02 liftl a01) liftl
                                      (refl a01)))
                                (A12⁽¹ᵉ⁾ (refl A10 liftr a10)
                                   (refl A11 liftr a11) liftr a12)
                                (A20⁽¹ᵉ⁾
                                   (A02⁽ᵉ¹⁾ a02 (A02 liftl a01) trl
                                      (refl a01)) (refl A10 liftr a10)
                                   liftr a20)
                                (A21⁽¹ᵉ⁾ (refl a01) (refl A11 liftr a11)
                                   liftr a21) trr a22))
                          (A22 (A02 liftl a01)
                             (A12 liftl (refl A11 trr a11)) liftl
                             (A21⁽¹ᵉ⁾ (refl a01)
                                (A11⁽ᵉᵉ⁾ trr⟨1⟩ (refl a11)) trr
                                (A21⁽¹ᵉ⁾ (refl a01) (refl A11 liftr a11)
                                   trr a21))) liftl
                          (A21⁽¹ᵉᵉ⁾ a01⁽ᵉᵉ⁾ (A11⁽ᵉᵉᵉ⁾ trr⟨1⟩ a11⁽ᵉᵉ⁾)
                             trr⟨1⟩
                             (A21⁽¹ᵉᵉ⁾ a01⁽ᵉᵉ⁾
                                (A11⁽ᵉᵉ⁾ liftr⟨1⟩ (refl a11)) trr⟨1⟩
                                (refl a21)))))
                    (f02⁽¹ᵉ⁾ (refl A02 liftl⟨1⟩ (refl a01)))
                    (f12⁽¹ᵉ⁾
                       (refl A12 liftl⟨1⟩ (A11⁽ᵉᵉ⁾ trr⟨1⟩ (refl a11))))
                    (refl f20
                       (A22⁽ᵉ¹⁾ (sym (refl A02 liftl⟨1⟩ (refl a01)))
                          (sym
                             (refl A12 liftl⟨1⟩ (A11⁽ᵉᵉ⁾ trr⟨1⟩ (refl a11))))
                          (A22⁽¹²ᵉ⁾ (refl A02 liftl⟨1⟩ (refl a01))
                             (sym
                                (A12⁽ᵉ¹⁾
                                   (A12⁽¹ᵉ⁾ (refl A10 liftr a10)
                                      (refl A11 liftr a11) trr a12)
                                   (A12 liftl (refl A11 trr a11)) liftl
                                   (A11⁽ᵉᵉ⁾ trr⟨1⟩ (refl a11))))
                             (A20⁽¹ᵉ⁾ (refl A02 trl⟨1⟩ (refl a01))
                                (A12⁽ᵉ¹⁾
                                   (A12⁽¹ᵉ⁾ (refl A10 liftr a10)
                                      (refl A11 liftr a11) trr a12)
                                   (A12 liftl (refl A11 trr a11)) trl
                                   (A11⁽ᵉᵉ⁾ trr⟨1⟩ (refl a11))) liftr
                                (A20⁽¹ᵉ⁾
                                   (A02⁽ᵉ¹⁾ a02 (A02 liftl a01) trl
                                      (refl a01)) (refl A10 liftr a10) trr
                                   a20))
                             (A21⁽¹ᵉ⁾ (refl a01)
                                (A11⁽ᵉᵉ⁾ trr⟨1⟩ (refl a11)) liftr
                                (A21⁽¹ᵉ⁾ (refl a01) (refl A11 liftr a11)
                                   trr a21)) trr
                             (A22⁽¹²ᵉ⁾
                                (sym
                                   (A02⁽ᵉ¹⁾ a02 (A02 liftl a01) liftl
                                      (refl a01)))
                                (A12⁽¹ᵉ⁾ (refl A10 liftr a10)
                                   (refl A11 liftr a11) liftr a12)
                                (A20⁽¹ᵉ⁾
                                   (A02⁽ᵉ¹⁾ a02 (A02 liftl a01) trl
                                      (refl a01)) (refl A10 liftr a10)
                                   liftr a20)
                                (A21⁽¹ᵉ⁾ (refl a01) (refl A11 liftr a11)
                                   liftr a21) trr a22))
                          (A22 (A02 liftl a01)
                             (A12 liftl (refl A11 trr a11)) liftl
                             (A21⁽¹ᵉ⁾ (refl a01)
                                (A11⁽ᵉᵉ⁾ trr⟨1⟩ (refl a11)) trr
                                (A21⁽¹ᵉ⁾ (refl a01) (refl A11 liftr a11)
                                   trr a21))) trl
                          (A21⁽¹ᵉᵉ⁾ a01⁽ᵉᵉ⁾ (A11⁽ᵉᵉᵉ⁾ trr⟨1⟩ a11⁽ᵉᵉ⁾)
                             trr⟨1⟩
                             (A21⁽¹ᵉᵉ⁾ a01⁽ᵉᵉ⁾
                                (A11⁽ᵉᵉ⁾ liftr⟨1⟩ (refl a11)) trr⟨1⟩
                                (refl a21)))))
                    (B22⁽¹²ᵉ⁾
                       (A22⁽¹ᵉ⁾ (refl A02 liftl⟨1⟩ (refl a01))
                          (refl A12 liftl⟨1⟩ (A11⁽ᵉᵉ⁾ trr⟨1⟩ (refl a11)))
                          liftl⟨1⟩
                          (A21⁽¹ᵉᵉ⁾ a01⁽ᵉᵉ⁾ (A11⁽ᵉᵉᵉ⁾ trr⟨1⟩ a11⁽ᵉᵉ⁾)
                             trr⟨1⟩
                             (A21⁽¹ᵉᵉ⁾ a01⁽ᵉᵉ⁾
                                (A11⁽ᵉᵉ⁾ liftr⟨1⟩ (refl a11)) trr⟨1⟩
                                (refl a21))))
                       (f02⁽¹ᵉ⁾ (refl A02 liftl⟨1⟩ (refl a01)))
                       (f12⁽¹ᵉ⁾
                          (refl A12 liftl⟨1⟩ (A11⁽ᵉᵉ⁾ trr⟨1⟩ (refl a11))))
                       trr⟨1⟩
                       (refl f20
                          (A22⁽¹ᵉ⁾ (refl A02 liftl⟨1⟩ (refl a01))
                             (refl A12 liftl⟨1⟩ (A11⁽ᵉᵉ⁾ trr⟨1⟩ (refl a11)))
                             trl⟨1⟩
                             (A21⁽¹ᵉᵉ⁾ a01⁽ᵉᵉ⁾ (A11⁽ᵉᵉᵉ⁾ trr⟨1⟩ a11⁽ᵉᵉ⁾)
                                trr⟨1⟩
                                (A21⁽¹ᵉᵉ⁾ a01⁽ᵉᵉ⁾
                                   (A11⁽ᵉᵉ⁾ liftr⟨1⟩ (refl a11)) trr⟨1⟩
                                   (refl a21)))))) trl
                    (B22
                       (A22 (A02 liftl a01) (A12 liftl (refl A11 trr a11))
                          liftl
                          (A21⁽¹ᵉ⁾ (refl a01) (A11⁽ᵉᵉ⁾ trr⟨1⟩ (refl a11))
                             trr
                             (A21⁽¹ᵉ⁾ (refl a01) (refl A11 liftr a11) trr
                                a21))) (f02 (A02 liftl a01))
                       (f12 (A12 liftl (refl A11 trr a11))) liftr
                       (f20
                          (A22 (A02 liftl a01)
                             (A12 liftl (refl A11 trr a11)) trl
                             (A21⁽¹ᵉ⁾ (refl a01)
                                (A11⁽ᵉᵉ⁾ trr⟨1⟩ (refl a11)) trr
                                (A21⁽¹ᵉ⁾ (refl a01) (refl A11 liftr a11)
                                   trr a21))))))))

Πliftr = refl _

echo ((λ X Y → (x : X) → Y x) : ((X : Set) (Y : X → Set) → Set))⁽ᵉᵉ⁾ A22
       B22 f02 f12 liftl f21 a22

Πliftl : Id
           (B22 a22 (f02 a02) (f12 a12)
              (B22 (A22 (A02 liftr a00) (A12 liftr a10) liftr a20)
                 (f02 (A02 liftr a00)) (f12 (A12 liftr a10)) trl
                 (f21 (A22 (A02 liftr a00) (A12 liftr a10) trr a20)))
              (f21 a21))
           (((λ X Y → (x : X) → Y x) : ((X : Set) (Y : X → Set) → Set))⁽ᵉᵉ⁾
              A22 B22 f02 f12 liftl f21 a22)
           (B22⁽¹²ᵉ⁾
              (A22⁽¹²ᵉ⁾
                 (sym (A02⁽ᵉ¹⁾ a02 (A02 liftr a00) liftr (refl a00)))
                 (A12⁽¹ᵉ⁾ (refl A10 liftr a10) (refl A11 liftr a11) liftr
                    a12)
                 (A20⁽¹ᵉ⁾ (refl a00) (refl A10 liftr a10) liftr a20)
                 (A21⁽¹ᵉ⁾ (A02⁽ᵉ¹⁾ a02 (A02 liftr a00) trr (refl a00))
                    (refl A11 liftr a11) liftr a21) liftr a22)
              (f02⁽¹ᵉ⁾ (sym (A02⁽ᵉ¹⁾ a02 (A02 liftr a00) liftr (refl a00))))
              (f12⁽¹ᵉ⁾
                 (A12⁽¹ᵉ⁾ (refl A10 liftr a10) (refl A11 liftr a11) liftr
                    a12))
              (B22⁽¹²ᵉ⁾
                 (A22⁽¹²ᵉ⁾ (A02⁽¹ᵉ⁾ liftr⟨1⟩ (refl a00))
                    (A12⁽¹ᵉ⁾ liftr⟨1⟩ (refl A10 liftr a10)) liftr⟨1⟩
                    (A20⁽¹ᵉ⁾ (refl a00) (refl A10 liftr a10) liftr a20))
                 (f02⁽¹ᵉ⁾ (A02⁽¹ᵉ⁾ liftr⟨1⟩ (refl a00)))
                 (f12⁽¹ᵉ⁾ (A12⁽¹ᵉ⁾ liftr⟨1⟩ (refl A10 liftr a10))) trl⟨1⟩
                 (refl f21
                    (A22⁽¹²ᵉ⁾ (A02⁽¹ᵉ⁾ liftr⟨1⟩ (refl a00))
                       (A12⁽¹ᵉ⁾ liftr⟨1⟩ (refl A10 liftr a10)) trr⟨1⟩
                       (A20⁽¹ᵉ⁾ (refl a00) (refl A10 liftr a10) liftr a20))))
              (refl f21
                 (A21⁽¹ᵉ⁾ (A02⁽ᵉ¹⁾ a02 (A02 liftr a00) trr (refl a00))
                    (refl A11 liftr a11) liftr a21)) trl
              (B22⁽¹²ᵉ⁾
                 (A22⁽¹²ᵉ⁾ (refl A02 liftr⟨1⟩ (refl a00))
                    (sym
                       (A12⁽ᵉ¹⁾
                          (A12⁽¹ᵉ⁾ (refl A10 liftr a10)
                             (refl A11 liftr a11) trr a12)
                          (A12 liftr (refl A10 trr a10)) liftr
                          (A10⁽ᵉᵉ⁾ trr⟨1⟩ (refl a10))))
                    (A20⁽¹ᵉ⁾ (refl a00) (A10⁽ᵉᵉ⁾ trr⟨1⟩ (refl a10)) liftr
                       (A20⁽¹ᵉ⁾ (refl a00) (refl A10 liftr a10) trr a20))
                    (A21⁽¹ᵉ⁾ (refl A02 trr⟨1⟩ (refl a00))
                       (A12⁽ᵉ¹⁾
                          (A12⁽¹ᵉ⁾ (refl A10 liftr a10)
                             (refl A11 liftr a11) trr a12)
                          (A12 liftr (refl A10 trr a10)) trr
                          (A10⁽ᵉᵉ⁾ trr⟨1⟩ (refl a10))) liftr
                       (A21⁽¹ᵉ⁾
                          (A02⁽ᵉ¹⁾ a02 (A02 liftr a00) trr (refl a00))
                          (refl A11 liftr a11) trr a21)) liftr
                    (A22⁽¹²ᵉ⁾
                       (sym (A02⁽ᵉ¹⁾ a02 (A02 liftr a00) liftr (refl a00)))
                       (A12⁽¹ᵉ⁾ (refl A10 liftr a10) (refl A11 liftr a11)
                          liftr a12)
                       (A20⁽¹ᵉ⁾ (refl a00) (refl A10 liftr a10) liftr a20)
                       (A21⁽¹ᵉ⁾
                          (A02⁽ᵉ¹⁾ a02 (A02 liftr a00) trr (refl a00))
                          (refl A11 liftr a11) liftr a21) trr a22))
                 (f02⁽¹ᵉ⁾ (refl A02 liftr⟨1⟩ (refl a00)))
                 (f12⁽¹ᵉ⁾
                    (sym
                       (A12⁽ᵉ¹⁾
                          (A12⁽¹ᵉ⁾ (refl A10 liftr a10)
                             (refl A11 liftr a11) trr a12)
                          (A12 liftr (refl A10 trr a10)) liftr
                          (A10⁽ᵉᵉ⁾ trr⟨1⟩ (refl a10)))))
                 (B22⁽¹²ᵉ⁾
                    (A22⁽¹²ᵉ⁾ (refl A02 liftr⟨1⟩ (refl a00))
                       (A12⁽¹ᵉ⁾ liftr⟨1⟩ (A10⁽ᵉᵉ⁾ trr⟨1⟩ (refl a10)))
                       liftr⟨1⟩
                       (A20⁽¹ᵉ⁾ (refl a00) (A10⁽ᵉᵉ⁾ trr⟨1⟩ (refl a10))
                          liftr
                          (A20⁽¹ᵉ⁾ (refl a00) (refl A10 liftr a10) trr a20)))
                    (f02⁽¹ᵉ⁾ (refl A02 liftr⟨1⟩ (refl a00)))
                    (f12⁽¹ᵉ⁾ (A12⁽¹ᵉ⁾ liftr⟨1⟩ (A10⁽ᵉᵉ⁾ trr⟨1⟩ (refl a10))))
                    trl⟨1⟩
                    (refl f21
                       (A22⁽¹²ᵉ⁾ (refl A02 liftr⟨1⟩ (refl a00))
                          (A12⁽¹ᵉ⁾ liftr⟨1⟩ (A10⁽ᵉᵉ⁾ trr⟨1⟩ (refl a10)))
                          trr⟨1⟩
                          (A20⁽¹ᵉ⁾ (refl a00) (A10⁽ᵉᵉ⁾ trr⟨1⟩ (refl a10))
                             liftr
                             (A20⁽¹ᵉ⁾ (refl a00) (refl A10 liftr a10) trr
                                a20)))))
                 (refl f21
                    (A21⁽¹ᵉ⁾ (refl A02 trr⟨1⟩ (refl a00))
                       (A12⁽ᵉ¹⁾
                          (A12⁽¹ᵉ⁾ (refl A10 liftr a10)
                             (refl A11 liftr a11) trr a12)
                          (A12 liftr (refl A10 trr a10)) trr
                          (A10⁽ᵉᵉ⁾ trr⟨1⟩ (refl a10))) liftr
                       (A21⁽¹ᵉ⁾
                          (A02⁽ᵉ¹⁾ a02 (A02 liftr a00) trr (refl a00))
                          (refl A11 liftr a11) trr a21))) trl
                 (B22⁽¹²ᵉ⁾
                    (sym
                       (A22⁽ᵉ¹⁾ (sym (refl A02 liftr⟨1⟩ (refl a00)))
                          (sym
                             (refl A12 liftr⟨1⟩ (A10⁽ᵉᵉ⁾ trr⟨1⟩ (refl a10))))
                          (A22⁽¹²ᵉ⁾ (refl A02 liftr⟨1⟩ (refl a00))
                             (sym
                                (A12⁽ᵉ¹⁾
                                   (A12⁽¹ᵉ⁾ (refl A10 liftr a10)
                                      (refl A11 liftr a11) trr a12)
                                   (A12 liftr (refl A10 trr a10)) liftr
                                   (A10⁽ᵉᵉ⁾ trr⟨1⟩ (refl a10))))
                             (A20⁽¹ᵉ⁾ (refl a00)
                                (A10⁽ᵉᵉ⁾ trr⟨1⟩ (refl a10)) liftr
                                (A20⁽¹ᵉ⁾ (refl a00) (refl A10 liftr a10)
                                   trr a20))
                             (A21⁽¹ᵉ⁾ (refl A02 trr⟨1⟩ (refl a00))
                                (A12⁽ᵉ¹⁾
                                   (A12⁽¹ᵉ⁾ (refl A10 liftr a10)
                                      (refl A11 liftr a11) trr a12)
                                   (A12 liftr (refl A10 trr a10)) trr
                                   (A10⁽ᵉᵉ⁾ trr⟨1⟩ (refl a10))) liftr
                                (A21⁽¹ᵉ⁾
                                   (A02⁽ᵉ¹⁾ a02 (A02 liftr a00) trr
                                      (refl a00)) (refl A11 liftr a11) trr
                                   a21)) trr
                             (A22⁽¹²ᵉ⁾
                                (sym
                                   (A02⁽ᵉ¹⁾ a02 (A02 liftr a00) liftr
                                      (refl a00)))
                                (A12⁽¹ᵉ⁾ (refl A10 liftr a10)
                                   (refl A11 liftr a11) liftr a12)
                                (A20⁽¹ᵉ⁾ (refl a00) (refl A10 liftr a10)
                                   liftr a20)
                                (A21⁽¹ᵉ⁾
                                   (A02⁽ᵉ¹⁾ a02 (A02 liftr a00) trr
                                      (refl a00)) (refl A11 liftr a11)
                                   liftr a21) trr a22))
                          (A22 (A02 liftr a00)
                             (A12 liftr (refl A10 trr a10)) liftr
                             (A20⁽¹ᵉ⁾ (refl a00)
                                (A10⁽ᵉᵉ⁾ trr⟨1⟩ (refl a10)) trr
                                (A20⁽¹ᵉ⁾ (refl a00) (refl A10 liftr a10)
                                   trr a20))) liftr
                          (A20⁽¹ᵉᵉ⁾ a00⁽ᵉᵉ⁾ (A10⁽ᵉᵉᵉ⁾ trr⟨1⟩ a10⁽ᵉᵉ⁾)
                             trr⟨1⟩
                             (A20⁽¹ᵉᵉ⁾ a00⁽ᵉᵉ⁾
                                (A10⁽ᵉᵉ⁾ liftr⟨1⟩ (refl a10)) trr⟨1⟩
                                (refl a20)))))
                    (f02⁽¹ᵉ⁾ (refl A02 liftr⟨1⟩ (refl a00)))
                    (f12⁽¹ᵉ⁾
                       (refl A12 liftr⟨1⟩ (A10⁽ᵉᵉ⁾ trr⟨1⟩ (refl a10))))
                    (B22⁽¹²ᵉ⁾
                       (A22⁽¹ᵉ⁾ (refl A02 liftr⟨1⟩ (refl a00))
                          (refl A12 liftr⟨1⟩ (A10⁽ᵉᵉ⁾ trr⟨1⟩ (refl a10)))
                          liftr⟨1⟩
                          (A20⁽¹ᵉᵉ⁾ a00⁽ᵉᵉ⁾ (A10⁽ᵉᵉᵉ⁾ trr⟨1⟩ a10⁽ᵉᵉ⁾)
                             trr⟨1⟩
                             (A20⁽¹ᵉᵉ⁾ a00⁽ᵉᵉ⁾
                                (A10⁽ᵉᵉ⁾ liftr⟨1⟩ (refl a10)) trr⟨1⟩
                                (refl a20))))
                       (f02⁽¹ᵉ⁾ (refl A02 liftr⟨1⟩ (refl a00)))
                       (f12⁽¹ᵉ⁾
                          (refl A12 liftr⟨1⟩ (A10⁽ᵉᵉ⁾ trr⟨1⟩ (refl a10))))
                       trl⟨1⟩
                       (refl f21
                          (A22⁽¹ᵉ⁾ (refl A02 liftr⟨1⟩ (refl a00))
                             (refl A12 liftr⟨1⟩ (A10⁽ᵉᵉ⁾ trr⟨1⟩ (refl a10)))
                             trr⟨1⟩
                             (A20⁽¹ᵉᵉ⁾ a00⁽ᵉᵉ⁾ (A10⁽ᵉᵉᵉ⁾ trr⟨1⟩ a10⁽ᵉᵉ⁾)
                                trr⟨1⟩
                                (A20⁽¹ᵉᵉ⁾ a00⁽ᵉᵉ⁾
                                   (A10⁽ᵉᵉ⁾ liftr⟨1⟩ (refl a10)) trr⟨1⟩
                                   (refl a20))))))
                    (refl f21
                       (A22⁽ᵉ¹⁾ (sym (refl A02 liftr⟨1⟩ (refl a00)))
                          (sym
                             (refl A12 liftr⟨1⟩ (A10⁽ᵉᵉ⁾ trr⟨1⟩ (refl a10))))
                          (A22⁽¹²ᵉ⁾ (refl A02 liftr⟨1⟩ (refl a00))
                             (sym
                                (A12⁽ᵉ¹⁾
                                   (A12⁽¹ᵉ⁾ (refl A10 liftr a10)
                                      (refl A11 liftr a11) trr a12)
                                   (A12 liftr (refl A10 trr a10)) liftr
                                   (A10⁽ᵉᵉ⁾ trr⟨1⟩ (refl a10))))
                             (A20⁽¹ᵉ⁾ (refl a00)
                                (A10⁽ᵉᵉ⁾ trr⟨1⟩ (refl a10)) liftr
                                (A20⁽¹ᵉ⁾ (refl a00) (refl A10 liftr a10)
                                   trr a20))
                             (A21⁽¹ᵉ⁾ (refl A02 trr⟨1⟩ (refl a00))
                                (A12⁽ᵉ¹⁾
                                   (A12⁽¹ᵉ⁾ (refl A10 liftr a10)
                                      (refl A11 liftr a11) trr a12)
                                   (A12 liftr (refl A10 trr a10)) trr
                                   (A10⁽ᵉᵉ⁾ trr⟨1⟩ (refl a10))) liftr
                                (A21⁽¹ᵉ⁾
                                   (A02⁽ᵉ¹⁾ a02 (A02 liftr a00) trr
                                      (refl a00)) (refl A11 liftr a11) trr
                                   a21)) trr
                             (A22⁽¹²ᵉ⁾
                                (sym
                                   (A02⁽ᵉ¹⁾ a02 (A02 liftr a00) liftr
                                      (refl a00)))
                                (A12⁽¹ᵉ⁾ (refl A10 liftr a10)
                                   (refl A11 liftr a11) liftr a12)
                                (A20⁽¹ᵉ⁾ (refl a00) (refl A10 liftr a10)
                                   liftr a20)
                                (A21⁽¹ᵉ⁾
                                   (A02⁽ᵉ¹⁾ a02 (A02 liftr a00) trr
                                      (refl a00)) (refl A11 liftr a11)
                                   liftr a21) trr a22))
                          (A22 (A02 liftr a00)
                             (A12 liftr (refl A10 trr a10)) liftr
                             (A20⁽¹ᵉ⁾ (refl a00)
                                (A10⁽ᵉᵉ⁾ trr⟨1⟩ (refl a10)) trr
                                (A20⁽¹ᵉ⁾ (refl a00) (refl A10 liftr a10)
                                   trr a20))) trr
                          (A20⁽¹ᵉᵉ⁾ a00⁽ᵉᵉ⁾ (A10⁽ᵉᵉᵉ⁾ trr⟨1⟩ a10⁽ᵉᵉ⁾)
                             trr⟨1⟩
                             (A20⁽¹ᵉᵉ⁾ a00⁽ᵉᵉ⁾
                                (A10⁽ᵉᵉ⁾ liftr⟨1⟩ (refl a10)) trr⟨1⟩
                                (refl a20))))) trl
                    (B22
                       (A22 (A02 liftr a00) (A12 liftr (refl A10 trr a10))
                          liftr
                          (A20⁽¹ᵉ⁾ (refl a00) (A10⁽ᵉᵉ⁾ trr⟨1⟩ (refl a10))
                             trr
                             (A20⁽¹ᵉ⁾ (refl a00) (refl A10 liftr a10) trr
                                a20))) (f02 (A02 liftr a00))
                       (f12 (A12 liftr (refl A10 trr a10))) liftl
                       (f21
                          (A22 (A02 liftr a00)
                             (A12 liftr (refl A10 trr a10)) trr
                             (A20⁽¹ᵉ⁾ (refl a00)
                                (A10⁽ᵉᵉ⁾ trr⟨1⟩ (refl a10)) trr
                                (A20⁽¹ᵉ⁾ (refl a00) (refl A10 liftr a10)
                                   trr a20))))))))

Πliftl = refl _
