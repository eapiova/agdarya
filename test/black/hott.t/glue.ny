postulate A : Set
postulate B : Set
postulate R : A → B → Set
postulate Rb : isBisim A B R

postulate a : A

glue.trr : Id B (glue A B R Rb trr a) (Rb trr a)
glue.trr = refl _

glue.liftr : Id (R a (glue A B R Rb trr a)) (glue A B R Rb liftr a unglue)
      (Rb liftr a)
glue.liftr = refl _

postulate b : B

glue.trl : Id A (glue A B R Rb trl b) (Rb trl b)
glue.trl = refl _

glue.liftl : Id (R (glue A B R Rb trl b) b) (glue A B R Rb liftl b unglue)
      (Rb liftl b)
glue.liftl = refl _
