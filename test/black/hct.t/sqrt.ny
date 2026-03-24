 {- The "amazing right adjoint" can only be defined for closed types. -}

postulate A : Set

√A : Set

√A = codata [ root⟨e⟩ x : A ] {- If we have an equality in √A, we can project out an element of A.  This is the counit of the adjunction Id ⊣ √. -}

postulate s0 : √A

postulate s1 : √A

postulate s2 : Id √A s0 s1

echo s2 root⟨1⟩ {- We can leave off the suffix if it's the identity (1, 12, etc.) -}

echo s2 root {- At higher dimensions, if we have a square in √A, we can project out *two* elements of A, according to the two directions of the square. -}

postulate s00 : √A

postulate s01 : √A

postulate s10 : √A

postulate s11 : √A

postulate s02 : Id √A s00 s01

postulate s12 : Id √A s10 s11

postulate s20 : Id √A s00 s10

postulate s21 : Id √A s01 s11

postulate s22 : √A⁽ᵉᵉ⁾ s02 s12 s20 s21

echo s22 root⟨1⟩

echo s22 root⟨2⟩ {- We can also take the fields of refl s2. -}

echo refl s2 root⟨1⟩

echo refl s2 root⟨2⟩

echo refl (s2 root⟨1⟩) {- Since sym fixes refl-refl, the two fields of refl-refl s0 are the same. -}

echo refl (refl s0) root⟨1⟩

echo refl (refl s0) root⟨2⟩ {- To define an element of √, we specify the value for the higher field in a degenerated context. -}

postulate B : Set

postulate f (y0 y1 : B) (y2 : Id B y0 y1) : A

√f : (b : B) → √A

√f b = record { root⟨e⟩ = f b⟨0⟩ b⟨1⟩ b⟨2⟩ }

postulate b0 : B

postulate b1 : B

postulate b2 : Id B b0 b1 {- When we have this element sufficiently degenerated, we can project out its field(s) and get the value we supplied, applied to the correct arguments. -}

echo refl √f b2 root⟨1⟩ {- And similarly at the next dimension. -}

postulate t00 : B

postulate t01 : B

postulate t10 : B

postulate t11 : B

postulate t02 : Id B t00 t01

postulate t12 : Id B t10 t11

postulate t20 : Id B t00 t10

postulate t21 : Id B t01 t11

postulate t22 : Id (Id B) t02 t12 t20 t21

echo √f⁽ᵉᵉ⁾ t22 root⟨2⟩

echo √f⁽ᵉᵉ⁾ t22 root⟨1⟩ {- We can also see that sym fixes refl-refl on a non-neutral element. -}

postulate a : A

√a : √A

√a = record { root⟨e⟩ = a }

echo refl √a root⟨1⟩

echo refl (refl √a) root⟨1⟩

echo refl (refl √a) root⟨2⟩ {- We can also define elements of degenerate versions of √A, as higher coinductive types in their own right  In this case we have to give a value for the "actual" field that has appeared, as well as the higher field that is now further degenerated. -}

s2' : Id √A (√f b0) (√f b1)

s2' = record { root⟨e⟩ = refl f b2 b2 (sym (refl b2)); root⟨1⟩ = a } {- Only the version that's already fully instantiated can be directly projected out. -}

echo s2' root⟨1⟩ {- The other one only comes into play when we degenerate. -}

echo refl s2' root⟨2⟩

echo refl s2' root⟨1⟩ {- One way to define the unit of the adjunction Id ⊣ √ is to wrap up Id and its endpoints in a sig. -}

ID : (X : Set) → Set

ID X = sig ( x0 : X, x1 : X, x2 : Id X x0 x1 )

√IDA : Set

√IDA = codata [ root⟨e⟩ x : ID A ]

η : (a : A) → √IDA

η a = record { root⟨e⟩ = (a.0, a⟨1⟩, a⟨2⟩) }

postulate a0 : A

postulate a1 : A

postulate a2 : Id A a0 a1 {- The pieces of this are what we put in.  (A triangle identity) -}

echo refl η a2 root⟨1⟩ x0

echo refl η a2 root⟨1⟩ x1

echo refl η a2 root⟨1⟩ x2 {- Higher-dimensional versions -}

postulate u0 : √IDA

postulate u1 : √IDA

postulate u2 : Id √IDA u0 u1

echo u2 root⟨1⟩

u2' : Id √IDA u0 u1

u2' = record { root⟨1⟩ = ?; root⟨e⟩ = ? }

postulate u00 : √IDA

postulate u01 : √IDA

postulate u02 : Id √IDA u00 u01

postulate u10 : √IDA

postulate u11 : √IDA

postulate u12 : Id √IDA u10 u11

postulate u20 : Id √IDA u00 u10

postulate u21 : Id √IDA u01 u11

postulate u22 : Id (Id √IDA) u02 u12 u20 u21

echo u22 root⟨1⟩

echo u22 root⟨2⟩

u22' : Id (Id √IDA) u02 u12 u20 u21

u22' = record { root⟨1⟩ = ?; root⟨2⟩ = ?; root⟨e⟩ = ? }
