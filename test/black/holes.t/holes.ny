 {- -*- agdarya-prog-args: ("-proofgeneral" "-parametric") -*- -}

postulate A : Set

postulate B : Set

echo B

id : Set → Set

id X = X

postulate b : B

postulate g : (A → B) → A → B

f : A → B

f = ?

postulate a_very_long_variable : A

postulate a_very_long_function : A → A → A → A → A → A → A → B

f' : A → B

f' = ? {- Check whether notations that were in scope at the time of a hole are still available when solving the hole even if they're no longer in scope at the current time, while notations defined later are not in scope for the hole. -}

section sec ≔

  notation "&" ≔ b

  f' : A → B

  f' = ?

end

notation "$" ≔ b

ℕ : Set

ℕ = data [ zero : ℕ | suc : ℕ → ℕ ]

plus : (m n : ℕ) → ℕ

plus m n = case n of λ { zero → ?; suc n → ?}

postulate P : ℕ → Set

anop : ℕ → ℕ → (x : ℕ) → P x

anop n n′ n = ? {- The user's "n′" should not be shadowed by an auto-generated one -}

anop' : ℕ → ℕ → (x : ℕ) → P x

anop' n′ n n = ?

anop'' : ℕ → ℕ → (x : ℕ) → P x

anop'' n _ n = ? {- Nor the user's 𝑥 be shadowed by an auto-generated one -}

anop''' : ℕ → ℕ → (x : ℕ) → P x

anop''' 𝑥 _ n = ?

Σ : (A : Set) → (B : A → Set) → Set

Σ A B = sig ( fst : A, snd : B fst ) {- Here the type of the second hole is not the first hole but "pp fst", since the first hole is potential and causes its case tree to be just stuck. -}

pp : Σ Set (X ↦ X)

pp = (?, ?) {- But if we break the case tree, then the type of the second hole is the first hole. -}

pp' : Σ Set (X ↦ X)

pp' = (id ?, ?) {- The out-of-scope variable "𝑥" that appears here is because record types are stored internally like codatatypes with all fields depending on a single variable, so we have to introduce that variable during typechecking. -}

foo : Set

foo
=
  sig (
  bar : ℕ,
{- It's important for ? to be its own token, so that it can be followed immediately by a comma. -}
  baz : ? )

foo' : Set

foo' = sig ( bar : Set, baz : (x : bar) → ? )

gel0 : (A B : Set) → Id Set A B

gel0 A B = sig x y ↦ ( one : ? )

gel1 : (A B : Set) → Id Set A B

gel1 A B = sig x y ↦ ( one : Set, two : ? )

gel2 : (A B : Set) → Id Set A B

gel2 A B = sig x y ↦ ( one : ?, two : ? )

gel3 : (A B : Set) → Id Set A B

gel3 A B = codata [ one x : ? | two x : ? ]

postulate C : A → Set

AC : Set

AC = sig ( a : ℕ → A, c : C (a zero) )

ac : AC

ac = (a ≔ ?, c ≔ ?)

ida : A → A

ida x = x

ideqid : Id (A → A) ida ida

ideqid
=
  ((x ↦ x) : Id (A → A) ida ida → Id (A → A) ida ida) ({u} {u} u ↦ u)

echo ideqid {- TODO: Ideally, the user's "u′" should not be shadowed by an auto-generated one (although this matters a bit less than the one for contexts, since the user won't be using it to enter terms).  (This isn't about holes.) -}

ideqid' : Id (A → A) ida ida

ideqid'
=
  ((x ↦ x) : Id (A → A) ida ida → Id (A → A) ida ida) ({u} {u} u′ ↦ u′)

echo ideqid'

ideqid'' : Id (A → A) ida ida

ideqid''
=
  ((x ↦ x) : Id (A → A) ida ida → Id (A → A) ida ida) ({u} {u} u ↦ ?) {- A kinetic hole -}

afam : Set → Set

afam X = id ? {- This requires comparing a metavariable to equal itself when evaluated in equal environments. -}

idafam : (X : Set) → afam X → afam X

idafam X x = x {- For testing hole splitting -}

postulate f0 : A → B

f2 : Id ((x : A) → B) f0 f0

f2 = x ⤇ ?

prod : Set

prod = sig ( fst : A, snd : B )

p : prod

p = ?

postulate p0 : prod

p2 : Id prod p0 p0

p2 = ?

prod' : Set

prod' = codata [ fst x : A | snd x : B ]

p : prod'

p = ?
