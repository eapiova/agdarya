{- -*- agdarya-prog-args: ("-proofgeneral" "-parametric" "-arity" "0" "-direction" "w,wk") -*- -}

И : (A : Set) → Set
И A = codata [ subst⟨w⟩ x : A.0 . ]

toИ : (A : Set) → (a : A) → И A
toИ A a = record { subst⟨w⟩ = a⟨0⟩ }

postulate A : Set

postulate a : wk (И A) .

echo a subst

postulate b : wk (wk (И A)) . .

echo b subst⟨1⟩

echo b subst⟨2⟩
