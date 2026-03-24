{- -*- agdarya-prog-args: ("-proofgeneral" "-parametric" "-arity" "0" "-direction" "w,wk") -*- -}

postulate A : Set
postulate B : A → Set

echo wk ((x : A) → B x)
echo wk ((x : A) → B x) .
echo wk (wk ((x : A) → B x))
echo wk (wk ((x : A) → B x)) .
echo wk (wk ((x : A) → B x)) . .

postulate f : (x : A) → B x
echo wk f
echo wk (wk f)
