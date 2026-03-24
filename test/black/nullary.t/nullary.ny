{- -*- agdarya-prog-args: ("-proofgeneral" "-parametric" "-arity" "0" "-direction" "w,wk") -*- -}

postulate A : Set
echo wk A
echo A⁽ʷ⁾
echo wk (wk A)

postulate a : A
echo wk a
echo wk (wk a)

postulate a' : wk A .
echo a'
echo wk a'
echo sym (wk a')

postulate a'' : A⁽ʷʷ⁾ . .
echo a''
echo sym a''
echo wk a''
echo sym (wk a'')

postulate B : Set⁽ʷ⁾ .
postulate b : B .
echo b
echo wk b
echo sym (wk b)

postulate C : Set⁽ʷʷ⁾ . .
postulate c : C . .
echo c
echo sym c
echo wk c
echo sym (wk c)
echo wk (sym c)
