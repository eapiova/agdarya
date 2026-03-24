  $ agdarya -parametric -arity 0 -direction w,wk nullary.ny
  wk A
    : Set⁽ʷ⁾ .
  
  wk A
    : Set⁽ʷ⁾ .
  
  A⁽ʷʷ⁾
    : Set⁽ʷʷ⁾ . .
  
  wk a
    : wk A .
  
  a⁽ʷʷ⁾
    : A⁽ʷʷ⁾ . .
  
  a'
    : wk A .
  
  wk a'
    : A⁽ʷʷ⁾ . .
  
  a'⁽ʷ¹⁾
    : A⁽ʷʷ⁾ . .
  
  a''
    : A⁽ʷʷ⁾ . .
  
  sym a''
    : A⁽ʷʷ⁾ . .
  
  wk a''
    : A⁽ʷʷʷ⁾ . . .
  
  a''⁽ʷ¹⁾
    : A⁽ʷʷʷ⁾ . . .
  
  b
    : B .
  
  wk b
    : B⁽¹ʷ⁾ . .
  
  b⁽ʷ¹⁾
    : B⁽ʷ¹⁾ . .
  
  c
    : C . .
  
  sym c
    : sym C . .
  
  wk c
    : C⁽¹²ʷ⁾ . . .
  
  c⁽ʷ¹⁾
    : C⁽¹ʷ²⁾ . . .
  
  c⁽²¹ʷ⁾
    : C⁽²¹ʷ⁾ . . .
  
  $ agdarya -parametric -arity 0 -direction w,wk functions.ny
  (x : wk A) ⇒ wk B x.0
    : Set⁽ʷ⁾ .
  
  (x₀ : wk A .) →⁽ʷ⁾ wk B x₀ .
    : Set
  
  (x : A⁽ʷʷ⁾) ⇒ B⁽ʷʷ⁾ x.00
    : Set⁽ʷʷ⁾ . .
  
  ((x : A⁽ʷʷ⁾) ⇒ B⁽ʷʷ⁾ x.00) .
    : Set⁽ʷ⁾ .
  
  (x₀₀ : A⁽ʷʷ⁾ . .) →⁽ʷʷ⁾ B⁽ʷʷ⁾ x₀₀ . .
    : Set
  
  wk f
    : (x₀ : wk A .) →⁽ʷ⁾ wk B x₀ .
  
  f⁽ʷʷ⁾
    : (x₀₀ : A⁽ʷʷ⁾ . .) →⁽ʷʷ⁾ B⁽ʷʷ⁾ x₀₀ . .
  

  $ agdarya -parametric -arity 0 -direction w,wk nominal.ny
  a subst
    : wk A .
  
  b subst⟨1⟩
    : A⁽ʷʷ⁾ . .
  
  sym b subst⟨1⟩
    : A⁽ʷʷ⁾ . .
  
