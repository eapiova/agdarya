  $ agdarya -v -e "«a long name» : Set" -e "«a long name» = sig ()" -e "« » : «a long name»" -e "« » = ()"
   ￫ info[I0000]
   ￮ constant «a long name» defined
  
   ￫ info[I0000]
   ￮ constant « » defined
  

  $ agdarya -v -e "«nested «guillemets» here» : Set" -e "«nested «guillemets» here» = sig ()" -e "«a + b» : «nested «guillemets» here»" -e "«a + b» = ()"
   ￫ info[I0000]
   ￮ constant «nested «guillemets» here» defined
  
   ￫ info[I0000]
   ￮ constant «a + b» defined
  

  $ agdarya -v -e "«foo.bar» : Set" -e "«foo.bar» = sig ()" -e "import foo" -e "x : bar" -e "x = ()"
   ￫ info[I0000]
   ￮ constant «foo.bar» defined
  
   ￫ error[E0300]
   ￭ command-line exec string
   1 | x : bar
     ^ unbound variable: bar
  
  [1]

  $ agdarya -v -e "«foo.bar» : Set" -e "«foo.bar» = sig ()" -e "import «foo def x : bar»" -e "x = ()"
   ￫ info[I0000]
   ￮ constant «foo.bar» defined
  
   ￫ error[E0400]
   ￮ non-synthesizing term in synthesizing position (body of def without specified type)
  
  [1]

  $ agdarya -v -e "«foo.bar» : Set" -e "«foo.bar» = sig ()" -e "import «foo def x : bar := ()"
   ￫ info[I0000]
   ￮ constant «foo.bar» defined
  
   ￫ error[E0200]
   ￭ command-line exec string
   1 | import «foo def x : bar := ()‹EOF›
     ^ parse error
  
  [1]

  $ agdarya -v -e "foo.«a long name» : Set" -e "foo.«a long name» = sig ()" -e "import foo" -e "« » : «a long name»" -e "« » = ()"
   ￫ info[I0000]
   ￮ constant foo.«a long name» defined
  
   ￫ info[I0000]
   ￮ constant « » defined
  

  $ agdarya -v -e "«contains \` comments» : Set" -e "«contains \` comments» = sig ()" -e "import foo" -e "«{\`» : «contains \` comments»" -e "«{\`» = ()"
   ￫ info[I0000]
   ￮ constant «contains ` comments» defined
  
   ￫ info[I0000]
   ￮ constant «{`» defined
  

  $ agdarya -v -e "«contains \" quotes» : Set" -e "«contains \" quotes» = sig ()" -e "import foo" -e "«\"» : «contains \" quotes»" -e "«\"» = ()"
   ￫ info[I0000]
   ￮ constant «contains " quotes» defined
  
   ￫ info[I0000]
   ￮ constant «"» defined
  
