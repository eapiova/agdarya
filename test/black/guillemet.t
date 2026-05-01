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
  

  $ agdarya -v -e "module foo where { bar : Set; bar = sig () }" -e "open foo" -e "x : bar" -e "x = ()"
   ￫ info[I0000]
   ￮ constant bar defined
  
   ￫ info[I0000]
   ￮ constant x defined
  

  $ agdarya -v -e "module «foo def x : bar» where { x : Set; x = sig () }" -e "open «foo def x : bar»" -e "y : x" -e "y = ()"
   ￫ info[I0000]
   ￮ constant x defined
  
   ￫ info[I0000]
   ￮ constant y defined
  

  $ agdarya -v -e "module «foo def x : bar» where { x : Set; x = sig () }" -e "open «foo def x : bar"
   ￫ info[I0000]
   ￮ constant x defined
  
   ￫ error[E0200]
   ￭ command-line exec string
   1 | open «foo def x : bar‹EOF›
     ^ parse error
  
  [1]

  $ agdarya -v -e "module foo where { «a long name» : Set; «a long name» = sig () }" -e "open foo" -e "« » : «a long name»" -e "« » = ()"
   ￫ info[I0000]
   ￮ constant «a long name» defined
  
   ￫ info[I0000]
   ￮ constant « » defined
  

  $ agdarya -v -e "module foo where { «contains \` comments» : Set; «contains \` comments» = sig () }" -e "open foo" -e "«{\`» : «contains \` comments»" -e "«{\`» = ()"
   ￫ info[I0000]
   ￮ constant «contains ` comments» defined
  
   ￫ info[I0000]
   ￮ constant «{`» defined
  

  $ agdarya -v -e "module foo where { «contains \" quotes» : Set; «contains \" quotes» = sig () }" -e "open foo" -e "«\"» : «contains \" quotes»" -e "«\"» = ()"
   ￫ info[I0000]
   ￮ constant «contains " quotes» defined
  
   ￫ info[I0000]
   ￮ constant «"» defined
  
