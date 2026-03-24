bool : Set
bool = data [ true | false ]

-- We can define an inductive-recursive universe as well.  Here is the type of it and its recursive eliminator.
uu_el_type : Set
uu_el_type = sig (
  uu : Set,
  el : uu → Set,
)

-- And now here are their definitions.
uu_el : uu_el_type
uu_el = (
  uu ≔ data [
  | bool
  | pi (A : uu_el uu) (B : uu_el el A → uu_el uu)
  ],
  el ≔ λ {
  bool → bool;
  pi A B → (x : uu_el el A) → uu_el el (B x)
  },
)
