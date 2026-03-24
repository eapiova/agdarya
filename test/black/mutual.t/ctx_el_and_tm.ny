

ctx : Set

ctx = data [ empty | ext (Γ : ctx) (A : ty Γ) ]

ty : (Γ : ctx) → Set

ty Γ
=
  data [
| base
| pi (A : ty Γ) (B : ty (ext Γ A))
| uu
| el (X : tm Γ uu)
| sub (A : ty Γ) (B : ty (ext Γ A)) (a : tm Γ A) ]

tm : (Γ : ctx) → ty Γ → Set

tm Γ
=
  data [
| codebase : tm Γ uu
| lam (A : ty Γ) (B : ty (ext Γ A)) (b : tm (ext Γ A) B) : tm Γ (pi A B)
| app (A : ty Γ) (B : ty (ext Γ A)) (f : tm Γ (pi A B)) (a : tm Γ A)
  : tm Γ (sub A B a) ]
