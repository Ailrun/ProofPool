module Logic.First.Signature where

open import Logic.Base

infixr 8 _×ₜ₁_
infixr 7 _→ₜ₁_

data Ty₁ : Set where
  1ₜ₁ : Ty₁
  ℕₜ₁ : Ty₁
  _→ₜ₁_ : Ty₁ → Ty₁ → Ty₁
  _×ₜ₁_ : Ty₁ → Ty₁ → Ty₁

record Signature₁ : Set₁ where
  field
    Func₁ Pred₁ : Set
    fargₜ₁ : Func₁ → Ty₁
    fresₜ₁ : Func₁ → Ty₁
