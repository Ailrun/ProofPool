module Logic.Zeroth.Syntax where

open import Logic.Base public

infixl 11 ¬ₚ₀_
infixl 10 _∧ₚ₀_
infixl 9 _∨ₚ₀_
infixr 8 _→ₚ₀_

data P₀ : Set where
  ⊥ₚ₀ : P₀
  _∧ₚ₀_ : P₀ → P₀ → P₀
  _∨ₚ₀_ : P₀ → P₀ → P₀
  _→ₚ₀_ : P₀ → P₀ → P₀

¬ₚ₀_ = _→ₚ₀ ⊥ₚ₀

Ctx₀ = List P₀

variable
  Γ Γ′ Γ″ Δ Δ′ Δ″ Ψ Ψ′ Ψ″ : Ctx₀
  A A′ A″ B B′ B″ C C′ C″ D D′ D″ E E′ E″ : P₀

size-P₀ : P₀ → ℕ
size-P₀ ⊥ₚ₀       = 1
size-P₀ (A ∧ₚ₀ B) = suc (size-P₀ A + size-P₀ B)
size-P₀ (A ∨ₚ₀ B) = suc (size-P₀ A + size-P₀ B)
size-P₀ (A →ₚ₀ B) = suc (size-P₀ A + size-P₀ B)
