-- Natural Deduction
module Logic.Zeroth.ND where

open import Logic.Zeroth.Base
open import Logic.Zeroth.Syntax public

infixl 4 _⊢₀_

data _⊢₀_ : Ctx₀ → P₀ → Set where
  pre₀  : A ∈ Γ →
          --------
          Γ ⊢₀ A

  ⊥ₚ₀E  : Γ ⊢₀ ⊥ₚ₀ →
          -----------
          Γ ⊢₀ A

  ∧ₚ₀I  : Γ ⊢₀ A →
          Γ ⊢₀ B →
          -------------
          Γ ⊢₀ A ∧ₚ₀ B

  ∧ₚ₀E₁ : Γ ⊢₀ A ∧ₚ₀ B →
          ---------------
          Γ ⊢₀ A

  ∧ₚ₀E₂ : Γ ⊢₀ A ∧ₚ₀ B →
          ---------------
          Γ ⊢₀ B

  ∨ₚ₀I₁ : Γ ⊢₀ A →
          -------------
          Γ ⊢₀ A ∨ₚ₀ B

  ∨ₚ₀I₂ : Γ ⊢₀ B →
          -------------
          Γ ⊢₀ A ∨ₚ₀ B

  ∨ₚ₀E  : Γ ⊢₀ A ∨ₚ₀ B →
          A ∷ Γ ⊢₀ C →
          B ∷ Γ ⊢₀ C →
          ---------------
          Γ ⊢₀ C

  →ₚ₀I  : A ∷ Γ ⊢₀ B →
          -------------
          Γ ⊢₀ A →ₚ₀ B

  →ₚ₀E  : Γ ⊢₀ A →ₚ₀ B →
          Γ ⊢₀ A →
          ---------------
          Γ ⊢₀ B

size-⊢₀ : Γ ⊢₀ A → ℕ
size-⊢₀ (pre₀  B∈)         = 1
size-⊢₀ (⊥ₚ₀E  ⊢⊥)         = suc (size-⊢₀ ⊢⊥)
size-⊢₀ (∧ₚ₀I  ⊢B ⊢C)      = suc (size-⊢₀ ⊢B + size-⊢₀ ⊢C)
size-⊢₀ (∧ₚ₀E₁ ⊢B∧C)       = suc (size-⊢₀ ⊢B∧C)
size-⊢₀ (∧ₚ₀E₂ ⊢B∧C)       = suc (size-⊢₀ ⊢B∧C)
size-⊢₀ (∨ₚ₀I₁ ⊢B)         = suc (size-⊢₀ ⊢B)
size-⊢₀ (∨ₚ₀I₂ ⊢C)         = suc (size-⊢₀ ⊢C)
size-⊢₀ (∨ₚ₀E  ⊢B∨C B⊢ C⊢) = suc (size-⊢₀ ⊢B∨C + size-⊢₀ B⊢ + size-⊢₀ C⊢)
size-⊢₀ (→ₚ₀I  B⊢C)        = suc (size-⊢₀ B⊢C)
size-⊢₀ (→ₚ₀E  ⊢B→C ⊢B)    = suc (size-⊢₀ ⊢B→C + size-⊢₀ ⊢B)
