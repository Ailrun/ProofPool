-- Normal Natural Deduction
module Logic.Zeroth.NND where

open import Logic.Zeroth.Syntax public

infixl 4 _⊢₀ⁿ_
infixl 4 _⊢₀ʳ_

data _⊢₀ⁿ_ : Ctx₀ → P₀ → Set
data _⊢₀ʳ_ : Ctx₀ → P₀ → Set

data _⊢₀ⁿ_ where
  ∧ₚ₀ⁿI  : Γ ⊢₀ⁿ A →
           Γ ⊢₀ⁿ B →
           --------------
           Γ ⊢₀ⁿ A ∧ₚ₀ B

  ∨ₚ₀ⁿI₁ : Γ ⊢₀ⁿ A →
           --------------
           Γ ⊢₀ⁿ A ∨ₚ₀ B

  ∨ₚ₀ⁿI₂ : Γ ⊢₀ⁿ B →
           --------------
           Γ ⊢₀ⁿ A ∨ₚ₀ B

  ∨ₚ₀ⁿE  : Γ ⊢₀ʳ A ∨ₚ₀ B →
           A ∷ Γ ⊢₀ⁿ C →
           B ∷ Γ ⊢₀ⁿ C →
           ---------------
           Γ ⊢₀ⁿ C

  →ₚ₀ⁿI  : A ∷ Γ ⊢₀ⁿ B →
           --------------
           Γ ⊢₀ⁿ A →ₚ₀ B

  neut₀ⁿ : Γ ⊢₀ʳ A →
           ----------
           Γ ⊢₀ⁿ A

data _⊢₀ʳ_ where
  pre₀ʳ  : A ∈ Γ →
           --------
           Γ ⊢₀ʳ A

  ⊥ₚ₀ʳE  : Γ ⊢₀ʳ ⊥ₚ₀ →
           -----------
           Γ ⊢₀ʳ A

  ∧ₚ₀ʳE₁ : Γ ⊢₀ʳ A ∧ₚ₀ B →
           ---------------
           Γ ⊢₀ʳ A

  ∧ₚ₀ʳE₂ : Γ ⊢₀ʳ A ∧ₚ₀ B →
           ---------------
           Γ ⊢₀ʳ B

  →ₚ₀ʳE  : Γ ⊢₀ʳ A →ₚ₀ B →
           Γ ⊢₀ⁿ A →
           ---------------
           Γ ⊢₀ʳ B

size-⊢₀ⁿ : Γ ⊢₀ⁿ A → ℕ
size-⊢₀ʳ : Γ ⊢₀ʳ A → ℕ

size-⊢₀ⁿ (∧ₚ₀ⁿI  ⊢B ⊢C)      = suc (size-⊢₀ⁿ ⊢B + size-⊢₀ⁿ ⊢C)
size-⊢₀ⁿ (∨ₚ₀ⁿI₁ ⊢B)         = suc (size-⊢₀ⁿ ⊢B)
size-⊢₀ⁿ (∨ₚ₀ⁿI₂ ⊢C)         = suc (size-⊢₀ⁿ ⊢C)
size-⊢₀ⁿ (∨ₚ₀ⁿE  ⊢B∨C B⊢ C⊢) = suc (size-⊢₀ʳ ⊢B∨C + size-⊢₀ⁿ B⊢ + size-⊢₀ⁿ C⊢)
size-⊢₀ⁿ (→ₚ₀ⁿI  B⊢C)        = suc (size-⊢₀ⁿ B⊢C)
size-⊢₀ⁿ (neut₀ⁿ ⊢B)         = size-⊢₀ʳ ⊢B

size-⊢₀ʳ (pre₀ʳ  B∈)      = 1
size-⊢₀ʳ (⊥ₚ₀ʳE  ⊢⊥)      = suc (size-⊢₀ʳ ⊢⊥)
size-⊢₀ʳ (∧ₚ₀ʳE₁ ⊢B∧C)    = suc (size-⊢₀ʳ ⊢B∧C)
size-⊢₀ʳ (∧ₚ₀ʳE₂ ⊢B∧C)    = suc (size-⊢₀ʳ ⊢B∧C)
size-⊢₀ʳ (→ₚ₀ʳE  ⊢B→C ⊢B) = suc (size-⊢₀ʳ ⊢B→C + size-⊢₀ⁿ ⊢B)
