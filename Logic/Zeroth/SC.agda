-- Sequent Calculus without Cut
module Logic.Zeroth.SC where

open import Logic.Zeroth.Base
open import Logic.Zeroth.Syntax public

infixl 4 _⟶₀₋_

data _⟶₀₋_ : Ctx₀ → P₀ → Set where
  init₀₋ : A ∈ Γ →
           --------
           Γ ⟶₀₋ A

  ⊥ₚ₀₋L  : ⊥ₚ₀ ∈ Γ →
           ----------
           Γ ⟶₀₋ A

  ∧ₚ₀₋R  : Γ ⟶₀₋ A →
           Γ ⟶₀₋ B →
           --------------
           Γ ⟶₀₋ A ∧ₚ₀ B

  ∧ₚ₀₋L₁ : A ∧ₚ₀ B ∈ Γ →
           A ∷ Γ ⟶₀₋ C →
           --------------
           Γ ⟶₀₋ C

  ∧ₚ₀₋L₂ : A ∧ₚ₀ B ∈ Γ →
           B ∷ Γ ⟶₀₋ C →
           --------------
           Γ ⟶₀₋ C

  ∨ₚ₀₋R₁ : Γ ⟶₀₋ A →
           --------------
           Γ ⟶₀₋ A ∨ₚ₀ B

  ∨ₚ₀₋R₂ : Γ ⟶₀₋ B →
           --------------
           Γ ⟶₀₋ A ∨ₚ₀ B

  ∨ₚ₀₋L  : A ∨ₚ₀ B ∈ Γ →
           A ∷ Γ ⟶₀₋ C →
           B ∷ Γ ⟶₀₋ C →
           --------------
           Γ ⟶₀₋ C

  →ₚ₀₋R  : A ∷ Γ ⟶₀₋ B →
           --------------
           Γ ⟶₀₋ A →ₚ₀ B

  →ₚ₀₋L  : A →ₚ₀ B ∈ Γ →
           Γ ⟶₀₋ A →
           B ∷ Γ ⟶₀₋ C →
           --------------
           Γ ⟶₀₋ C

size-⟶₀₋ : Γ ⟶₀₋ A → ℕ
size-⟶₀₋ (init₀₋ B∈)         = 1
size-⟶₀₋ (⊥ₚ₀₋L  ⊥∈)         = 1
size-⟶₀₋ (∧ₚ₀₋R  ⟶B ⟶C)      = suc (size-⟶₀₋ ⟶B + size-⟶₀₋ ⟶C)
size-⟶₀₋ (∧ₚ₀₋L₁ B∧C∈ B⟶)    = suc (size-⟶₀₋ B⟶)
size-⟶₀₋ (∧ₚ₀₋L₂ B∧C∈ C⟶)    = suc (size-⟶₀₋ C⟶)
size-⟶₀₋ (∨ₚ₀₋R₁ ⟶B)         = suc (size-⟶₀₋ ⟶B)
size-⟶₀₋ (∨ₚ₀₋R₂ ⟶C)         = suc (size-⟶₀₋ ⟶C)
size-⟶₀₋ (∨ₚ₀₋L  B∨C∈ B⟶ C⟶) = suc (size-⟶₀₋ B⟶ + size-⟶₀₋ C⟶)
size-⟶₀₋ (→ₚ₀₋R  B⟶C)        = suc (size-⟶₀₋ B⟶C)
size-⟶₀₋ (→ₚ₀₋L  B→C∈ ⟶B C⟶) = suc (size-⟶₀₋ ⟶B + size-⟶₀₋ C⟶)
