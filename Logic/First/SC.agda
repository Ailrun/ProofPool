-- Sequent Calculus without Cut
open import Logic.First.Signature

module Logic.First.SC (Sig : Signature₁) where

open import Logic.First.Syntax (Sig) public

infixl 4 _⟶₁₋_

data _⟶₁₋_ : Ctx₁ → P₁ → Set where
  init₁₋ : A ∈ Γ →
           --------
           Γ ⟶₁₋ A

  ⊥ₚ₁₋L  : ⊥ₚ₁ ∈ Γ →
           ----------
           Γ ⟶₁₋ A

  ∧ₚ₁₋R  : Γ ⟶₁₋ A →
           Γ ⟶₁₋ B →
           --------------
           Γ ⟶₁₋ A ∧ₚ₁ B

  ∧ₚ₁₋L₁ : A ∧ₚ₁ B ∈ Γ →
           A ∷ Γ ⟶₁₋ C →
           --------------
           Γ ⟶₁₋ C

  ∧ₚ₁₋L₂ : A ∧ₚ₁ B ∈ Γ →
           B ∷ Γ ⟶₁₋ C →
           --------------
           Γ ⟶₁₋ C

  ∨ₚ₁₋R₁ : Γ ⟶₁₋ A →
           --------------
           Γ ⟶₁₋ A ∨ₚ₁ B

  ∨ₚ₁₋R₂ : Γ ⟶₁₋ B →
           --------------
           Γ ⟶₁₋ A ∨ₚ₁ B

  ∨ₚ₁₋L  : A ∨ₚ₁ B ∈ Γ →
           A ∷ Γ ⟶₁₋ C →
           B ∷ Γ ⟶₁₋ C →
           --------------
           Γ ⟶₁₋ C

  →ₚ₁₋R  : A ∷ Γ ⟶₁₋ B →
           --------------
           Γ ⟶₁₋ A →ₚ₁ B

  →ₚ₁₋L  : A →ₚ₁ B ∈ Γ →
           Γ ⟶₁₋ A →
           B ∷ Γ ⟶₁₋ C →
           --------------
           Γ ⟶₁₋ C

  →ₚ₁₋R  : A ∷ Γ ⟶₁₋ B →
           --------------
           Γ ⟶₁₋ A →ₚ₁ B

  →ₚ₁₋L  : A →ₚ₁ B ∈ Γ →
           Γ ⟶₁₋ A →
           B ∷ Γ ⟶₁₋ C →
           --------------
           Γ ⟶₁₋ C

size-⟶₁₋ : Γ ⟶₁₋ A → ℕ
size-⟶₁₋ (init₁₋ B∈)         = 1
size-⟶₁₋ (⊥ₚ₁₋L  ⊥∈)         = 1
size-⟶₁₋ (∧ₚ₁₋R  ⟶B ⟶C)      = suc (size-⟶₁₋ ⟶B + size-⟶₁₋ ⟶C)
size-⟶₁₋ (∧ₚ₁₋L₁ B∧C∈ B⟶)    = suc (size-⟶₁₋ B⟶)
size-⟶₁₋ (∧ₚ₁₋L₂ B∧C∈ C⟶)    = suc (size-⟶₁₋ C⟶)
size-⟶₁₋ (∨ₚ₁₋R₁ ⟶B)         = suc (size-⟶₁₋ ⟶B)
size-⟶₁₋ (∨ₚ₁₋R₂ ⟶C)         = suc (size-⟶₁₋ ⟶C)
size-⟶₁₋ (∨ₚ₁₋L  B∨C∈ B⟶ C⟶) = suc (size-⟶₁₋ B⟶ + size-⟶₁₋ C⟶)
size-⟶₁₋ (→ₚ₁₋R  B⟶C)        = suc (size-⟶₁₋ B⟶C)
size-⟶₁₋ (→ₚ₁₋L  B→C∈ ⟶B C⟶) = suc (size-⟶₁₋ ⟶B + size-⟶₁₋ C⟶)
