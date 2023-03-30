-- Natural Deduction
open import Logic.First.Signature

module Logic.First.ND (Sig : Signature₁) where

open import Logic.First.Syntax Sig

infixl 4 _⊢₁_

data _⊢₁_ : Ctx₁ → P₁ → Set where
  pre₁  : inj₁ A ∈ Γ →
          --------
          Γ ⊢₁ A

  ⊥ₚ₁E  : Γ ⊢₁ ⊥ₚ₁ →
          -----------
          Γ ⊢₁ A

  ∧ₚ₁I  : Γ ⊢₁ A →
          Γ ⊢₁ B →
          -------------
          Γ ⊢₁ A ∧ₚ₁ B

  ∧ₚ₁E₁ : Γ ⊢₁ A ∧ₚ₁ B →
          ---------------
          Γ ⊢₁ A

  ∧ₚ₁E₂ : Γ ⊢₁ A ∧ₚ₁ B →
          ---------------
          Γ ⊢₁ B

  ∨ₚ₁I₁ : Γ ⊢₁ A →
          -------------
          Γ ⊢₁ A ∨ₚ₁ B

  ∨ₚ₁I₂ : Γ ⊢₁ B →
          -------------
          Γ ⊢₁ A ∨ₚ₁ B

  ∨ₚ₁E  : Γ ⊢₁ A ∨ₚ₁ B →
          inj₁ A ∷ Γ ⊢₁ C →
          inj₁ B ∷ Γ ⊢₁ C →
          ---------------
          Γ ⊢₁ C

  →ₚ₁I  : inj₁ A ∷ Γ ⊢₁ B →
          -------------
          Γ ⊢₁ A →ₚ₁ B

  →ₚ₁E  : Γ ⊢₁ A →ₚ₁ B →
          Γ ⊢₁ A →
          ---------------
          Γ ⊢₁ B

  ∀ₚ₁∙I : inj₂ s ∷ Γ ⊢₁ A →
          ------------------
          Γ ⊢₁ ∀ₚ₁ s ∙ A

  ∀ₚ₁∙E : Γ ⊢₁ ∀ₚ₁ s ∙ A →
          Γ ⊢ₜ₁ v ∈ₜ₁ s →
          ---------------------
          Γ ⊢₁ P₁-substₜ A v 0

size-⊢₁ : Γ ⊢₁ A → ℕ
size-⊢₁ (pre₁  A∈)         = 1
size-⊢₁ (⊥ₚ₁E  ⊢⊥)         = suc (size-⊢₁ ⊢⊥)
size-⊢₁ (∧ₚ₁I  ⊢A ⊢B)      = suc (size-⊢₁ ⊢A + size-⊢₁ ⊢B)
size-⊢₁ (∧ₚ₁E₁ ⊢A∧B)       = suc (size-⊢₁ ⊢A∧B)
size-⊢₁ (∧ₚ₁E₂ ⊢A∧B)       = suc (size-⊢₁ ⊢A∧B)
size-⊢₁ (∨ₚ₁I₁ ⊢A)         = suc (size-⊢₁ ⊢A)
size-⊢₁ (∨ₚ₁I₂ ⊢B)         = suc (size-⊢₁ ⊢B)
size-⊢₁ (∨ₚ₁E  ⊢A∨B A⊢ B⊢) = suc (size-⊢₁ ⊢A∨B + size-⊢₁ A⊢ + size-⊢₁ B⊢)
size-⊢₁ (→ₚ₁I  A⊢B)        = suc (size-⊢₁ A⊢B)
size-⊢₁ (→ₚ₁E  ⊢A→B ⊢A)    = suc (size-⊢₁ ⊢A→B + size-⊢₁ ⊢A)
size-⊢₁ (∀ₚ₁∙I ⊢A)         = suc (size-⊢₁ ⊢A)
size-⊢₁ (∀ₚ₁∙E ⊢A _)       = suc (size-⊢₁ ⊢A)
