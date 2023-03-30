-- Sequent Calculus with Cut
open import Logic.First.Signature

module Logic.First.SCC (Sig : Signature₁) where

open import Logic.First.Syntax Sig

infixl 4 _⟶₁_

data _⟶₁_ : Ctx₁ → P₁ → Set where
  init₁ : inj₁ A ∈ Γ →
          -------------
          Γ ⟶₁ A

  ⊥ₚ₁L  : inj₁ ⊥ₚ₁ ∈ Γ →
          ---------------
          Γ ⟶₁ A

  ∧ₚ₁R  : Γ ⟶₁ A →
          Γ ⟶₁ B →
          -------------
          Γ ⟶₁ A ∧ₚ₁ B

  ∧ₚ₁L₁ : inj₁ (A ∧ₚ₁ B) ∈ Γ →
          inj₁ A ∷ Γ ⟶₁ C →
          ---------------------
          Γ ⟶₁ C

  ∧ₚ₁L₂ : inj₁ (A ∧ₚ₁ B) ∈ Γ →
          inj₁ B ∷ Γ ⟶₁ C →
          ---------------------
          Γ ⟶₁ C

  ∨ₚ₁R₁ : Γ ⟶₁ A →
          -------------
          Γ ⟶₁ A ∨ₚ₁ B

  ∨ₚ₁R₂ : Γ ⟶₁ B →
          -------------
          Γ ⟶₁ A ∨ₚ₁ B

  ∨ₚ₁L  : inj₁ (A ∨ₚ₁ B) ∈ Γ →
          inj₁ A ∷ Γ ⟶₁ C →
          inj₁ B ∷ Γ ⟶₁ C →
          ---------------------
          Γ ⟶₁ C

  →ₚ₁R  : inj₁ A ∷ Γ ⟶₁ B →
          ------------------
          Γ ⟶₁ A →ₚ₁ B

  →ₚ₁L  : inj₁ (A →ₚ₁ B) ∈ Γ →
          Γ ⟶₁ A →
          inj₁ B ∷ Γ ⟶₁ C →
          ---------------------
          Γ ⟶₁ C

  ∀ₚ₁∙R : inj₂ s ∷ Γ ⟶₁ B →
          -------------
          Γ ⟶₁ ∀ₚ₁ s ∙ B

  ∀ₚ₁∙L : inj₁ (∀ₚ₁ s ∙ B) ∈ Γ →
          inj₁ (P₁-substₜ B v 0) ∷ Γ ⟶₁ C →
          Γ ⊢ₜ₁ v ∈ₜ₁ s →
          ----------------------------------
          Γ ⟶₁ C

  cut₁  : Γ ⟶₁ A →
          inj₁ A ∷ Γ ⟶₁ B →
          ------------------
          Γ ⟶₁ B

size-⟶₁ : Γ ⟶₁ A → ℕ
size-⟶₁ (init₁ B∈)         = 1
size-⟶₁ (⊥ₚ₁L  ⊥∈)         = 1
size-⟶₁ (∧ₚ₁R  ⟶B ⟶C)      = suc (size-⟶₁ ⟶B + size-⟶₁ ⟶C)
size-⟶₁ (∧ₚ₁L₁ B∧C∈ B⟶)    = suc (size-⟶₁ B⟶)
size-⟶₁ (∧ₚ₁L₂ B∧C∈ C⟶)    = suc (size-⟶₁ C⟶)
size-⟶₁ (∨ₚ₁R₁ ⟶B)         = suc (size-⟶₁ ⟶B)
size-⟶₁ (∨ₚ₁R₂ ⟶C)         = suc (size-⟶₁ ⟶C)
size-⟶₁ (∨ₚ₁L  B∨C∈ B⟶ C⟶) = suc (size-⟶₁ B⟶ + size-⟶₁ C⟶)
size-⟶₁ (→ₚ₁R  B⟶C)        = suc (size-⟶₁ B⟶C)
size-⟶₁ (→ₚ₁L  B→C∈ ⟶B C⟶) = suc (size-⟶₁ ⟶B + size-⟶₁ C⟶)
size-⟶₁ (∀ₚ₁∙R s⟶B)        = suc (size-⟶₁ s⟶B)
size-⟶₁ (∀ₚ₁∙L _ B⟶ _)     = suc (size-⟶₁ B⟶)
size-⟶₁ (cut₁  ⟶B B⟶)      = suc (size-⟶₁ ⟶B + size-⟶₁ B⟶)
