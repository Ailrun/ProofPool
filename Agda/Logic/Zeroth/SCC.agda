-- Sequent Calculus with Cut
module Logic.Zeroth.SCC where

open import Logic.Zeroth.Syntax public

infixl 4 _⟶₀_

data _⟶₀_ : Ctx₀ → P₀ → Set where
  init₀ : A ∈ Γ →
          --------
          Γ ⟶₀ A

  ⊥ₚ₀L  : ⊥ₚ₀ ∈ Γ →
          ----------
          Γ ⟶₀ A

  ∧ₚ₀R  : Γ ⟶₀ A →
          Γ ⟶₀ B →
          -------------
          Γ ⟶₀ A ∧ₚ₀ B

  ∧ₚ₀L₁ : A ∧ₚ₀ B ∈ Γ →
          A ∷ Γ ⟶₀ C →
          --------------
          Γ ⟶₀ C

  ∧ₚ₀L₂ : A ∧ₚ₀ B ∈ Γ →
          B ∷ Γ ⟶₀ C →
          --------------
          Γ ⟶₀ C

  ∨ₚ₀R₁ : Γ ⟶₀ A →
          -------------
          Γ ⟶₀ A ∨ₚ₀ B

  ∨ₚ₀R₂ : Γ ⟶₀ B →
          -------------
          Γ ⟶₀ A ∨ₚ₀ B

  ∨ₚ₀L  : A ∨ₚ₀ B ∈ Γ →
          A ∷ Γ ⟶₀ C →
          B ∷ Γ ⟶₀ C →
          --------------
          Γ ⟶₀ C

  →ₚ₀R  : A ∷ Γ ⟶₀ B →
          -------------
          Γ ⟶₀ A →ₚ₀ B

  →ₚ₀L  : A →ₚ₀ B ∈ Γ →
          Γ ⟶₀ A →
          B ∷ Γ ⟶₀ C →
          --------------
          Γ ⟶₀ C

  cut₀  : Γ ⟶₀ A →
          A ∷ Γ ⟶₀ B →
          -------------
          Γ ⟶₀ B

size-⟶₀ : Γ ⟶₀ A → ℕ
size-⟶₀ (init₀ B∈)         = 1
size-⟶₀ (⊥ₚ₀L  ⊥∈)         = 1
size-⟶₀ (∧ₚ₀R  ⟶B ⟶C)      = suc (size-⟶₀ ⟶B + size-⟶₀ ⟶C)
size-⟶₀ (∧ₚ₀L₁ B∧C∈ B⟶)    = suc (size-⟶₀ B⟶)
size-⟶₀ (∧ₚ₀L₂ B∧C∈ C⟶)    = suc (size-⟶₀ C⟶)
size-⟶₀ (∨ₚ₀R₁ ⟶B)         = suc (size-⟶₀ ⟶B)
size-⟶₀ (∨ₚ₀R₂ ⟶C)         = suc (size-⟶₀ ⟶C)
size-⟶₀ (∨ₚ₀L  B∨C∈ B⟶ C⟶) = suc (size-⟶₀ B⟶ + size-⟶₀ C⟶)
size-⟶₀ (→ₚ₀R  B⟶C)        = suc (size-⟶₀ B⟶C)
size-⟶₀ (→ₚ₀L  B→C∈ ⟶B C⟶) = suc (size-⟶₀ ⟶B + size-⟶₀ C⟶)
size-⟶₀ (cut₀  ⟶B B⟶)      = suc (size-⟶₀ ⟶B + size-⟶₀ B⟶)
