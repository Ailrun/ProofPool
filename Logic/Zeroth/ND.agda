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
size-⊢₀ (pre₀ B∈)         = 1
size-⊢₀ (⊥ₚ₀E ⊢⊥)         = suc (size-⊢₀ ⊢⊥)
size-⊢₀ (∧ₚ₀I ⊢B ⊢C)      = suc (size-⊢₀ ⊢B + size-⊢₀ ⊢C)
size-⊢₀ (∧ₚ₀E₁ ⊢B∧C)      = suc (size-⊢₀ ⊢B∧C)
size-⊢₀ (∧ₚ₀E₂ ⊢B∧C)      = suc (size-⊢₀ ⊢B∧C)
size-⊢₀ (∨ₚ₀I₁ ⊢B)        = suc (size-⊢₀ ⊢B)
size-⊢₀ (∨ₚ₀I₂ ⊢C)        = suc (size-⊢₀ ⊢C)
size-⊢₀ (∨ₚ₀E ⊢B∨C B⊢ C⊢) = suc (size-⊢₀ ⊢B∨C + size-⊢₀ B⊢ + size-⊢₀ C⊢)
size-⊢₀ (→ₚ₀I B⊢C)        = suc (size-⊢₀ B⊢C)
size-⊢₀ (→ₚ₀E ⊢B→C ⊢B)    = suc (size-⊢₀ ⊢B→C + size-⊢₀ ⊢B)

⊢₀-resp-∈⇒∈ : (∀ {A} → A ∈ Γ → A ∈ Γ′) → Γ ⊢₀ B → Γ′ ⊢₀ B
⊢₀-resp-∈⇒∈ f (pre₀ B∈)         = pre₀ (f B∈)
⊢₀-resp-∈⇒∈ f (⊥ₚ₀E ⊢⊥)         = ⊥ₚ₀E (⊢₀-resp-∈⇒∈ f ⊢⊥)
⊢₀-resp-∈⇒∈ f (∧ₚ₀I ⊢B ⊢C)      = ∧ₚ₀I (⊢₀-resp-∈⇒∈ f ⊢B) (⊢₀-resp-∈⇒∈ f ⊢C)
⊢₀-resp-∈⇒∈ f (∧ₚ₀E₁ ⊢B∧C)      = ∧ₚ₀E₁ (⊢₀-resp-∈⇒∈ f ⊢B∧C)
⊢₀-resp-∈⇒∈ f (∧ₚ₀E₂ ⊢B∧C)      = ∧ₚ₀E₂ (⊢₀-resp-∈⇒∈ f ⊢B∧C)
⊢₀-resp-∈⇒∈ f (∨ₚ₀I₁ ⊢B)        = ∨ₚ₀I₁ (⊢₀-resp-∈⇒∈ f ⊢B)
⊢₀-resp-∈⇒∈ f (∨ₚ₀I₂ ⊢C)        = ∨ₚ₀I₂ (⊢₀-resp-∈⇒∈ f ⊢C)
⊢₀-resp-∈⇒∈ f (∨ₚ₀E ⊢B∨C B⊢ C⊢) = ∨ₚ₀E (⊢₀-resp-∈⇒∈ f ⊢B∨C) (⊢₀-resp-∈⇒∈ (∈⇒∈-ext f) B⊢) (⊢₀-resp-∈⇒∈ (∈⇒∈-ext f) C⊢)
⊢₀-resp-∈⇒∈ f (→ₚ₀I B⊢C)        = →ₚ₀I (⊢₀-resp-∈⇒∈ (∈⇒∈-ext f) B⊢C)
⊢₀-resp-∈⇒∈ f (→ₚ₀E ⊢B→C ⊢B)    = →ₚ₀E (⊢₀-resp-∈⇒∈ f ⊢B→C) (⊢₀-resp-∈⇒∈ f ⊢B)

⊢₀wk : Γ′ ++ Γ ⊢₀ B → Γ′ ++ A ∷ Γ ⊢₀ B
⊢₀wk {Γ′} ⊢B = ⊢₀-resp-∈⇒∈ (∈-++-∷ Γ′ _) ⊢B

⊢₀wk′ : Γ′ ++ Γ ⊢₀ A → Γ′ ++ Γ″ ++ Γ ⊢₀ A
⊢₀wk′ {Γ′} ⊢A = ⊢₀-resp-∈⇒∈ (∈-++-++ Γ′ _) ⊢A

⊢₀ct : Γ′ ++ A ∷ A ∷ Γ ⊢₀ B → Γ′ ++ A ∷ Γ ⊢₀ B
⊢₀ct {Γ′} ⊢B = ⊢₀-resp-∈⇒∈ (∈-++-dedupe₁ Γ′) ⊢B

⊢₀ex : Γ′ ++ A ∷ B ∷ Γ ⊢₀ C → Γ′ ++ B ∷ A ∷ Γ ⊢₀ C
⊢₀ex {Γ′} ⊢C = ⊢₀-resp-∈⇒∈ (∈-++-swap Γ′) ⊢C
