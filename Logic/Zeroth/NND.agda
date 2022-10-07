-- Normal Natural Deduction
module Logic.Zeroth.NND where

open import Logic.Zeroth.Base
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

size-⊢₀ⁿ (∧ₚ₀ⁿI ⊢B ⊢C)      = suc (size-⊢₀ⁿ ⊢B + size-⊢₀ⁿ ⊢C)
size-⊢₀ⁿ (∨ₚ₀ⁿI₁ ⊢B)        = suc (size-⊢₀ⁿ ⊢B)
size-⊢₀ⁿ (∨ₚ₀ⁿI₂ ⊢C)        = suc (size-⊢₀ⁿ ⊢C)
size-⊢₀ⁿ (∨ₚ₀ⁿE ⊢B∨C B⊢ C⊢) = suc (size-⊢₀ʳ ⊢B∨C + size-⊢₀ⁿ B⊢ + size-⊢₀ⁿ C⊢)
size-⊢₀ⁿ (→ₚ₀ⁿI B⊢C)        = suc (size-⊢₀ⁿ B⊢C)
size-⊢₀ⁿ (neut₀ⁿ ⊢B)        = size-⊢₀ʳ ⊢B

size-⊢₀ʳ (pre₀ʳ B∈)      = 1
size-⊢₀ʳ (⊥ₚ₀ʳE ⊢⊥)      = suc (size-⊢₀ʳ ⊢⊥)
size-⊢₀ʳ (∧ₚ₀ʳE₁ ⊢B∧C)   = suc (size-⊢₀ʳ ⊢B∧C)
size-⊢₀ʳ (∧ₚ₀ʳE₂ ⊢B∧C)   = suc (size-⊢₀ʳ ⊢B∧C)
size-⊢₀ʳ (→ₚ₀ʳE ⊢B→C ⊢B) = suc (size-⊢₀ʳ ⊢B→C + size-⊢₀ⁿ ⊢B)

⊢₀ⁿ-resp-∈⇒∈ : (∀ {A} → A ∈ Γ → A ∈ Γ′) → Γ ⊢₀ⁿ B → Γ′ ⊢₀ⁿ B
⊢₀ʳ-resp-∈⇒∈ : (∀ {A} → A ∈ Γ → A ∈ Γ′) → Γ ⊢₀ʳ B → Γ′ ⊢₀ʳ B

⊢₀ⁿ-resp-∈⇒∈ f (∧ₚ₀ⁿI ⊢B ⊢C)      = ∧ₚ₀ⁿI (⊢₀ⁿ-resp-∈⇒∈ f ⊢B) (⊢₀ⁿ-resp-∈⇒∈ f ⊢C)
⊢₀ⁿ-resp-∈⇒∈ f (∨ₚ₀ⁿI₁ ⊢B)        = ∨ₚ₀ⁿI₁ (⊢₀ⁿ-resp-∈⇒∈ f ⊢B)
⊢₀ⁿ-resp-∈⇒∈ f (∨ₚ₀ⁿI₂ ⊢C)        = ∨ₚ₀ⁿI₂ (⊢₀ⁿ-resp-∈⇒∈ f ⊢C)
⊢₀ⁿ-resp-∈⇒∈ f (∨ₚ₀ⁿE ⊢B∨C B⊢ C⊢) = ∨ₚ₀ⁿE (⊢₀ʳ-resp-∈⇒∈ f ⊢B∨C) (⊢₀ⁿ-resp-∈⇒∈ (∈⇒∈-ext f) B⊢) (⊢₀ⁿ-resp-∈⇒∈ (∈⇒∈-ext f) C⊢)
⊢₀ⁿ-resp-∈⇒∈ f (→ₚ₀ⁿI B⊢C)        = →ₚ₀ⁿI (⊢₀ⁿ-resp-∈⇒∈ (∈⇒∈-ext f) B⊢C)
⊢₀ⁿ-resp-∈⇒∈ f (neut₀ⁿ ⊢B)        = neut₀ⁿ (⊢₀ʳ-resp-∈⇒∈ f ⊢B)

⊢₀ʳ-resp-∈⇒∈ f (pre₀ʳ B∈)      = pre₀ʳ (f B∈)
⊢₀ʳ-resp-∈⇒∈ f (⊥ₚ₀ʳE ⊢⊥)      = ⊥ₚ₀ʳE (⊢₀ʳ-resp-∈⇒∈ f ⊢⊥)
⊢₀ʳ-resp-∈⇒∈ f (∧ₚ₀ʳE₁ ⊢B∧C)   = ∧ₚ₀ʳE₁ (⊢₀ʳ-resp-∈⇒∈ f ⊢B∧C)
⊢₀ʳ-resp-∈⇒∈ f (∧ₚ₀ʳE₂ ⊢B∧C)   = ∧ₚ₀ʳE₂ (⊢₀ʳ-resp-∈⇒∈ f ⊢B∧C)
⊢₀ʳ-resp-∈⇒∈ f (→ₚ₀ʳE ⊢B→C ⊢B) = →ₚ₀ʳE (⊢₀ʳ-resp-∈⇒∈ f ⊢B→C) (⊢₀ⁿ-resp-∈⇒∈ f ⊢B)

⊢₀ⁿwk : Γ′ ++ Γ ⊢₀ⁿ B → Γ′ ++ A ∷ Γ ⊢₀ⁿ B
⊢₀ⁿwk {Γ′} ⊢B = ⊢₀ⁿ-resp-∈⇒∈ (∈-++-∷ Γ′ _) ⊢B

⊢₀ʳwk : Γ′ ++ Γ ⊢₀ʳ B → Γ′ ++ A ∷ Γ ⊢₀ʳ B
⊢₀ʳwk {Γ′} ⊢B = ⊢₀ʳ-resp-∈⇒∈ (∈-++-∷ Γ′ _) ⊢B

⊢₀ⁿwk′ : Γ′ ++ Γ ⊢₀ⁿ A → Γ′ ++ Γ″ ++ Γ ⊢₀ⁿ A
⊢₀ⁿwk′ {Γ′} ⊢A = ⊢₀ⁿ-resp-∈⇒∈ (∈-++-++ Γ′ _) ⊢A

⊢₀ʳwk′ : Γ′ ++ Γ ⊢₀ʳ A → Γ′ ++ Γ″ ++ Γ ⊢₀ʳ A
⊢₀ʳwk′ {Γ′} ⊢A = ⊢₀ʳ-resp-∈⇒∈ (∈-++-++ Γ′ _) ⊢A

⊢₀ⁿct : Γ′ ++ A ∷ A ∷ Γ ⊢₀ⁿ B → Γ′ ++ A ∷ Γ ⊢₀ⁿ B
⊢₀ⁿct {Γ′} ⊢B = ⊢₀ⁿ-resp-∈⇒∈ (∈-++-dedupe₁ Γ′) ⊢B

⊢₀ʳct : Γ′ ++ A ∷ A ∷ Γ ⊢₀ʳ B → Γ′ ++ A ∷ Γ ⊢₀ʳ B
⊢₀ʳct {Γ′} ⊢B = ⊢₀ʳ-resp-∈⇒∈ (∈-++-dedupe₁ Γ′) ⊢B

⊢₀ⁿex : Γ′ ++ A ∷ B ∷ Γ ⊢₀ⁿ C → Γ′ ++ B ∷ A ∷ Γ ⊢₀ⁿ C
⊢₀ⁿex {Γ′} ⊢C = ⊢₀ⁿ-resp-∈⇒∈ (∈-++-swap Γ′) ⊢C

⊢₀ʳex : Γ′ ++ A ∷ B ∷ Γ ⊢₀ʳ C → Γ′ ++ B ∷ A ∷ Γ ⊢₀ʳ C
⊢₀ʳex {Γ′} ⊢C = ⊢₀ʳ-resp-∈⇒∈ (∈-++-swap Γ′) ⊢C
