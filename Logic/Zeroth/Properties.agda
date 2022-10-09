module Logic.Zeroth.Properties where

open import Logic.Zeroth.Base
open import Logic.Zeroth.ND
open import Logic.Zeroth.ND.Properties
open import Logic.Zeroth.NND
open import Logic.Zeroth.NND.Properties
open import Logic.Zeroth.SC
open import Logic.Zeroth.SC.Properties
open import Logic.Zeroth.SCC
open import Logic.Zeroth.SCC.Properties

-- Soundness and Completeness between Systems
⊢₀⇒⟶₀ : Γ ⊢₀ A → Γ ⟶₀ A
⊢₀⇒⟶₀ (pre₀  A∈)         = init₀ A∈
⊢₀⇒⟶₀ (⊥ₚ₀E  ⊢⊥)         = cut₀ (⊢₀⇒⟶₀ ⊢⊥) (⊥ₚ₀L (here refl))
⊢₀⇒⟶₀ (∧ₚ₀I  ⊢A ⊢B)      = ∧ₚ₀R (⊢₀⇒⟶₀ ⊢A) (⊢₀⇒⟶₀ ⊢B)
⊢₀⇒⟶₀ (∧ₚ₀E₁ ⊢A∧B)       = cut₀ (⊢₀⇒⟶₀ ⊢A∧B) (∧ₚ₀L₁ (here refl) (init₀ (here refl)))
⊢₀⇒⟶₀ (∧ₚ₀E₂ ⊢A∧B)       = cut₀ (⊢₀⇒⟶₀ ⊢A∧B) (∧ₚ₀L₂ (here refl) (init₀ (here refl)))
⊢₀⇒⟶₀ (∨ₚ₀I₁ ⊢A)         = ∨ₚ₀R₁ (⊢₀⇒⟶₀ ⊢A)
⊢₀⇒⟶₀ (∨ₚ₀I₂ ⊢B)         = ∨ₚ₀R₂ (⊢₀⇒⟶₀ ⊢B)
⊢₀⇒⟶₀ (∨ₚ₀E  ⊢A∨B A⊢ B⊢) = cut₀ (⊢₀⇒⟶₀ ⊢A∨B) (∨ₚ₀L (here refl) (⟶₀wk {_ ∷ []} (⊢₀⇒⟶₀ A⊢)) (⟶₀wk {_ ∷ []} (⊢₀⇒⟶₀ B⊢)))
⊢₀⇒⟶₀ (→ₚ₀I  A⊢B)        = →ₚ₀R (⊢₀⇒⟶₀ A⊢B)
⊢₀⇒⟶₀ (→ₚ₀E  ⊢A→B ⊢A)    = cut₀ (⊢₀⇒⟶₀ ⊢A→B) (→ₚ₀L (here refl) (⟶₀wk {[]} (⊢₀⇒⟶₀ ⊢A)) (init₀ (here refl)))

⟶₀⇒⊢₀ : Γ ⟶₀ A → Γ ⊢₀ A
⟶₀⇒⊢₀ (init₀ A∈)         = pre₀ A∈
⟶₀⇒⊢₀ (⊥ₚ₀L  ⊥∈)         = ⊥ₚ₀E (pre₀ ⊥∈)
⟶₀⇒⊢₀ (∧ₚ₀R  ⟶A ⟶B)      = ∧ₚ₀I (⟶₀⇒⊢₀ ⟶A) (⟶₀⇒⊢₀ ⟶B)
⟶₀⇒⊢₀ (∧ₚ₀L₁ A∧B∈ A⟶)    = ⊢₀-subst {[]} (⟶₀⇒⊢₀ A⟶) (∧ₚ₀E₁ (pre₀ A∧B∈))
⟶₀⇒⊢₀ (∧ₚ₀L₂ A∧B∈ B⟶)    = ⊢₀-subst {[]} (⟶₀⇒⊢₀ B⟶) (∧ₚ₀E₂ (pre₀ A∧B∈))
⟶₀⇒⊢₀ (∨ₚ₀R₁ ⟶A)         = ∨ₚ₀I₁ (⟶₀⇒⊢₀ ⟶A)
⟶₀⇒⊢₀ (∨ₚ₀R₂ ⟶B)         = ∨ₚ₀I₂ (⟶₀⇒⊢₀ ⟶B)
⟶₀⇒⊢₀ (∨ₚ₀L  A∨B∈ A⟶ B⟶) = ∨ₚ₀E (pre₀ A∨B∈) (⟶₀⇒⊢₀ A⟶) (⟶₀⇒⊢₀ B⟶)
⟶₀⇒⊢₀ (→ₚ₀R  A⟶B)        = →ₚ₀I (⟶₀⇒⊢₀ A⟶B)
⟶₀⇒⊢₀ (→ₚ₀L  A→B∈ ⟶A B⟶) = ⊢₀-subst {[]} (⟶₀⇒⊢₀ B⟶) (→ₚ₀E (pre₀ A→B∈) (⟶₀⇒⊢₀ ⟶A))
⟶₀⇒⊢₀ (cut₀  ⟶A A⟶)      = ∨ₚ₀E (∨ₚ₀I₁ (⟶₀⇒⊢₀ ⟶A)) (⟶₀⇒⊢₀ A⟶) (⟶₀⇒⊢₀ A⟶)

⟶₀₋⇒⟶₀ : Γ ⟶₀₋ A → Γ ⟶₀ A
⟶₀₋⇒⟶₀ (init₀₋ A∈)         = init₀ A∈
⟶₀₋⇒⟶₀ (⊥ₚ₀₋L  ⊥∈)         = ⊥ₚ₀L ⊥∈
⟶₀₋⇒⟶₀ (∧ₚ₀₋R  ⟶A ⟶B)      = ∧ₚ₀R (⟶₀₋⇒⟶₀ ⟶A) (⟶₀₋⇒⟶₀ ⟶B)
⟶₀₋⇒⟶₀ (∧ₚ₀₋L₁ A∧B∈ A⟶)    = ∧ₚ₀L₁ A∧B∈ (⟶₀₋⇒⟶₀ A⟶)
⟶₀₋⇒⟶₀ (∧ₚ₀₋L₂ A∧B∈ B⟶)    = ∧ₚ₀L₂ A∧B∈ (⟶₀₋⇒⟶₀ B⟶)
⟶₀₋⇒⟶₀ (∨ₚ₀₋R₁ ⟶A)         = ∨ₚ₀R₁ (⟶₀₋⇒⟶₀ ⟶A)
⟶₀₋⇒⟶₀ (∨ₚ₀₋R₂ ⟶B)         = ∨ₚ₀R₂ (⟶₀₋⇒⟶₀ ⟶B)
⟶₀₋⇒⟶₀ (∨ₚ₀₋L  A∨B∈ A⟶ B⟶) = ∨ₚ₀L A∨B∈ (⟶₀₋⇒⟶₀ A⟶) (⟶₀₋⇒⟶₀ B⟶)
⟶₀₋⇒⟶₀ (→ₚ₀₋R  A⟶B)        = →ₚ₀R (⟶₀₋⇒⟶₀ A⟶B)
⟶₀₋⇒⟶₀ (→ₚ₀₋L  A→B∈ ⟶A B⟶) = →ₚ₀L A→B∈ (⟶₀₋⇒⟶₀ ⟶A) (⟶₀₋⇒⟶₀ B⟶)

⟶₀⇒⟶₀₋ : Γ ⟶₀ A → Γ ⟶₀₋ A
⟶₀⇒⟶₀₋ (init₀ A∈)         = init₀₋ A∈
⟶₀⇒⟶₀₋ (⊥ₚ₀L  ⊥∈)         = ⊥ₚ₀₋L ⊥∈
⟶₀⇒⟶₀₋ (∧ₚ₀R  ⟶A ⟶B)      = ∧ₚ₀₋R (⟶₀⇒⟶₀₋ ⟶A) (⟶₀⇒⟶₀₋ ⟶B)
⟶₀⇒⟶₀₋ (∧ₚ₀L₁ A∧B∈ A⟶)    = ∧ₚ₀₋L₁ A∧B∈ (⟶₀⇒⟶₀₋ A⟶)
⟶₀⇒⟶₀₋ (∧ₚ₀L₂ A∧B∈ B⟶)    = ∧ₚ₀₋L₂ A∧B∈ (⟶₀⇒⟶₀₋ B⟶)
⟶₀⇒⟶₀₋ (∨ₚ₀R₁ ⟶A)         = ∨ₚ₀₋R₁ (⟶₀⇒⟶₀₋ ⟶A)
⟶₀⇒⟶₀₋ (∨ₚ₀R₂ ⟶B)         = ∨ₚ₀₋R₂ (⟶₀⇒⟶₀₋ ⟶B)
⟶₀⇒⟶₀₋ (∨ₚ₀L  A∨B∈ A⟶ B⟶) = ∨ₚ₀₋L A∨B∈ (⟶₀⇒⟶₀₋ A⟶) (⟶₀⇒⟶₀₋ B⟶)
⟶₀⇒⟶₀₋ (→ₚ₀R  A⟶B)        = →ₚ₀₋R (⟶₀⇒⟶₀₋ A⟶B)
⟶₀⇒⟶₀₋ (→ₚ₀L  A→B∈ ⟶A B⟶) = →ₚ₀₋L A→B∈ (⟶₀⇒⟶₀₋ ⟶A) (⟶₀⇒⟶₀₋ B⟶)
⟶₀⇒⟶₀₋ (cut₀  ⟶A A⟶)      = cut-elimination₀ (⟶₀⇒⟶₀₋ ⟶A) (⟶₀⇒⟶₀₋ A⟶)

⟶₀₋⇒⊢₀ⁿ : Γ ⟶₀₋ A → Γ ⊢₀ⁿ A
⟶₀₋⇒⊢₀ⁿ (init₀₋ A∈)         = neut₀ⁿ (pre₀ʳ A∈)
⟶₀₋⇒⊢₀ⁿ (⊥ₚ₀₋L  ⊥∈)         = neut₀ⁿ (⊥ₚ₀ʳE (pre₀ʳ ⊥∈))
⟶₀₋⇒⊢₀ⁿ (∧ₚ₀₋R  ⟶A ⟶B)      = ∧ₚ₀ⁿI (⟶₀₋⇒⊢₀ⁿ ⟶A) (⟶₀₋⇒⊢₀ⁿ ⟶B)
⟶₀₋⇒⊢₀ⁿ (∧ₚ₀₋L₁ A∧B∈ A⟶)    = ⊢₀ⁿ-subst {[]} (⟶₀₋⇒⊢₀ⁿ A⟶) (∧ₚ₀ʳE₁ (pre₀ʳ A∧B∈))
⟶₀₋⇒⊢₀ⁿ (∧ₚ₀₋L₂ A∧B∈ B⟶)    = ⊢₀ⁿ-subst {[]} (⟶₀₋⇒⊢₀ⁿ B⟶) (∧ₚ₀ʳE₂ (pre₀ʳ A∧B∈))
⟶₀₋⇒⊢₀ⁿ (∨ₚ₀₋R₁ ⟶A)         = ∨ₚ₀ⁿI₁ (⟶₀₋⇒⊢₀ⁿ ⟶A)
⟶₀₋⇒⊢₀ⁿ (∨ₚ₀₋R₂ ⟶B)         = ∨ₚ₀ⁿI₂ (⟶₀₋⇒⊢₀ⁿ ⟶B)
⟶₀₋⇒⊢₀ⁿ (∨ₚ₀₋L  A∨B∈ A⟶ B⟶) = ∨ₚ₀ⁿE (pre₀ʳ A∨B∈) (⟶₀₋⇒⊢₀ⁿ A⟶) (⟶₀₋⇒⊢₀ⁿ B⟶)
⟶₀₋⇒⊢₀ⁿ (→ₚ₀₋R  A⟶B)        = →ₚ₀ⁿI (⟶₀₋⇒⊢₀ⁿ A⟶B)
⟶₀₋⇒⊢₀ⁿ (→ₚ₀₋L  A→B∈ ⟶A B⟶) = ⊢₀ⁿ-subst {[]} (⟶₀₋⇒⊢₀ⁿ B⟶) (→ₚ₀ʳE (pre₀ʳ A→B∈) (⟶₀₋⇒⊢₀ⁿ ⟶A))

⊢₀ⁿ⇒⟶₀₋ : Γ ⊢₀ⁿ A → Γ ⟶₀₋ A
⊢₀ʳ⇒⟶₀₋⇒⟶₀₋ : Γ ⊢₀ʳ A → A ∷ Γ ⟶₀₋ C → Γ ⟶₀₋ C

⊢₀ⁿ⇒⟶₀₋ (∧ₚ₀ⁿI  ⊢A ⊢B)      = ∧ₚ₀₋R (⊢₀ⁿ⇒⟶₀₋ ⊢A) (⊢₀ⁿ⇒⟶₀₋ ⊢B)
⊢₀ⁿ⇒⟶₀₋ (∨ₚ₀ⁿI₁ ⊢A)         = ∨ₚ₀₋R₁ (⊢₀ⁿ⇒⟶₀₋ ⊢A)
⊢₀ⁿ⇒⟶₀₋ (∨ₚ₀ⁿI₂ ⊢B)         = ∨ₚ₀₋R₂ (⊢₀ⁿ⇒⟶₀₋ ⊢B)
⊢₀ⁿ⇒⟶₀₋ (∨ₚ₀ⁿE  ⊢A∨B A⊢ B⊢) = ⊢₀ʳ⇒⟶₀₋⇒⟶₀₋ ⊢A∨B (∨ₚ₀₋L (here refl) (⟶₀₋wk {_ ∷ []} (⊢₀ⁿ⇒⟶₀₋ A⊢)) (⟶₀₋wk {_ ∷ []} (⊢₀ⁿ⇒⟶₀₋ B⊢)))
⊢₀ⁿ⇒⟶₀₋ (→ₚ₀ⁿI  A⊢B)        = →ₚ₀₋R (⊢₀ⁿ⇒⟶₀₋ A⊢B)
⊢₀ⁿ⇒⟶₀₋ (neut₀ⁿ ⊢A)         = ⊢₀ʳ⇒⟶₀₋⇒⟶₀₋ ⊢A (init₀₋ (here refl))

⊢₀ʳ⇒⟶₀₋⇒⟶₀₋ (pre₀ʳ  A∈)         A⟶ = ⟶₀₋-resp-∈⇒∈ ∈⇒∈ A⟶
  where
    ∈⇒∈ : ∀ {B} → B ∈ _ ∷ _ → B ∈ _
    ∈⇒∈ (here refl) = ∈-++⁺ʳ _ A∈
    ∈⇒∈ (there B∈)  = ∈-++⁺ʳ _ B∈
⊢₀ʳ⇒⟶₀₋⇒⟶₀₋ (⊥ₚ₀ʳE  ⊢⊥)         _  = ⊢₀ʳ⇒⟶₀₋⇒⟶₀₋ ⊢⊥ (⊥ₚ₀₋L (here refl))
⊢₀ʳ⇒⟶₀₋⇒⟶₀₋ (∧ₚ₀ʳE₁ ⊢A∧B)       A⟶ = ⊢₀ʳ⇒⟶₀₋⇒⟶₀₋ ⊢A∧B (∧ₚ₀₋L₁ (here refl) (⟶₀₋wk {_ ∷ []} A⟶))
⊢₀ʳ⇒⟶₀₋⇒⟶₀₋ (∧ₚ₀ʳE₂ ⊢A∧B)       B⟶ = ⊢₀ʳ⇒⟶₀₋⇒⟶₀₋ ⊢A∧B (∧ₚ₀₋L₂ (here refl) (⟶₀₋wk {_ ∷ []} B⟶))
⊢₀ʳ⇒⟶₀₋⇒⟶₀₋ (→ₚ₀ʳE  ⊢A→B ⊢A)    B⟶ = ⊢₀ʳ⇒⟶₀₋⇒⟶₀₋ ⊢A→B (→ₚ₀₋L (here refl) (⟶₀₋wk {[]} (⊢₀ⁿ⇒⟶₀₋ ⊢A)) (⟶₀₋wk {_ ∷ []} B⟶))

-- Consistencies of Systems from Soundness/Completeness
⟶₀-consistency : [] ⟶₀ ⊥ₚ₀ → ⊥
⟶₀-consistency ⟶⊥ = ⟶₀₋-consistency (⟶₀⇒⟶₀₋ ⟶⊥)

⊢₀-consistency : [] ⊢₀ ⊥ₚ₀ → ⊥
⊢₀-consistency ⊢⊥ = ⟶₀-consistency (⊢₀⇒⟶₀ ⊢⊥)

⊢₀ⁿ-consistency : [] ⊢₀ⁿ ⊥ₚ₀ → ⊥
⊢₀ⁿ-consistency ⊢⊥ = ⟶₀₋-consistency (⊢₀ⁿ⇒⟶₀₋ ⊢⊥)

⊢₀ʳ-consistency : [] ⊢₀ʳ ⊥ₚ₀ → ⊥
⊢₀ʳ-consistency ⊢⊥ = ⊢₀ⁿ-consistency (neut₀ⁿ ⊢⊥)

-- Weak Normalization of Natural Deduction
weak-normalization₀ : Γ ⊢₀ A → Γ ⊢₀ⁿ A
weak-normalization₀ ⊢A = ⟶₀₋⇒⊢₀ⁿ (⟶₀⇒⟶₀₋ (⊢₀⇒⟶₀ ⊢A))
