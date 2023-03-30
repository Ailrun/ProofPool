open import Logic.First.Signature

module Logic.First.Properties (Sig : Signature₁) where

open import Logic.First.ND Sig
open import Logic.First.ND.Properties Sig
-- open import Logic.Zeroth.NND
-- open import Logic.Zeroth.NND.Properties
-- open import Logic.Zeroth.SC
-- open import Logic.Zeroth.SC.Properties
open import Logic.First.SCC Sig
open import Logic.First.SCC.Properties Sig
open import Logic.First.Syntax Sig

-- Soundness and Completeness between Systems
⊢₁⇒⟶₁ : Γ ⊢₁ A → Γ ⟶₁ A
⊢₁⇒⟶₁ (pre₁  A∈)         = init₁ A∈
⊢₁⇒⟶₁ (⊥ₚ₁E  ⊢⊥)         = cut₁ (⊢₁⇒⟶₁ ⊢⊥) (⊥ₚ₁L (here refl))
⊢₁⇒⟶₁ (∧ₚ₁I  ⊢A ⊢B)      = ∧ₚ₁R (⊢₁⇒⟶₁ ⊢A) (⊢₁⇒⟶₁ ⊢B)
⊢₁⇒⟶₁ (∧ₚ₁E₁ ⊢A∧B)       = cut₁ (⊢₁⇒⟶₁ ⊢A∧B) (∧ₚ₁L₁ (here refl) (init₁ (here refl)))
⊢₁⇒⟶₁ (∧ₚ₁E₂ ⊢A∧B)       = cut₁ (⊢₁⇒⟶₁ ⊢A∧B) (∧ₚ₁L₂ (here refl) (init₁ (here refl)))
⊢₁⇒⟶₁ (∨ₚ₁I₁ ⊢A)         = ∨ₚ₁R₁ (⊢₁⇒⟶₁ ⊢A)
⊢₁⇒⟶₁ (∨ₚ₁I₂ ⊢B)         = ∨ₚ₁R₂ (⊢₁⇒⟶₁ ⊢B)
⊢₁⇒⟶₁ (∨ₚ₁E  ⊢A∨B A⊢ B⊢) = cut₁ (⊢₁⇒⟶₁ ⊢A∨B) (∨ₚ₁L (here refl) {!!} {!!}) -- (⟶₁wk {_ ∷ []} (⊢₁⇒⟶₁ A⊢)) (⟶₁wk {_ ∷ []} (⊢₁⇒⟶₁ B⊢)))
⊢₁⇒⟶₁ (→ₚ₁I  A⊢B)        = →ₚ₁R (⊢₁⇒⟶₁ A⊢B)
⊢₁⇒⟶₁ (→ₚ₁E  ⊢A→B ⊢A)    = cut₁ (⊢₁⇒⟶₁ ⊢A→B) (→ₚ₁L (here refl) {!!} {!!}) -- (⟶₁wk {[]} (⊢₁⇒⟶₁ ⊢A)) (init₁ (here refl)))
⊢₁⇒⟶₁ (∀ₚ₁∙I s⊢A)        = ∀ₚ₁∙R (⊢₁⇒⟶₁ s⊢A)
⊢₁⇒⟶₁ (∀ₚ₁∙E ⊢A ⊢v)      = cut₁ (⊢₁⇒⟶₁ ⊢A) (∀ₚ₁∙L (here refl) (init₁ (here refl)) {!!})

⟶₁⇒⊢₁ : Γ ⟶₁ A → Γ ⊢₁ A
⟶₁⇒⊢₁ (init₁ A∈)         = pre₁ A∈
⟶₁⇒⊢₁ (⊥ₚ₁L  ⊥∈)         = ⊥ₚ₁E (pre₁ ⊥∈)
⟶₁⇒⊢₁ (∧ₚ₁R  ⟶A ⟶B)      = ∧ₚ₁I (⟶₁⇒⊢₁ ⟶A) (⟶₁⇒⊢₁ ⟶B)
⟶₁⇒⊢₁ (∧ₚ₁L₁ A∧B∈ A⟶)    = {!!} -- ⊢₁-subst {[]} (⟶₁⇒⊢₁ A⟶) (∧ₚ₁E₁ (pre₁ A∧B∈))
⟶₁⇒⊢₁ (∧ₚ₁L₂ A∧B∈ B⟶)    = {!!} -- ⊢₁-subst {[]} (⟶₁⇒⊢₁ B⟶) (∧ₚ₁E₂ (pre₁ A∧B∈))
⟶₁⇒⊢₁ (∨ₚ₁R₁ ⟶A)         = ∨ₚ₁I₁ (⟶₁⇒⊢₁ ⟶A)
⟶₁⇒⊢₁ (∨ₚ₁R₂ ⟶B)         = ∨ₚ₁I₂ (⟶₁⇒⊢₁ ⟶B)
⟶₁⇒⊢₁ (∨ₚ₁L  A∨B∈ A⟶ B⟶) = ∨ₚ₁E (pre₁ A∨B∈) (⟶₁⇒⊢₁ A⟶) (⟶₁⇒⊢₁ B⟶)
⟶₁⇒⊢₁ (→ₚ₁R  A⟶B)        = →ₚ₁I (⟶₁⇒⊢₁ A⟶B)
⟶₁⇒⊢₁ (→ₚ₁L  A→B∈ ⟶A B⟶) = {!!} -- ⊢₁-subst {[]} (⟶₁⇒⊢₁ B⟶) (→ₚ₁E (pre₁ A→B∈) (⟶₁⇒⊢₁ ⟶A))
⟶₁⇒⊢₁ (cut₁  ⟶A A⟶)      = ∨ₚ₁E (∨ₚ₁I₁ (⟶₁⇒⊢₁ ⟶A)) (⟶₁⇒⊢₁ A⟶) (⟶₁⇒⊢₁ A⟶)
⟶₁⇒⊢₁ (∀ₚ₁∙R s⟶A)        = ∀ₚ₁∙I (⟶₁⇒⊢₁ s⟶A)
⟶₁⇒⊢₁ (∀ₚ₁∙L ∀A∈ ⟶A ⊢v)  = {!!}

-- ⟶₁₋⇒⟶₁ : Γ ⟶₁₋ A → Γ ⟶₁ A
-- ⟶₁₋⇒⟶₁ (init₁₋ A∈)         = init₁ A∈
-- ⟶₁₋⇒⟶₁ (⊥ₚ₁₋L  ⊥∈)         = ⊥ₚ₁L ⊥∈
-- ⟶₁₋⇒⟶₁ (∧ₚ₁₋R  ⟶A ⟶B)      = ∧ₚ₁R (⟶₁₋⇒⟶₁ ⟶A) (⟶₁₋⇒⟶₁ ⟶B)
-- ⟶₁₋⇒⟶₁ (∧ₚ₁₋L₁ A∧B∈ A⟶)    = ∧ₚ₁L₁ A∧B∈ (⟶₁₋⇒⟶₁ A⟶)
-- ⟶₁₋⇒⟶₁ (∧ₚ₁₋L₂ A∧B∈ B⟶)    = ∧ₚ₁L₂ A∧B∈ (⟶₁₋⇒⟶₁ B⟶)
-- ⟶₁₋⇒⟶₁ (∨ₚ₁₋R₁ ⟶A)         = ∨ₚ₁R₁ (⟶₁₋⇒⟶₁ ⟶A)
-- ⟶₁₋⇒⟶₁ (∨ₚ₁₋R₂ ⟶B)         = ∨ₚ₁R₂ (⟶₁₋⇒⟶₁ ⟶B)
-- ⟶₁₋⇒⟶₁ (∨ₚ₁₋L  A∨B∈ A⟶ B⟶) = ∨ₚ₁L A∨B∈ (⟶₁₋⇒⟶₁ A⟶) (⟶₁₋⇒⟶₁ B⟶)
-- ⟶₁₋⇒⟶₁ (→ₚ₁₋R  A⟶B)        = →ₚ₁R (⟶₁₋⇒⟶₁ A⟶B)
-- ⟶₁₋⇒⟶₁ (→ₚ₁₋L  A→B∈ ⟶A B⟶) = →ₚ₁L A→B∈ (⟶₁₋⇒⟶₁ ⟶A) (⟶₁₋⇒⟶₁ B⟶)

-- ⟶₁⇒⟶₁₋ : Γ ⟶₁ A → Γ ⟶₁₋ A
-- ⟶₁⇒⟶₁₋ (init₁ A∈)         = init₁₋ A∈
-- ⟶₁⇒⟶₁₋ (⊥ₚ₁L  ⊥∈)         = ⊥ₚ₁₋L ⊥∈
-- ⟶₁⇒⟶₁₋ (∧ₚ₁R  ⟶A ⟶B)      = ∧ₚ₁₋R (⟶₁⇒⟶₁₋ ⟶A) (⟶₁⇒⟶₁₋ ⟶B)
-- ⟶₁⇒⟶₁₋ (∧ₚ₁L₁ A∧B∈ A⟶)    = ∧ₚ₁₋L₁ A∧B∈ (⟶₁⇒⟶₁₋ A⟶)
-- ⟶₁⇒⟶₁₋ (∧ₚ₁L₂ A∧B∈ B⟶)    = ∧ₚ₁₋L₂ A∧B∈ (⟶₁⇒⟶₁₋ B⟶)
-- ⟶₁⇒⟶₁₋ (∨ₚ₁R₁ ⟶A)         = ∨ₚ₁₋R₁ (⟶₁⇒⟶₁₋ ⟶A)
-- ⟶₁⇒⟶₁₋ (∨ₚ₁R₂ ⟶B)         = ∨ₚ₁₋R₂ (⟶₁⇒⟶₁₋ ⟶B)
-- ⟶₁⇒⟶₁₋ (∨ₚ₁L  A∨B∈ A⟶ B⟶) = ∨ₚ₁₋L A∨B∈ (⟶₁⇒⟶₁₋ A⟶) (⟶₁⇒⟶₁₋ B⟶)
-- ⟶₁⇒⟶₁₋ (→ₚ₁R  A⟶B)        = →ₚ₁₋R (⟶₁⇒⟶₁₋ A⟶B)
-- ⟶₁⇒⟶₁₋ (→ₚ₁L  A→B∈ ⟶A B⟶) = →ₚ₁₋L A→B∈ (⟶₁⇒⟶₁₋ ⟶A) (⟶₁⇒⟶₁₋ B⟶)
-- ⟶₁⇒⟶₁₋ (cut₁  ⟶A A⟶)      = cut₁₋ (⟶₁⇒⟶₁₋ ⟶A) (⟶₁⇒⟶₁₋ A⟶)

-- ⟶₁₋⇒⊢₁ⁿ : Γ ⟶₁₋ A → Γ ⊢₁ⁿ A
-- ⟶₁₋⇒⊢₁ⁿ (init₁₋ A∈)         = neut₁ⁿ (pre₁ʳ A∈)
-- ⟶₁₋⇒⊢₁ⁿ (⊥ₚ₁₋L  ⊥∈)         = neut₁ⁿ (⊥ₚ₁ʳE (pre₁ʳ ⊥∈))
-- ⟶₁₋⇒⊢₁ⁿ (∧ₚ₁₋R  ⟶A ⟶B)      = ∧ₚ₁ⁿI (⟶₁₋⇒⊢₁ⁿ ⟶A) (⟶₁₋⇒⊢₁ⁿ ⟶B)
-- ⟶₁₋⇒⊢₁ⁿ (∧ₚ₁₋L₁ A∧B∈ A⟶)    = ⊢₁ⁿ-subst {[]} (⟶₁₋⇒⊢₁ⁿ A⟶) (∧ₚ₁ʳE₁ (pre₁ʳ A∧B∈))
-- ⟶₁₋⇒⊢₁ⁿ (∧ₚ₁₋L₂ A∧B∈ B⟶)    = ⊢₁ⁿ-subst {[]} (⟶₁₋⇒⊢₁ⁿ B⟶) (∧ₚ₁ʳE₂ (pre₁ʳ A∧B∈))
-- ⟶₁₋⇒⊢₁ⁿ (∨ₚ₁₋R₁ ⟶A)         = ∨ₚ₁ⁿI₁ (⟶₁₋⇒⊢₁ⁿ ⟶A)
-- ⟶₁₋⇒⊢₁ⁿ (∨ₚ₁₋R₂ ⟶B)         = ∨ₚ₁ⁿI₂ (⟶₁₋⇒⊢₁ⁿ ⟶B)
-- ⟶₁₋⇒⊢₁ⁿ (∨ₚ₁₋L  A∨B∈ A⟶ B⟶) = ∨ₚ₁ⁿE (pre₁ʳ A∨B∈) (⟶₁₋⇒⊢₁ⁿ A⟶) (⟶₁₋⇒⊢₁ⁿ B⟶)
-- ⟶₁₋⇒⊢₁ⁿ (→ₚ₁₋R  A⟶B)        = →ₚ₁ⁿI (⟶₁₋⇒⊢₁ⁿ A⟶B)
-- ⟶₁₋⇒⊢₁ⁿ (→ₚ₁₋L  A→B∈ ⟶A B⟶) = ⊢₁ⁿ-subst {[]} (⟶₁₋⇒⊢₁ⁿ B⟶) (→ₚ₁ʳE (pre₁ʳ A→B∈) (⟶₁₋⇒⊢₁ⁿ ⟶A))

-- ⊢₁ⁿ⇒⟶₁₋ : Γ ⊢₁ⁿ A → Γ ⟶₁₋ A
-- ⊢₁ʳ⇒⟶₁₋⇒⟶₁₋ : Γ ⊢₁ʳ A → A ∷ Γ ⟶₁₋ C → Γ ⟶₁₋ C

-- ⊢₁ⁿ⇒⟶₁₋ (∧ₚ₁ⁿI  ⊢A ⊢B)      = ∧ₚ₁₋R (⊢₁ⁿ⇒⟶₁₋ ⊢A) (⊢₁ⁿ⇒⟶₁₋ ⊢B)
-- ⊢₁ⁿ⇒⟶₁₋ (∨ₚ₁ⁿI₁ ⊢A)         = ∨ₚ₁₋R₁ (⊢₁ⁿ⇒⟶₁₋ ⊢A)
-- ⊢₁ⁿ⇒⟶₁₋ (∨ₚ₁ⁿI₂ ⊢B)         = ∨ₚ₁₋R₂ (⊢₁ⁿ⇒⟶₁₋ ⊢B)
-- ⊢₁ⁿ⇒⟶₁₋ (∨ₚ₁ⁿE  ⊢A∨B A⊢ B⊢) = ⊢₁ʳ⇒⟶₁₋⇒⟶₁₋ ⊢A∨B (∨ₚ₁₋L (here refl) (⟶₁₋wk {_ ∷ []} (⊢₁ⁿ⇒⟶₁₋ A⊢)) (⟶₁₋wk {_ ∷ []} (⊢₁ⁿ⇒⟶₁₋ B⊢)))
-- ⊢₁ⁿ⇒⟶₁₋ (→ₚ₁ⁿI  A⊢B)        = →ₚ₁₋R (⊢₁ⁿ⇒⟶₁₋ A⊢B)
-- ⊢₁ⁿ⇒⟶₁₋ (neut₁ⁿ ⊢A)         = ⊢₁ʳ⇒⟶₁₋⇒⟶₁₋ ⊢A (init₁₋ (here refl))

-- ⊢₁ʳ⇒⟶₁₋⇒⟶₁₋ (pre₁ʳ  A∈)         A⟶ = ⟶₁₋-resp-∈⇒∈ ∈⇒∈ A⟶
--   where
--     ∈⇒∈ : ∀ {B} → B ∈ _ ∷ _ → B ∈ _
--     ∈⇒∈ (here refl) = ∈-++⁺ʳ _ A∈
--     ∈⇒∈ (there B∈)  = ∈-++⁺ʳ _ B∈
-- ⊢₁ʳ⇒⟶₁₋⇒⟶₁₋ (⊥ₚ₁ʳE  ⊢⊥)         _  = ⊢₁ʳ⇒⟶₁₋⇒⟶₁₋ ⊢⊥ (⊥ₚ₁₋L (here refl))
-- ⊢₁ʳ⇒⟶₁₋⇒⟶₁₋ (∧ₚ₁ʳE₁ ⊢A∧B)       A⟶ = ⊢₁ʳ⇒⟶₁₋⇒⟶₁₋ ⊢A∧B (∧ₚ₁₋L₁ (here refl) (⟶₁₋wk {_ ∷ []} A⟶))
-- ⊢₁ʳ⇒⟶₁₋⇒⟶₁₋ (∧ₚ₁ʳE₂ ⊢A∧B)       B⟶ = ⊢₁ʳ⇒⟶₁₋⇒⟶₁₋ ⊢A∧B (∧ₚ₁₋L₂ (here refl) (⟶₁₋wk {_ ∷ []} B⟶))
-- ⊢₁ʳ⇒⟶₁₋⇒⟶₁₋ (→ₚ₁ʳE  ⊢A→B ⊢A)    B⟶ = ⊢₁ʳ⇒⟶₁₋⇒⟶₁₋ ⊢A→B (→ₚ₁₋L (here refl) (⟶₁₋wk {[]} (⊢₁ⁿ⇒⟶₁₋ ⊢A)) (⟶₁₋wk {_ ∷ []} B⟶))

-- -- Consistencies of Systems from Soundness/Completeness
-- ⟶₁-consistency : [] ⟶₁ ⊥ₚ₁ → ⊥
-- ⟶₁-consistency ⟶⊥ = ⟶₁₋-consistency (⟶₁⇒⟶₁₋ ⟶⊥)

-- ⊢₁-consistency : [] ⊢₁ ⊥ₚ₁ → ⊥
-- ⊢₁-consistency ⊢⊥ = ⟶₁-consistency (⊢₁⇒⟶₁ ⊢⊥)

-- ⊢₁ⁿ-consistency : [] ⊢₁ⁿ ⊥ₚ₁ → ⊥
-- ⊢₁ⁿ-consistency ⊢⊥ = ⟶₁₋-consistency (⊢₁ⁿ⇒⟶₁₋ ⊢⊥)

-- ⊢₁ʳ-consistency : [] ⊢₁ʳ ⊥ₚ₁ → ⊥
-- ⊢₁ʳ-consistency ⊢⊥ = ⊢₁ⁿ-consistency (neut₁ⁿ ⊢⊥)

-- -- Weak Normalization of Natural Deduction
-- weak-normalization₁ : Γ ⊢₁ A → Γ ⊢₁ⁿ A
-- weak-normalization₁ ⊢A = ⟶₁₋⇒⊢₁ⁿ (⟶₁⇒⟶₁₋ (⊢₁⇒⟶₁ ⊢A))
