-- Properties of Natural Deduction
open import Logic.First.Signature

module Logic.First.ND.Properties (Sig : Signature₁) where

open import Logic.First.ND Sig

-- ⊢₁ₜ-∈₁ₜ-resp-∈⇒∈ : (∀ {l} → l ∈ Γ → l ∈ Γ′) → Γ ⊢₁ₜ v ∈₁ₜ s → Γ′ ⊢₁ₜ v ∈₁ₜ s
-- ⊢₁ₜ-∈₁ₜ-resp-∈⇒∈ f (var₁ₜ x) = {!var₁ₜ (f x)!}
-- ⊢₁ₜ-∈₁ₜ-resp-∈⇒∈ f unit₁ₜ = {!!}
-- ⊢₁ₜ-∈₁ₜ-resp-∈⇒∈ f zero₁ₜ = {!!}
-- ⊢₁ₜ-∈₁ₜ-resp-∈⇒∈ f (suc₁ₜ ⊢s) = {!!}
-- ⊢₁ₜ-∈₁ₜ-resp-∈⇒∈ f (_$₁ₜ_ ⊢s) = {!!}
-- ⊢₁ₜ-∈₁ₜ-resp-∈⇒∈ f (⊢s ,₁ₜ ⊢s₁) = {!!}

-- ⊢₁-resp-∈⇒∈ : (∀ {l} → l ∈ Γ → l ∈ Γ′) → Γ ⊢₁ B → Γ′ ⊢₁ B
-- ⊢₁-resp-∈⇒∈ f (pre₁  B∈)         = pre₁ (f B∈)
-- ⊢₁-resp-∈⇒∈ f (⊥ₚ₁E  ⊢⊥)         = ⊥ₚ₁E (⊢₁-resp-∈⇒∈ f ⊢⊥)
-- ⊢₁-resp-∈⇒∈ f (∧ₚ₁I  ⊢B ⊢C)      = ∧ₚ₁I (⊢₁-resp-∈⇒∈ f ⊢B) (⊢₁-resp-∈⇒∈ f ⊢C)
-- ⊢₁-resp-∈⇒∈ f (∧ₚ₁E₁ ⊢B∧C)       = ∧ₚ₁E₁ (⊢₁-resp-∈⇒∈ f ⊢B∧C)
-- ⊢₁-resp-∈⇒∈ f (∧ₚ₁E₂ ⊢B∧C)       = ∧ₚ₁E₂ (⊢₁-resp-∈⇒∈ f ⊢B∧C)
-- ⊢₁-resp-∈⇒∈ f (∨ₚ₁I₁ ⊢B)         = ∨ₚ₁I₁ (⊢₁-resp-∈⇒∈ f ⊢B)
-- ⊢₁-resp-∈⇒∈ f (∨ₚ₁I₂ ⊢C)         = ∨ₚ₁I₂ (⊢₁-resp-∈⇒∈ f ⊢C)
-- ⊢₁-resp-∈⇒∈ f (∨ₚ₁E  ⊢B∨C B⊢ C⊢) = ∨ₚ₁E (⊢₁-resp-∈⇒∈ f ⊢B∨C) (⊢₁-resp-∈⇒∈ (∈⇒∈-ext f) B⊢) (⊢₁-resp-∈⇒∈ (∈⇒∈-ext f) C⊢)
-- ⊢₁-resp-∈⇒∈ f (→ₚ₁I  B⊢C)        = →ₚ₁I (⊢₁-resp-∈⇒∈ (∈⇒∈-ext f) B⊢C)
-- ⊢₁-resp-∈⇒∈ f (→ₚ₁E  ⊢B→C ⊢B)    = →ₚ₁E (⊢₁-resp-∈⇒∈ f ⊢B→C) (⊢₁-resp-∈⇒∈ f ⊢B)
-- ⊢₁-resp-∈⇒∈ f (∀ₚ₁I  ⊢B)         = ∀ₚ₁I (⊢₁-resp-∈⇒∈ (∈⇒∈-ext f) ⊢B)
-- ⊢₁-resp-∈⇒∈ f (∀ₚ₁E  ⊢B ⊢s)      = ∀ₚ₁E (⊢₁-resp-∈⇒∈ f ⊢B) (⊢₁ₜ-∈₁ₜ-resp-∈⇒∈ f ⊢s)

-- ⊢₁wk : Γ′ ++ Γ ⊢₁ B → Γ′ ++ l ∷ Γ ⊢₁ B
-- ⊢₁wk {Γ′} ⊢B = ⊢₁-resp-∈⇒∈ (∈-++⇒∈-++-∷ Γ′ _) ⊢B

-- ⊢₁wk′ : Γ′ ++ Γ ⊢₁ A → Γ′ ++ Γ″ ++ Γ ⊢₁ A
-- ⊢₁wk′ {Γ′} ⊢A = ⊢₁-resp-∈⇒∈ (∈-++⇒∈-++-++ Γ′ _) ⊢A

-- ⊢₁ct : Γ′ ++ l ∷ l ∷ Γ ⊢₁ B → Γ′ ++ l ∷ Γ ⊢₁ B
-- ⊢₁ct {Γ′} ⊢B = ⊢₁-resp-∈⇒∈ (∈-++-dedupe₁ Γ′) ⊢B

-- ⊢₁ex : Γ′ ++ l ∷ m ∷ Γ ⊢₁ C → Γ′ ++ m ∷ l ∷ Γ ⊢₁ C
-- ⊢₁ex {Γ′} ⊢C = ⊢₁-resp-∈⇒∈ (∈-++-swap Γ′) ⊢C

-- ⊢₁-subst : Γ′ ++ A ∷ Γ ⊢₁ B → Γ ⊢₁ A → Γ′ ++ Γ ⊢₁ B
-- ⊢₁-subst {Γ′} (pre₁  B∈)         ⊢A = ⊢B
--   where
--     ⊢B : _ ⊢₁ _
--     ⊢B
--       with ∈-++⁻ Γ′ B∈
--     ...  | inj₁ B∈Γ′        = pre₁ (∈-++⁺ˡ B∈Γ′)
--     ...  | inj₂ (here refl) = ⊢₁wk′ {[]} ⊢A
--     ...  | inj₂ (there B∈Γ) = pre₁ (∈-++⁺ʳ Γ′ B∈Γ)
-- ⊢₁-subst      (⊥ₚ₁E  ⊢⊥)         ⊢A = ⊥ₚ₁E (⊢₁-subst ⊢⊥ ⊢A)
-- ⊢₁-subst      (∧ₚ₁I  ⊢B ⊢C)      ⊢A = ∧ₚ₁I (⊢₁-subst ⊢B ⊢A) (⊢₁-subst ⊢C ⊢A)
-- ⊢₁-subst      (∧ₚ₁E₁ ⊢B∧C)       ⊢A = ∧ₚ₁E₁ (⊢₁-subst ⊢B∧C ⊢A)
-- ⊢₁-subst      (∧ₚ₁E₂ ⊢B∧C)       ⊢A = ∧ₚ₁E₂ (⊢₁-subst ⊢B∧C ⊢A)
-- ⊢₁-subst      (∨ₚ₁I₁ ⊢B)         ⊢A = ∨ₚ₁I₁ (⊢₁-subst ⊢B ⊢A)
-- ⊢₁-subst      (∨ₚ₁I₂ ⊢C)         ⊢A = ∨ₚ₁I₂ (⊢₁-subst ⊢C ⊢A)
-- ⊢₁-subst      (∨ₚ₁E  ⊢B∨C B⊢ C⊢) ⊢A = ∨ₚ₁E (⊢₁-subst ⊢B∨C ⊢A) (⊢₁-subst B⊢ ⊢A) (⊢₁-subst C⊢ ⊢A)
-- ⊢₁-subst      (→ₚ₁I  B⊢C)        ⊢A = →ₚ₁I (⊢₁-subst B⊢C ⊢A)
-- ⊢₁-subst      (→ₚ₁E  ⊢B→C ⊢B)    ⊢A = →ₚ₁E (⊢₁-subst ⊢B→C ⊢A) (⊢₁-subst ⊢B ⊢A)
