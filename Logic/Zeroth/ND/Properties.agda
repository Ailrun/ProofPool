-- Properties of Natural Deduction
module Logic.Zeroth.ND.Properties where

open import Logic.Zeroth.ND

⊢₀-resp-∈⇒∈ : (∀ {A} → A ∈ Γ → A ∈ Γ′) → Γ ⊢₀ B → Γ′ ⊢₀ B
⊢₀-resp-∈⇒∈ f (pre₀  B∈)         = pre₀ (f B∈)
⊢₀-resp-∈⇒∈ f (⊥ₚ₀E  ⊢⊥)         = ⊥ₚ₀E (⊢₀-resp-∈⇒∈ f ⊢⊥)
⊢₀-resp-∈⇒∈ f (∧ₚ₀I  ⊢B ⊢C)      = ∧ₚ₀I (⊢₀-resp-∈⇒∈ f ⊢B) (⊢₀-resp-∈⇒∈ f ⊢C)
⊢₀-resp-∈⇒∈ f (∧ₚ₀E₁ ⊢B∧C)       = ∧ₚ₀E₁ (⊢₀-resp-∈⇒∈ f ⊢B∧C)
⊢₀-resp-∈⇒∈ f (∧ₚ₀E₂ ⊢B∧C)       = ∧ₚ₀E₂ (⊢₀-resp-∈⇒∈ f ⊢B∧C)
⊢₀-resp-∈⇒∈ f (∨ₚ₀I₁ ⊢B)         = ∨ₚ₀I₁ (⊢₀-resp-∈⇒∈ f ⊢B)
⊢₀-resp-∈⇒∈ f (∨ₚ₀I₂ ⊢C)         = ∨ₚ₀I₂ (⊢₀-resp-∈⇒∈ f ⊢C)
⊢₀-resp-∈⇒∈ f (∨ₚ₀E  ⊢B∨C B⊢ C⊢) = ∨ₚ₀E (⊢₀-resp-∈⇒∈ f ⊢B∨C) (⊢₀-resp-∈⇒∈ (∈⇒∈-ext f) B⊢) (⊢₀-resp-∈⇒∈ (∈⇒∈-ext f) C⊢)
⊢₀-resp-∈⇒∈ f (→ₚ₀I  B⊢C)        = →ₚ₀I (⊢₀-resp-∈⇒∈ (∈⇒∈-ext f) B⊢C)
⊢₀-resp-∈⇒∈ f (→ₚ₀E  ⊢B→C ⊢B)    = →ₚ₀E (⊢₀-resp-∈⇒∈ f ⊢B→C) (⊢₀-resp-∈⇒∈ f ⊢B)

⊢₀wk : Γ′ ++ Γ ⊢₀ B → Γ′ ++ A ∷ Γ ⊢₀ B
⊢₀wk {Γ′} ⊢B = ⊢₀-resp-∈⇒∈ (∈-++⇒∈-++-∷ Γ′ _) ⊢B

⊢₀wk′ : Γ′ ++ Γ ⊢₀ A → Γ′ ++ Γ″ ++ Γ ⊢₀ A
⊢₀wk′ {Γ′} ⊢A = ⊢₀-resp-∈⇒∈ (∈-++⇒∈-++-++ Γ′ _) ⊢A

⊢₀ct : Γ′ ++ A ∷ A ∷ Γ ⊢₀ B → Γ′ ++ A ∷ Γ ⊢₀ B
⊢₀ct {Γ′} ⊢B = ⊢₀-resp-∈⇒∈ (∈-++-dedupe₁ Γ′) ⊢B

⊢₀ex : Γ′ ++ A ∷ B ∷ Γ ⊢₀ C → Γ′ ++ B ∷ A ∷ Γ ⊢₀ C
⊢₀ex {Γ′} ⊢C = ⊢₀-resp-∈⇒∈ (∈-++-swap Γ′) ⊢C

⊢₀-subst : Γ′ ++ A ∷ Γ ⊢₀ B → Γ ⊢₀ A → Γ′ ++ Γ ⊢₀ B
⊢₀-subst {Γ′} (pre₀  B∈)         ⊢A = ⊢B
  where
    ⊢B : _ ⊢₀ _
    ⊢B
      with ∈-++⁻ Γ′ B∈
    ...  | inj₁ B∈Γ′        = pre₀ (∈-++⁺ˡ B∈Γ′)
    ...  | inj₂ (here refl) = ⊢₀wk′ {[]} ⊢A
    ...  | inj₂ (there B∈Γ) = pre₀ (∈-++⁺ʳ Γ′ B∈Γ)
⊢₀-subst      (⊥ₚ₀E  ⊢⊥)         ⊢A = ⊥ₚ₀E (⊢₀-subst ⊢⊥ ⊢A)
⊢₀-subst      (∧ₚ₀I  ⊢B ⊢C)      ⊢A = ∧ₚ₀I (⊢₀-subst ⊢B ⊢A) (⊢₀-subst ⊢C ⊢A)
⊢₀-subst      (∧ₚ₀E₁ ⊢B∧C)       ⊢A = ∧ₚ₀E₁ (⊢₀-subst ⊢B∧C ⊢A)
⊢₀-subst      (∧ₚ₀E₂ ⊢B∧C)       ⊢A = ∧ₚ₀E₂ (⊢₀-subst ⊢B∧C ⊢A)
⊢₀-subst      (∨ₚ₀I₁ ⊢B)         ⊢A = ∨ₚ₀I₁ (⊢₀-subst ⊢B ⊢A)
⊢₀-subst      (∨ₚ₀I₂ ⊢C)         ⊢A = ∨ₚ₀I₂ (⊢₀-subst ⊢C ⊢A)
⊢₀-subst      (∨ₚ₀E  ⊢B∨C B⊢ C⊢) ⊢A = ∨ₚ₀E (⊢₀-subst ⊢B∨C ⊢A) (⊢₀-subst B⊢ ⊢A) (⊢₀-subst C⊢ ⊢A)
⊢₀-subst      (→ₚ₀I  B⊢C)        ⊢A = →ₚ₀I (⊢₀-subst B⊢C ⊢A)
⊢₀-subst      (→ₚ₀E  ⊢B→C ⊢B)    ⊢A = →ₚ₀E (⊢₀-subst ⊢B→C ⊢A) (⊢₀-subst ⊢B ⊢A)
