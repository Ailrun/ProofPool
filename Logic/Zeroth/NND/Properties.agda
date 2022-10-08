-- Properties of Normal Natural Deduction
module Logic.Zeroth.NND.Properties where

open import Logic.Zeroth.Base
open import Logic.Zeroth.NND

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

⊢₀ⁿ-subst : Γ′ ++ A ∷ Γ ⊢₀ⁿ B → Γ ⊢₀ʳ A → Γ′ ++ Γ ⊢₀ⁿ B
⊢₀ʳ-subst : Γ′ ++ A ∷ Γ ⊢₀ʳ B → Γ ⊢₀ʳ A → Γ′ ++ Γ ⊢₀ʳ B

⊢₀ⁿ-subst      (∧ₚ₀ⁿI ⊢B ⊢C)      ⊢A = ∧ₚ₀ⁿI (⊢₀ⁿ-subst ⊢B ⊢A) (⊢₀ⁿ-subst ⊢C ⊢A)
⊢₀ⁿ-subst      (∨ₚ₀ⁿI₁ ⊢B)        ⊢A = ∨ₚ₀ⁿI₁ (⊢₀ⁿ-subst ⊢B ⊢A)
⊢₀ⁿ-subst      (∨ₚ₀ⁿI₂ ⊢C)        ⊢A = ∨ₚ₀ⁿI₂ (⊢₀ⁿ-subst ⊢C ⊢A)
⊢₀ⁿ-subst      (∨ₚ₀ⁿE ⊢B∨C B⊢ C⊢) ⊢A = ∨ₚ₀ⁿE (⊢₀ʳ-subst ⊢B∨C ⊢A) (⊢₀ⁿ-subst B⊢ ⊢A) (⊢₀ⁿ-subst C⊢ ⊢A)
⊢₀ⁿ-subst      (→ₚ₀ⁿI B⊢C)        ⊢A = →ₚ₀ⁿI (⊢₀ⁿ-subst B⊢C ⊢A)
⊢₀ⁿ-subst      (neut₀ⁿ ⊢B)        ⊢A = neut₀ⁿ (⊢₀ʳ-subst ⊢B ⊢A)

⊢₀ʳ-subst {Γ′} (pre₀ʳ B∈)         ⊢A = ⊢B
  where
    ⊢B : _ ⊢₀ʳ _
    ⊢B
      with ∈-++⁻ Γ′ B∈
    ...  | inj₁ B∈Γ′        = pre₀ʳ (∈-++⁺ˡ B∈Γ′)
    ...  | inj₂ (here refl) = ⊢₀ʳwk′ {[]} ⊢A
    ...  | inj₂ (there B∈Γ) = pre₀ʳ (∈-++⁺ʳ Γ′ B∈Γ)
⊢₀ʳ-subst      (⊥ₚ₀ʳE ⊢⊥)         ⊢A = ⊥ₚ₀ʳE (⊢₀ʳ-subst ⊢⊥ ⊢A)
⊢₀ʳ-subst      (∧ₚ₀ʳE₁ ⊢B∧C)      ⊢A = ∧ₚ₀ʳE₁ (⊢₀ʳ-subst ⊢B∧C ⊢A)
⊢₀ʳ-subst      (∧ₚ₀ʳE₂ ⊢B∧C)      ⊢A = ∧ₚ₀ʳE₂ (⊢₀ʳ-subst ⊢B∧C ⊢A)
⊢₀ʳ-subst      (→ₚ₀ʳE ⊢B→C ⊢B)    ⊢A = →ₚ₀ʳE (⊢₀ʳ-subst ⊢B→C ⊢A) (⊢₀ⁿ-subst ⊢B ⊢A)
