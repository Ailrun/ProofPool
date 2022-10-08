module Logic.Zeroth.Properties where

open import Logic.Zeroth.Base
open import Logic.Zeroth.ND
open import Logic.Zeroth.NND
open import Logic.Zeroth.SC
open import Logic.Zeroth.SCC

⊢₀-subst : Γ′ ++ A ∷ Γ ⊢₀ B → Γ ⊢₀ A → Γ′ ++ Γ ⊢₀ B
⊢₀-subst {Γ′} (pre₀ B∈)         ⊢A = ⊢B
  where
    ⊢B : _ ⊢₀ _
    ⊢B
      with ∈-++⁻ Γ′ B∈
    ...  | inj₁ B∈Γ′        = pre₀ (∈-++⁺ˡ B∈Γ′)
    ...  | inj₂ (here refl) = ⊢₀wk′ {[]} ⊢A
    ...  | inj₂ (there B∈Γ) = pre₀ (∈-++⁺ʳ Γ′ B∈Γ)
⊢₀-subst      (⊥ₚ₀E ⊢⊥)         ⊢A = ⊥ₚ₀E (⊢₀-subst ⊢⊥ ⊢A)
⊢₀-subst      (∧ₚ₀I ⊢B ⊢C)      ⊢A = ∧ₚ₀I (⊢₀-subst ⊢B ⊢A) (⊢₀-subst ⊢C ⊢A)
⊢₀-subst      (∧ₚ₀E₁ ⊢B∧C)      ⊢A = ∧ₚ₀E₁ (⊢₀-subst ⊢B∧C ⊢A)
⊢₀-subst      (∧ₚ₀E₂ ⊢B∧C)      ⊢A = ∧ₚ₀E₂ (⊢₀-subst ⊢B∧C ⊢A)
⊢₀-subst      (∨ₚ₀I₁ ⊢B)        ⊢A = ∨ₚ₀I₁ (⊢₀-subst ⊢B ⊢A)
⊢₀-subst      (∨ₚ₀I₂ ⊢C)        ⊢A = ∨ₚ₀I₂ (⊢₀-subst ⊢C ⊢A)
⊢₀-subst      (∨ₚ₀E ⊢B∨C B⊢ C⊢) ⊢A = ∨ₚ₀E (⊢₀-subst ⊢B∨C ⊢A) (⊢₀-subst B⊢ ⊢A) (⊢₀-subst C⊢ ⊢A)
⊢₀-subst      (→ₚ₀I B⊢C)        ⊢A = →ₚ₀I (⊢₀-subst B⊢C ⊢A)
⊢₀-subst      (→ₚ₀E ⊢B→C ⊢B)    ⊢A = →ₚ₀E (⊢₀-subst ⊢B→C ⊢A) (⊢₀-subst ⊢B ⊢A)

⊢₀⇒⟶₀ : Γ ⊢₀ A → Γ ⟶₀ A
⊢₀⇒⟶₀ (pre₀ A∈)         = init₀ A∈
⊢₀⇒⟶₀ (⊥ₚ₀E ⊢⊥)         = cut₀ (⊢₀⇒⟶₀ ⊢⊥) (⊥ₚ₀L (here refl))
⊢₀⇒⟶₀ (∧ₚ₀I ⊢A ⊢B)      = ∧ₚ₀R (⊢₀⇒⟶₀ ⊢A) (⊢₀⇒⟶₀ ⊢B)
⊢₀⇒⟶₀ (∧ₚ₀E₁ ⊢A∧B)      = cut₀ (⊢₀⇒⟶₀ ⊢A∧B) (∧ₚ₀L₁ (here refl) (init₀ (here refl)))
⊢₀⇒⟶₀ (∧ₚ₀E₂ ⊢A∧B)      = cut₀ (⊢₀⇒⟶₀ ⊢A∧B) (∧ₚ₀L₂ (here refl) (init₀ (here refl)))
⊢₀⇒⟶₀ (∨ₚ₀I₁ ⊢A)        = ∨ₚ₀R₁ (⊢₀⇒⟶₀ ⊢A)
⊢₀⇒⟶₀ (∨ₚ₀I₂ ⊢B)        = ∨ₚ₀R₂ (⊢₀⇒⟶₀ ⊢B)
⊢₀⇒⟶₀ (∨ₚ₀E ⊢A∨B A⊢ B⊢) = cut₀ (⊢₀⇒⟶₀ ⊢A∨B) (∨ₚ₀L (here refl) (⟶₀wk {_ ∷ []} (⊢₀⇒⟶₀ A⊢)) (⟶₀wk {_ ∷ []} (⊢₀⇒⟶₀ B⊢)))
⊢₀⇒⟶₀ (→ₚ₀I A⊢B)        = →ₚ₀R (⊢₀⇒⟶₀ A⊢B)
⊢₀⇒⟶₀ (→ₚ₀E ⊢A→B ⊢A)    = cut₀ (⊢₀⇒⟶₀ ⊢A→B) (→ₚ₀L (here refl) (⟶₀wk {[]} (⊢₀⇒⟶₀ ⊢A)) (init₀ (here refl)))

⟶₀⇒⊢₀ : Γ ⟶₀ A → Γ ⊢₀ A
⟶₀⇒⊢₀ (init₀ A∈)        = pre₀ A∈
⟶₀⇒⊢₀ (⊥ₚ₀L ⊥∈)         = ⊥ₚ₀E (pre₀ ⊥∈)
⟶₀⇒⊢₀ (∧ₚ₀R ⟶A ⟶B)      = ∧ₚ₀I (⟶₀⇒⊢₀ ⟶A) (⟶₀⇒⊢₀ ⟶B)
⟶₀⇒⊢₀ (∧ₚ₀L₁ A∧B∈ A⟶)   = ⊢₀-subst {[]} (⟶₀⇒⊢₀ A⟶) (∧ₚ₀E₁ (pre₀ A∧B∈))
⟶₀⇒⊢₀ (∧ₚ₀L₂ A∧B∈ B⟶)   = ⊢₀-subst {[]} (⟶₀⇒⊢₀ B⟶) (∧ₚ₀E₂ (pre₀ A∧B∈))
⟶₀⇒⊢₀ (∨ₚ₀R₁ ⟶A)        = ∨ₚ₀I₁ (⟶₀⇒⊢₀ ⟶A)
⟶₀⇒⊢₀ (∨ₚ₀R₂ ⟶B)        = ∨ₚ₀I₂ (⟶₀⇒⊢₀ ⟶B)
⟶₀⇒⊢₀ (∨ₚ₀L A∨B∈ A⟶ B⟶) = ∨ₚ₀E (pre₀ A∨B∈) (⟶₀⇒⊢₀ A⟶) (⟶₀⇒⊢₀ B⟶)
⟶₀⇒⊢₀ (→ₚ₀R A⟶B)        = →ₚ₀I (⟶₀⇒⊢₀ A⟶B)
⟶₀⇒⊢₀ (→ₚ₀L A→B∈ ⟶A B⟶) = ⊢₀-subst {[]} (⟶₀⇒⊢₀ B⟶) (→ₚ₀E (pre₀ A→B∈) (⟶₀⇒⊢₀ ⟶A))
⟶₀⇒⊢₀ (cut₀ ⟶A A⟶)      = ∨ₚ₀E (∨ₚ₀I₁ (⟶₀⇒⊢₀ ⟶A)) (⟶₀⇒⊢₀ A⟶) (⟶₀⇒⊢₀ A⟶)

⟶₀₋-consistency : [] ⟶₀₋ ⊥ₚ₀ → ⊥
⟶₀₋-consistency (init₀₋ ())
⟶₀₋-consistency (⊥ₚ₀₋L ())
⟶₀₋-consistency (∧ₚ₀₋L₁ () _)
⟶₀₋-consistency (∧ₚ₀₋L₂ () _)
⟶₀₋-consistency (∨ₚ₀₋L () _ _)
⟶₀₋-consistency (→ₚ₀₋L () _ _)

⟶₀₋⇒⟶₀ : Γ ⟶₀₋ A → Γ ⟶₀ A
⟶₀₋⇒⟶₀ (init₀₋ A∈)        = init₀ A∈
⟶₀₋⇒⟶₀ (⊥ₚ₀₋L ⊥∈)         = ⊥ₚ₀L ⊥∈
⟶₀₋⇒⟶₀ (∧ₚ₀₋R ⟶A ⟶B)      = ∧ₚ₀R (⟶₀₋⇒⟶₀ ⟶A) (⟶₀₋⇒⟶₀ ⟶B)
⟶₀₋⇒⟶₀ (∧ₚ₀₋L₁ A∧B∈ A⟶)   = ∧ₚ₀L₁ A∧B∈ (⟶₀₋⇒⟶₀ A⟶)
⟶₀₋⇒⟶₀ (∧ₚ₀₋L₂ A∧B∈ B⟶)   = ∧ₚ₀L₂ A∧B∈ (⟶₀₋⇒⟶₀ B⟶)
⟶₀₋⇒⟶₀ (∨ₚ₀₋R₁ ⟶A)        = ∨ₚ₀R₁ (⟶₀₋⇒⟶₀ ⟶A)
⟶₀₋⇒⟶₀ (∨ₚ₀₋R₂ ⟶B)        = ∨ₚ₀R₂ (⟶₀₋⇒⟶₀ ⟶B)
⟶₀₋⇒⟶₀ (∨ₚ₀₋L A∨B∈ A⟶ B⟶) = ∨ₚ₀L A∨B∈ (⟶₀₋⇒⟶₀ A⟶) (⟶₀₋⇒⟶₀ B⟶)
⟶₀₋⇒⟶₀ (→ₚ₀₋R A⟶B)        = →ₚ₀R (⟶₀₋⇒⟶₀ A⟶B)
⟶₀₋⇒⟶₀ (→ₚ₀₋L A→B∈ ⟶A B⟶) = →ₚ₀L A→B∈ (⟶₀₋⇒⟶₀ ⟶A) (⟶₀₋⇒⟶₀ B⟶)

module _ where
  private
    _<ₗₑₓ_ = WfLex.×-Lex _≡_ (_<_ on size-P₀) (WfLex.×-Lex _≡_ _<_ _<_)

    <ₗₑₓ-of₀ : ∀ {Aₗ Aᵣ szₗ szᵣ szₗ′ szᵣ′} → size-P₀ Aₗ < size-P₀ Aᵣ → (Aₗ , szₗ , szₗ′) <ₗₑₓ (Aᵣ , szᵣ , szᵣ′)
    <ₗₑₓ-of₀ <-prf = inj₁ <-prf

    <ₗₑₓ-of₁ : ∀ {szₗ szᵣ szₗ′ szᵣ′} → szₗ < szᵣ → (A , szₗ , szₗ′) <ₗₑₓ (A , szᵣ , szᵣ′)
    <ₗₑₓ-of₁ <-prf = inj₂ (refl , inj₁ <-prf)

    <ₗₑₓ-of₂ : ∀ {sz szₗ′ szᵣ′} → szₗ′ < szᵣ′ → (A , sz , szₗ′) <ₗₑₓ (A , sz , szᵣ′)
    <ₗₑₓ-of₂ <-prf = inj₂ (refl , inj₂ (refl , <-prf))

    cut-goal : P₀ × ℕ × ℕ → Set
    cut-goal (A , sz , sz′) =
      ∀ {Γ E} (Seq : Γ ⟶₀₋ A) (Seq′ : A ∷ Γ ⟶₀₋ E) →
      sz ≡ size-⟶₀₋ Seq →
      sz′ ≡ size-⟶₀₋ Seq′ → 
      Γ ⟶₀₋ E

    module _ trip (rec : ∀ {A Γ B Γ′ C} (Seq : Γ ⟶₀₋ B) (Seq′ : Γ′ ⟶₀₋ C) → (A , size-⟶₀₋ Seq , size-⟶₀₋ Seq′) <ₗₑₓ trip → cut-goal (A , size-⟶₀₋ Seq , size-⟶₀₋ Seq′)) where
      rec-structural : ∀ {Γ A E} → (Seq : Γ ⟶₀₋ A) (Seq′ : A ∷ Γ ⟶₀₋ E) → (A , size-⟶₀₋ Seq , size-⟶₀₋ Seq′) <ₗₑₓ trip → Γ ⟶₀₋ E
      rec-structural Seq Seq′ ord = rec Seq Seq′ ord Seq Seq′ refl refl

      rec-wk/ex      : ∀ {Γ A B E} → (Seq : Γ ⟶₀₋ A) (Seq′ : B ∷ A ∷ Γ ⟶₀₋ E) → (A , size-⟶₀₋ Seq , size-⟶₀₋ Seq′) <ₗₑₓ trip → B ∷ Γ ⟶₀₋ E
      rec-wk/ex      Seq Seq′ ord = rec Seq Seq′ ord (⟶₀₋wk {[]} Seq) (⟶₀₋ex {[]} Seq′) (⟶₀₋wk-preserves-size-⟶₀₋ {[]} Seq) (⟶₀₋ex-preserves-size-⟶₀₋ {[]} Seq′)

      cut-elimination₀-gen : cut-goal trip
      cut-elimination₀-gen (init₀₋ A∈)        A⟶                         refl refl = ⟶₀₋-resp-∈⇒∈ ∈⇒∈ A⟶
        where
          ∈⇒∈ : ∀ {B} → B ∈ proj₁ trip ∷ _ → B ∈ _
          ∈⇒∈ (here refl) = ∈-++⁺ʳ _ A∈
          ∈⇒∈ (there B∈)  = ∈-++⁺ʳ _ B∈
      cut-elimination₀-gen (⊥ₚ₀₋L ⊥∈)         A⟶                         refl refl = ⊥ₚ₀₋L ⊥∈
      cut-elimination₀-gen (∧ₚ₀₋L₁ A∧B∈ A⟶)   C⟶                         refl refl = ∧ₚ₀₋L₁ A∧B∈ (rec-structural A⟶ (⟶₀₋wk {_ ∷ []} C⟶) (<ₗₑₓ-of₁ ≤-refl))
      cut-elimination₀-gen (∧ₚ₀₋L₂ A∧B∈ B⟶)   C⟶                         refl refl = ∧ₚ₀₋L₂ A∧B∈ (rec-structural B⟶ (⟶₀₋wk {_ ∷ []} C⟶) (<ₗₑₓ-of₁ ≤-refl))
      cut-elimination₀-gen (∨ₚ₀₋L A∨B∈ A⟶ B⟶) C⟶                         refl refl = ∨ₚ₀₋L A∨B∈
                                                                                       (rec-structural A⟶ (⟶₀₋wk {_ ∷ []} C⟶) (<ₗₑₓ-of₁ (m≤m+n _ _)))
                                                                                       (rec-structural B⟶ (⟶₀₋wk {_ ∷ []} C⟶) (<ₗₑₓ-of₁ (s≤s (m≤n+m _ _))))
      cut-elimination₀-gen (→ₚ₀₋L A→B∈ ⟶A B⟶) C⟶                         refl refl = →ₚ₀₋L A→B∈ ⟶A (rec-structural B⟶ (⟶₀₋wk {_ ∷ []} C⟶) (<ₗₑₓ-of₁ (s≤s (m≤n+m _ _))))
      cut-elimination₀-gen ⟶A∧B@(∧ₚ₀₋R ⟶A ⟶B) (∧ₚ₀₋L₁ (here refl) A⟶)    refl refl = rec-structural ⟶A A⟶E (<ₗₑₓ-of₀ (m≤m+n _ _))
        where
          A⟶E = rec-wk/ex ⟶A∧B A⟶ (<ₗₑₓ-of₂ ≤-refl)
      cut-elimination₀-gen ⟶A∧B@(∧ₚ₀₋R _  _)  (∧ₚ₀₋L₁ (there C∧D∈) C⟶)   refl refl = ∧ₚ₀₋L₁ C∧D∈ (rec-wk/ex ⟶A∧B C⟶ (<ₗₑₓ-of₂ ≤-refl))
      cut-elimination₀-gen ⟶A∧B@(∧ₚ₀₋R ⟶A ⟶B) (∧ₚ₀₋L₂ (here refl) B⟶)    refl refl = rec-structural ⟶B B⟶E (<ₗₑₓ-of₀ (s≤s (m≤n+m _ _)))
        where
          B⟶E = rec-wk/ex ⟶A∧B B⟶ (<ₗₑₓ-of₂ ≤-refl)
      cut-elimination₀-gen ⟶A∧B@(∧ₚ₀₋R _  _)  (∧ₚ₀₋L₂ (there C∧D∈) D⟶)   refl refl = ∧ₚ₀₋L₂ C∧D∈ (rec-wk/ex ⟶A∧B D⟶ (<ₗₑₓ-of₂ ≤-refl))
      cut-elimination₀-gen ⟶A∧B@(∧ₚ₀₋R _  _)  (∨ₚ₀₋L (there C∨D∈) C⟶ D⟶) refl refl = ∨ₚ₀₋L C∨D∈
                                                                                       (rec-wk/ex ⟶A∧B C⟶ (<ₗₑₓ-of₂ (m≤m+n _ _)))
                                                                                       (rec-wk/ex ⟶A∧B D⟶ (<ₗₑₓ-of₂ (s≤s (m≤n+m _ _))))
      cut-elimination₀-gen ⟶A∧B@(∧ₚ₀₋R _  _)  (→ₚ₀₋L (there C→D∈) ⟶C D⟶) refl refl = →ₚ₀₋L C→D∈
                                                                                       (rec-structural ⟶A∧B ⟶C (<ₗₑₓ-of₂ (m≤m+n _ _)))
                                                                                       (rec-wk/ex ⟶A∧B D⟶ (<ₗₑₓ-of₂ (s≤s (m≤n+m _ _))))
      cut-elimination₀-gen ⟶A∨B@(∨ₚ₀₋R₁ _)    (∧ₚ₀₋L₁ (there C∧D∈) C⟶)   refl refl = ∧ₚ₀₋L₁ C∧D∈ (rec-wk/ex ⟶A∨B C⟶ (<ₗₑₓ-of₂ ≤-refl))
      cut-elimination₀-gen ⟶A∨B@(∨ₚ₀₋R₁ _)    (∧ₚ₀₋L₂ (there C∧D∈) D⟶)   refl refl = ∧ₚ₀₋L₂ C∧D∈ (rec-wk/ex ⟶A∨B D⟶ (<ₗₑₓ-of₂ ≤-refl))
      cut-elimination₀-gen ⟶A∨B@(∨ₚ₀₋R₁ ⟶A)   (∨ₚ₀₋L (here refl) A⟶ B⟶)  refl refl = rec-structural ⟶A A⟶E (<ₗₑₓ-of₀ (m≤m+n _ _))
        where
          A⟶E = rec-wk/ex ⟶A∨B A⟶ (<ₗₑₓ-of₂ (m≤m+n _ _))
      cut-elimination₀-gen ⟶A∨B@(∨ₚ₀₋R₁ _)    (∨ₚ₀₋L (there C∨D∈) C⟶ D⟶) refl refl = ∨ₚ₀₋L C∨D∈
                                                                                       (rec-wk/ex ⟶A∨B C⟶ (<ₗₑₓ-of₂ (m≤m+n _ _)))
                                                                                       (rec-wk/ex ⟶A∨B D⟶ (<ₗₑₓ-of₂ (s≤s (m≤n+m _ _))))
      cut-elimination₀-gen ⟶A∨B@(∨ₚ₀₋R₁ _)    (→ₚ₀₋L (there C→D∈) ⟶C D⟶) refl refl = →ₚ₀₋L C→D∈
                                                                                       (rec-structural ⟶A∨B ⟶C (<ₗₑₓ-of₂ (m≤m+n _ _)))
                                                                                       (rec-wk/ex ⟶A∨B D⟶ (<ₗₑₓ-of₂ (s≤s (m≤n+m _ _))))
      cut-elimination₀-gen ⟶A∨B@(∨ₚ₀₋R₂ _)    (∧ₚ₀₋L₁ (there C∧D∈) C⟶)   refl refl = ∧ₚ₀₋L₁ C∧D∈ (rec-wk/ex ⟶A∨B C⟶ (<ₗₑₓ-of₂ ≤-refl))
      cut-elimination₀-gen ⟶A∨B@(∨ₚ₀₋R₂ _)    (∧ₚ₀₋L₂ (there C∧D∈) D⟶)   refl refl = ∧ₚ₀₋L₂ C∧D∈ (rec-wk/ex ⟶A∨B D⟶ (<ₗₑₓ-of₂ ≤-refl))
      cut-elimination₀-gen ⟶A∨B@(∨ₚ₀₋R₂ ⟶B)   (∨ₚ₀₋L (here refl) A⟶ B⟶)  refl refl = rec-structural ⟶B B⟶E (<ₗₑₓ-of₀ (s≤s (m≤n+m _ _)))
        where
          B⟶E = rec-wk/ex ⟶A∨B B⟶ (<ₗₑₓ-of₂ (s≤s (m≤n+m _ _)))
      cut-elimination₀-gen ⟶A∨B@(∨ₚ₀₋R₂ _)    (∨ₚ₀₋L (there C∨D∈) C⟶ D⟶) refl refl = ∨ₚ₀₋L C∨D∈
                                                                                       (rec-wk/ex ⟶A∨B C⟶ (<ₗₑₓ-of₂ (m≤m+n _ _)))
                                                                                       (rec-wk/ex ⟶A∨B D⟶ (<ₗₑₓ-of₂ (s≤s (m≤n+m _ _))))
      cut-elimination₀-gen ⟶A∨B@(∨ₚ₀₋R₂ _)    (→ₚ₀₋L (there C→D∈) ⟶C D⟶) refl refl = →ₚ₀₋L C→D∈
                                                                                       (rec-structural ⟶A∨B ⟶C (<ₗₑₓ-of₂ (m≤m+n _ _)))
                                                                                       (rec-wk/ex ⟶A∨B D⟶ (<ₗₑₓ-of₂ (s≤s (m≤n+m _ _))))
      cut-elimination₀-gen ⟶A→B@(→ₚ₀₋R _)     (∧ₚ₀₋L₁ (there C∧D∈) C⟶)   refl refl = ∧ₚ₀₋L₁ C∧D∈ (rec-wk/ex ⟶A→B C⟶ (<ₗₑₓ-of₂ ≤-refl))
      cut-elimination₀-gen ⟶A→B@(→ₚ₀₋R _)     (∧ₚ₀₋L₂ (there C∧D∈) D⟶)   refl refl = ∧ₚ₀₋L₂ C∧D∈ (rec-wk/ex ⟶A→B D⟶ (<ₗₑₓ-of₂ ≤-refl))
      cut-elimination₀-gen ⟶A→B@(→ₚ₀₋R _)     (∨ₚ₀₋L (there C∨D∈) C⟶ D⟶) refl refl = ∨ₚ₀₋L C∨D∈
                                                                                       (rec-wk/ex ⟶A→B C⟶ (<ₗₑₓ-of₂ (m≤m+n _ _)))
                                                                                       (rec-wk/ex ⟶A→B D⟶ (<ₗₑₓ-of₂ (s≤s (m≤n+m _ _))))
      cut-elimination₀-gen ⟶A→B@(→ₚ₀₋R A⟶B)   (→ₚ₀₋L (here refl) ⟶A B⟶)  refl refl = rec-structural ⟶B B⟶E (<ₗₑₓ-of₀ (s≤s (m≤n+m _ _)))
        where
          ⟶A′ = rec-structural ⟶A→B ⟶A (<ₗₑₓ-of₂ (m≤m+n _ _))
          ⟶B  = rec-structural ⟶A′ A⟶B (<ₗₑₓ-of₀ (m≤m+n _ _))
          B⟶E = rec-wk/ex ⟶A→B B⟶ (<ₗₑₓ-of₂ (s≤s (m≤n+m _ _)))
      cut-elimination₀-gen ⟶A→B@(→ₚ₀₋R _)     (→ₚ₀₋L (there C→D∈) ⟶C D⟶) refl refl = →ₚ₀₋L C→D∈
                                                                                       (rec-structural ⟶A→B ⟶C (<ₗₑₓ-of₂ (m≤m+n _ _)))
                                                                                       (rec-wk/ex ⟶A→B D⟶ (<ₗₑₓ-of₂ (s≤s (m≤n+m _ _))))
      cut-elimination₀-gen ⟶A                 (init₀₋ (here refl))       refl refl = ⟶A
      cut-elimination₀-gen ⟶A                 (init₀₋ (there D∈))        refl refl = init₀₋ D∈
      cut-elimination₀-gen ⟶A                 (⊥ₚ₀₋L (there ⊥∈))         refl refl = ⊥ₚ₀₋L ⊥∈
      cut-elimination₀-gen ⟶A                 (∧ₚ₀₋R ⟶C ⟶D)              refl refl = ∧ₚ₀₋R
                                                                                       (rec-structural ⟶A ⟶C (<ₗₑₓ-of₂ (m≤m+n _ _)))
                                                                                       (rec-structural ⟶A ⟶D (<ₗₑₓ-of₂ (s≤s (m≤n+m _ _))))
      cut-elimination₀-gen ⟶A                 (∨ₚ₀₋R₁ ⟶C)                refl refl = ∨ₚ₀₋R₁ (rec-structural ⟶A ⟶C (<ₗₑₓ-of₂ ≤-refl))
      cut-elimination₀-gen ⟶A                 (∨ₚ₀₋R₂ ⟶D)                refl refl = ∨ₚ₀₋R₂ (rec-structural ⟶A ⟶D (<ₗₑₓ-of₂ ≤-refl))
      cut-elimination₀-gen ⟶A                 (→ₚ₀₋R C⟶D)                refl refl = →ₚ₀₋R (rec-wk/ex ⟶A C⟶D (<ₗₑₓ-of₂ ≤-refl))

  cut-elimination₀ : Γ ⟶₀₋ A → A ∷ Γ ⟶₀₋ E → Γ ⟶₀₋ E
  cut-elimination₀ {Γ} {A} {E} ⟶A A⟶ = Wfx.wfRec cut-goal (λ trip rec → cut-elimination₀-gen trip (λ {A} Seq Seq′ → rec (A , size-⟶₀₋ Seq , size-⟶₀₋ Seq′))) (A , size-⟶₀₋ ⟶A , size-⟶₀₋ A⟶) ⟶A A⟶ refl refl
    where
      module Wfx = Wf.All (WfLex.×-wellFounded (On.wellFounded size-P₀ <-wellFounded) (WfLex.×-wellFounded <-wellFounded <-wellFounded)) lzero

⟶₀⇒⟶₀₋ : Γ ⟶₀ A → Γ ⟶₀₋ A
⟶₀⇒⟶₀₋ (init₀ A∈)        = init₀₋ A∈
⟶₀⇒⟶₀₋ (⊥ₚ₀L ⊥∈)         = ⊥ₚ₀₋L ⊥∈
⟶₀⇒⟶₀₋ (∧ₚ₀R ⟶A ⟶B)      = ∧ₚ₀₋R (⟶₀⇒⟶₀₋ ⟶A) (⟶₀⇒⟶₀₋ ⟶B)
⟶₀⇒⟶₀₋ (∧ₚ₀L₁ A∧B∈ A⟶)   = ∧ₚ₀₋L₁ A∧B∈ (⟶₀⇒⟶₀₋ A⟶)
⟶₀⇒⟶₀₋ (∧ₚ₀L₂ A∧B∈ B⟶)   = ∧ₚ₀₋L₂ A∧B∈ (⟶₀⇒⟶₀₋ B⟶)
⟶₀⇒⟶₀₋ (∨ₚ₀R₁ ⟶A)        = ∨ₚ₀₋R₁ (⟶₀⇒⟶₀₋ ⟶A)
⟶₀⇒⟶₀₋ (∨ₚ₀R₂ ⟶B)        = ∨ₚ₀₋R₂ (⟶₀⇒⟶₀₋ ⟶B)
⟶₀⇒⟶₀₋ (∨ₚ₀L A∨B∈ A⟶ B⟶) = ∨ₚ₀₋L A∨B∈ (⟶₀⇒⟶₀₋ A⟶) (⟶₀⇒⟶₀₋ B⟶)
⟶₀⇒⟶₀₋ (→ₚ₀R A⟶B)        = →ₚ₀₋R (⟶₀⇒⟶₀₋ A⟶B)
⟶₀⇒⟶₀₋ (→ₚ₀L A→B∈ ⟶A B⟶) = →ₚ₀₋L A→B∈ (⟶₀⇒⟶₀₋ ⟶A) (⟶₀⇒⟶₀₋ B⟶)
⟶₀⇒⟶₀₋ (cut₀ ⟶A A⟶)      = cut-elimination₀ (⟶₀⇒⟶₀₋ ⟶A) (⟶₀⇒⟶₀₋ A⟶)

⟶₀-consistency : [] ⟶₀ ⊥ₚ₀ → ⊥
⟶₀-consistency ⟶⊥ = ⟶₀₋-consistency (⟶₀⇒⟶₀₋ ⟶⊥)

⊢₀-consistency : [] ⊢₀ ⊥ₚ₀ → ⊥
⊢₀-consistency ⊢⊥ = ⟶₀-consistency (⊢₀⇒⟶₀ ⊢⊥)

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

⟶₀₋⇒⊢₀ⁿ : Γ ⟶₀₋ A → Γ ⊢₀ⁿ A
⟶₀₋⇒⊢₀ⁿ (init₀₋ A∈)        = neut₀ⁿ (pre₀ʳ A∈)
⟶₀₋⇒⊢₀ⁿ (⊥ₚ₀₋L ⊥∈)         = neut₀ⁿ (⊥ₚ₀ʳE (pre₀ʳ ⊥∈))
⟶₀₋⇒⊢₀ⁿ (∧ₚ₀₋R ⟶A ⟶B)      = ∧ₚ₀ⁿI (⟶₀₋⇒⊢₀ⁿ ⟶A) (⟶₀₋⇒⊢₀ⁿ ⟶B)
⟶₀₋⇒⊢₀ⁿ (∧ₚ₀₋L₁ A∧B∈ A⟶)   = ⊢₀ⁿ-subst {[]} (⟶₀₋⇒⊢₀ⁿ A⟶) (∧ₚ₀ʳE₁ (pre₀ʳ A∧B∈))
⟶₀₋⇒⊢₀ⁿ (∧ₚ₀₋L₂ A∧B∈ B⟶)   = ⊢₀ⁿ-subst {[]} (⟶₀₋⇒⊢₀ⁿ B⟶) (∧ₚ₀ʳE₂ (pre₀ʳ A∧B∈))
⟶₀₋⇒⊢₀ⁿ (∨ₚ₀₋R₁ ⟶A)        = ∨ₚ₀ⁿI₁ (⟶₀₋⇒⊢₀ⁿ ⟶A)
⟶₀₋⇒⊢₀ⁿ (∨ₚ₀₋R₂ ⟶B)        = ∨ₚ₀ⁿI₂ (⟶₀₋⇒⊢₀ⁿ ⟶B)
⟶₀₋⇒⊢₀ⁿ (∨ₚ₀₋L A∨B∈ A⟶ B⟶) = ∨ₚ₀ⁿE (pre₀ʳ A∨B∈) (⟶₀₋⇒⊢₀ⁿ A⟶) (⟶₀₋⇒⊢₀ⁿ B⟶)
⟶₀₋⇒⊢₀ⁿ (→ₚ₀₋R A⟶B)        = →ₚ₀ⁿI (⟶₀₋⇒⊢₀ⁿ A⟶B)
⟶₀₋⇒⊢₀ⁿ (→ₚ₀₋L A→B∈ ⟶A B⟶) = ⊢₀ⁿ-subst {[]} (⟶₀₋⇒⊢₀ⁿ B⟶) (→ₚ₀ʳE (pre₀ʳ A→B∈) (⟶₀₋⇒⊢₀ⁿ ⟶A))

⊢₀ⁿ⇒⟶₀₋ : Γ ⊢₀ⁿ A → Γ ⟶₀₋ A
⊢₀ʳ⇒⟶₀₋⇒⟶₀₋ : Γ ⊢₀ʳ A → A ∷ Γ ⟶₀₋ C → Γ ⟶₀₋ C

⊢₀ⁿ⇒⟶₀₋ (∧ₚ₀ⁿI ⊢A ⊢B)      = ∧ₚ₀₋R (⊢₀ⁿ⇒⟶₀₋ ⊢A) (⊢₀ⁿ⇒⟶₀₋ ⊢B)
⊢₀ⁿ⇒⟶₀₋ (∨ₚ₀ⁿI₁ ⊢A)        = ∨ₚ₀₋R₁ (⊢₀ⁿ⇒⟶₀₋ ⊢A)
⊢₀ⁿ⇒⟶₀₋ (∨ₚ₀ⁿI₂ ⊢B)        = ∨ₚ₀₋R₂ (⊢₀ⁿ⇒⟶₀₋ ⊢B)
⊢₀ⁿ⇒⟶₀₋ (∨ₚ₀ⁿE ⊢A∨B A⊢ B⊢) = ⊢₀ʳ⇒⟶₀₋⇒⟶₀₋ ⊢A∨B (∨ₚ₀₋L (here refl) (⟶₀₋wk {_ ∷ []} (⊢₀ⁿ⇒⟶₀₋ A⊢)) (⟶₀₋wk {_ ∷ []} (⊢₀ⁿ⇒⟶₀₋ B⊢)))
⊢₀ⁿ⇒⟶₀₋ (→ₚ₀ⁿI A⊢B)        = →ₚ₀₋R (⊢₀ⁿ⇒⟶₀₋ A⊢B)
⊢₀ⁿ⇒⟶₀₋ (neut₀ⁿ ⊢A)        = ⊢₀ʳ⇒⟶₀₋⇒⟶₀₋ ⊢A (init₀₋ (here refl))

⊢₀ʳ⇒⟶₀₋⇒⟶₀₋ (pre₀ʳ A∈)         A⟶ = ⟶₀₋-resp-∈⇒∈ ∈⇒∈ A⟶
  where
    ∈⇒∈ : ∀ {B} → B ∈ _ ∷ _ → B ∈ _
    ∈⇒∈ (here refl) = ∈-++⁺ʳ _ A∈
    ∈⇒∈ (there B∈)  = ∈-++⁺ʳ _ B∈
⊢₀ʳ⇒⟶₀₋⇒⟶₀₋ (⊥ₚ₀ʳE ⊢⊥)         _  = ⊢₀ʳ⇒⟶₀₋⇒⟶₀₋ ⊢⊥ (⊥ₚ₀₋L (here refl))
⊢₀ʳ⇒⟶₀₋⇒⟶₀₋ (∧ₚ₀ʳE₁ ⊢A∧B)      A⟶ = ⊢₀ʳ⇒⟶₀₋⇒⟶₀₋ ⊢A∧B (∧ₚ₀₋L₁ (here refl) (⟶₀₋wk {_ ∷ []} A⟶))
⊢₀ʳ⇒⟶₀₋⇒⟶₀₋ (∧ₚ₀ʳE₂ ⊢A∧B)      B⟶ = ⊢₀ʳ⇒⟶₀₋⇒⟶₀₋ ⊢A∧B (∧ₚ₀₋L₂ (here refl) (⟶₀₋wk {_ ∷ []} B⟶))
⊢₀ʳ⇒⟶₀₋⇒⟶₀₋ (→ₚ₀ʳE ⊢A→B ⊢A)    B⟶ = ⊢₀ʳ⇒⟶₀₋⇒⟶₀₋ ⊢A→B (→ₚ₀₋L (here refl) (⟶₀₋wk {[]} (⊢₀ⁿ⇒⟶₀₋ ⊢A)) (⟶₀₋wk {_ ∷ []} B⟶))

⊢₀ⁿ-consistency : [] ⊢₀ⁿ ⊥ₚ₀ → ⊥
⊢₀ⁿ-consistency ⊢⊥ = ⟶₀₋-consistency (⊢₀ⁿ⇒⟶₀₋ ⊢⊥)

⊢₀ʳ-consistency : [] ⊢₀ʳ ⊥ₚ₀ → ⊥
⊢₀ʳ-consistency ⊢⊥ = ⊢₀ⁿ-consistency (neut₀ⁿ ⊢⊥)

weak-normalization₀ : Γ ⊢₀ A → Γ ⊢₀ⁿ A
weak-normalization₀ ⊢A = ⟶₀₋⇒⊢₀ⁿ (⟶₀⇒⟶₀₋ (⊢₀⇒⟶₀ ⊢A))
