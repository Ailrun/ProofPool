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

⟶₀₋-consistent : [] ⟶₀₋ ⊥ₚ₀ → ⊥
⟶₀₋-consistent (init₀₋ ())
⟶₀₋-consistent (⊥ₚ₀₋L ())
⟶₀₋-consistent (∧ₚ₀₋L₁ () _)
⟶₀₋-consistent (∧ₚ₀₋L₂ () _)
⟶₀₋-consistent (∨ₚ₀₋L () _ _)
⟶₀₋-consistent (→ₚ₀₋L () _ _)

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

    module CutRec where
      cut-elimination-helper′ : ∀ trip (rec : ∀ {A Γ B Γ′ C} (Seq : Γ ⟶₀₋ B) (Seq′ : Γ′ ⟶₀₋ C) → (A , size-⟶₀₋ Seq , size-⟶₀₋ Seq′) <ₗₑₓ trip → cut-goal (A , size-⟶₀₋ Seq , size-⟶₀₋ Seq′)) → cut-goal trip
      cut-elimination-helper′ (A , _) rec (init₀₋ A∈)        A⟶                         refl refl = ⟶₀₋-resp-∈⇒∈ ∈⇒∈ A⟶
        where
          ∈⇒∈ : ∀ {B} → B ∈ A ∷ _ → B ∈ _
          ∈⇒∈ (here refl) = ∈-++⁺ʳ _ A∈
          ∈⇒∈ (there B∈)  = ∈-++⁺ʳ _ B∈
      cut-elimination-helper′ _       rec (⊥ₚ₀₋L ⊥∈)         A⟶                         refl refl = ⊥ₚ₀₋L ⊥∈
      cut-elimination-helper′ _       rec (∧ₚ₀₋L₁ A∧B∈ A⟶)   C⟶                         refl refl = ∧ₚ₀₋L₁ A∧B∈ (rec A⟶ (⟶₀₋wk {_ ∷ []} C⟶) (<ₗₑₓ-of₁ ≤-refl) A⟶ (⟶₀₋wk {_ ∷ []} C⟶) refl refl)
      cut-elimination-helper′ _       rec (∧ₚ₀₋L₂ A∧B∈ B⟶)   C⟶                         refl refl = ∧ₚ₀₋L₂ A∧B∈ (rec B⟶ (⟶₀₋wk {_ ∷ []} C⟶) (<ₗₑₓ-of₁ ≤-refl) B⟶ (⟶₀₋wk {_ ∷ []} C⟶) refl refl)
      cut-elimination-helper′ _       rec (∨ₚ₀₋L A∨B∈ A⟶ B⟶) C⟶                         refl refl = ∨ₚ₀₋L A∨B∈ (rec A⟶ (⟶₀₋wk {_ ∷ []} C⟶) (<ₗₑₓ-of₁ (m≤m+n _ _)) A⟶ (⟶₀₋wk {_ ∷ []} C⟶) refl refl) (rec B⟶ (⟶₀₋wk {_ ∷ []} C⟶) (<ₗₑₓ-of₁ (s≤s (m≤n+m _ _))) B⟶ (⟶₀₋wk {_ ∷ []} C⟶) refl refl)
      cut-elimination-helper′ _       rec (→ₚ₀₋L A→B∈ ⟶A B⟶) C⟶                         refl refl = →ₚ₀₋L A→B∈ ⟶A (rec B⟶ (⟶₀₋wk {_ ∷ []} C⟶) (<ₗₑₓ-of₁ (s≤s (m≤n+m _ _))) B⟶ (⟶₀₋wk {_ ∷ []} C⟶) refl refl)
      cut-elimination-helper′ trip    rec ⟶A∧B@(∧ₚ₀₋R ⟶A ⟶B) (∧ₚ₀₋L₁ (here refl) A⟶)    refl refl = rec ⟶A A⟶E (<ₗₑₓ-of₀ (m≤m+n _ _)) ⟶A A⟶E refl refl
        where
          A⟶E = rec ⟶A∧B A⟶ (<ₗₑₓ-of₂ ≤-refl) (⟶₀₋wk {[]} ⟶A∧B) (⟶₀₋ex {[]} A⟶) (⟶₀₋wk-preserves-size-⟶₀₋ {[]} ⟶A∧B) (⟶₀₋ex-preserves-size-⟶₀₋ {[]} A⟶)
      cut-elimination-helper′ trip    rec ⟶A∧B@(∧ₚ₀₋R _  _)  (∧ₚ₀₋L₁ (there C∧D∈) C⟶)   refl refl = ∧ₚ₀₋L₁ C∧D∈ (rec ⟶A∧B C⟶ (<ₗₑₓ-of₂ ≤-refl) (⟶₀₋wk {[]} ⟶A∧B) (⟶₀₋ex {[]} C⟶) (⟶₀₋wk-preserves-size-⟶₀₋ {[]} ⟶A∧B) (⟶₀₋ex-preserves-size-⟶₀₋ {[]} C⟶))
      cut-elimination-helper′ trip    rec ⟶A∧B@(∧ₚ₀₋R ⟶A ⟶B) (∧ₚ₀₋L₂ (here refl) B⟶)    refl refl = rec ⟶B B⟶E (<ₗₑₓ-of₀ (s≤s (m≤n+m _ _))) ⟶B B⟶E refl refl
        where
          B⟶E = rec ⟶A∧B B⟶ (<ₗₑₓ-of₂ ≤-refl) (⟶₀₋wk {[]} ⟶A∧B) (⟶₀₋ex {[]} B⟶) (⟶₀₋wk-preserves-size-⟶₀₋ {[]} ⟶A∧B) (⟶₀₋ex-preserves-size-⟶₀₋ {[]} B⟶)
      cut-elimination-helper′ trip    rec ⟶A∧B@(∧ₚ₀₋R _  _)  (∧ₚ₀₋L₂ (there C∧D∈) D⟶)   refl refl = ∧ₚ₀₋L₂ C∧D∈ (rec ⟶A∧B D⟶ (<ₗₑₓ-of₂ ≤-refl) (⟶₀₋wk {[]} ⟶A∧B) (⟶₀₋ex {[]} D⟶) (⟶₀₋wk-preserves-size-⟶₀₋ {[]} ⟶A∧B) (⟶₀₋ex-preserves-size-⟶₀₋ {[]} D⟶))
      cut-elimination-helper′ trip    rec ⟶A∧B@(∧ₚ₀₋R _  _)  (∨ₚ₀₋L (there C∨D∈) C⟶ D⟶) refl refl = ∨ₚ₀₋L C∨D∈
                                                                                                     (rec ⟶A∧B C⟶ (<ₗₑₓ-of₂ (m≤m+n _ _)) (⟶₀₋wk {[]} ⟶A∧B) (⟶₀₋ex {[]} C⟶) (⟶₀₋wk-preserves-size-⟶₀₋ {[]} ⟶A∧B) (⟶₀₋ex-preserves-size-⟶₀₋ {[]} C⟶))
                                                                                                     (rec ⟶A∧B D⟶ (<ₗₑₓ-of₂ (s≤s (m≤n+m _ _))) (⟶₀₋wk {[]} ⟶A∧B) (⟶₀₋ex {[]} D⟶) (⟶₀₋wk-preserves-size-⟶₀₋ {[]} ⟶A∧B) (⟶₀₋ex-preserves-size-⟶₀₋ {[]} D⟶))
      cut-elimination-helper′ trip    rec ⟶A∧B@(∧ₚ₀₋R _  _)  (→ₚ₀₋L (there C→D∈) ⟶C D⟶) refl refl = →ₚ₀₋L C→D∈
                                                                                                     (rec ⟶A∧B ⟶C (<ₗₑₓ-of₂ (m≤m+n _ _)) ⟶A∧B ⟶C refl refl)
                                                                                                     (rec ⟶A∧B D⟶ (<ₗₑₓ-of₂ (s≤s (m≤n+m _ _))) (⟶₀₋wk {[]} ⟶A∧B) (⟶₀₋ex {[]} D⟶) (⟶₀₋wk-preserves-size-⟶₀₋ {[]} ⟶A∧B) (⟶₀₋ex-preserves-size-⟶₀₋ {[]} D⟶))
      cut-elimination-helper′ trip    rec ⟶A∨B@(∨ₚ₀₋R₁ _)    (∧ₚ₀₋L₁ (there C∧D∈) C⟶)   refl refl = ∧ₚ₀₋L₁ C∧D∈ (rec ⟶A∨B C⟶ (<ₗₑₓ-of₂ ≤-refl) (⟶₀₋wk {[]} ⟶A∨B) (⟶₀₋ex {[]} C⟶) (⟶₀₋wk-preserves-size-⟶₀₋ {[]} ⟶A∨B) (⟶₀₋ex-preserves-size-⟶₀₋ {[]} C⟶))
      cut-elimination-helper′ trip    rec ⟶A∨B@(∨ₚ₀₋R₁ _)    (∧ₚ₀₋L₂ (there C∧D∈) D⟶)   refl refl = ∧ₚ₀₋L₂ C∧D∈ (rec ⟶A∨B D⟶ (<ₗₑₓ-of₂ ≤-refl) (⟶₀₋wk {[]} ⟶A∨B) (⟶₀₋ex {[]} D⟶) (⟶₀₋wk-preserves-size-⟶₀₋ {[]} ⟶A∨B) (⟶₀₋ex-preserves-size-⟶₀₋ {[]} D⟶))
      cut-elimination-helper′ trip    rec ⟶A∨B@(∨ₚ₀₋R₁ ⟶A)   (∨ₚ₀₋L (here refl) A⟶ B⟶)  refl refl = rec ⟶A A⟶E (<ₗₑₓ-of₀ (m≤m+n _ _)) ⟶A A⟶E refl refl
        where
          A⟶E = rec ⟶A∨B A⟶ (<ₗₑₓ-of₂ (m≤m+n _ _)) (⟶₀₋wk {[]} ⟶A∨B) (⟶₀₋ex {[]} A⟶) (⟶₀₋wk-preserves-size-⟶₀₋ {[]} ⟶A∨B) (⟶₀₋ex-preserves-size-⟶₀₋ {[]} A⟶)
      cut-elimination-helper′ trip    rec ⟶A∨B@(∨ₚ₀₋R₁ _)    (∨ₚ₀₋L (there C∨D∈) C⟶ D⟶) refl refl = ∨ₚ₀₋L C∨D∈
                                                                                                     (rec ⟶A∨B C⟶ (<ₗₑₓ-of₂ (m≤m+n _ _)) (⟶₀₋wk {[]} ⟶A∨B) (⟶₀₋ex {[]} C⟶) (⟶₀₋wk-preserves-size-⟶₀₋ {[]} ⟶A∨B) (⟶₀₋ex-preserves-size-⟶₀₋ {[]} C⟶))
                                                                                                     (rec ⟶A∨B D⟶ (<ₗₑₓ-of₂ (s≤s (m≤n+m _ _))) (⟶₀₋wk {[]} ⟶A∨B) (⟶₀₋ex {[]} D⟶) (⟶₀₋wk-preserves-size-⟶₀₋ {[]} ⟶A∨B) (⟶₀₋ex-preserves-size-⟶₀₋ {[]} D⟶))
      cut-elimination-helper′ trip    rec ⟶A∨B@(∨ₚ₀₋R₁ _)    (→ₚ₀₋L (there C→D∈) ⟶C D⟶) refl refl = →ₚ₀₋L C→D∈
                                                                                                     (rec ⟶A∨B ⟶C (<ₗₑₓ-of₂ (m≤m+n _ _)) ⟶A∨B ⟶C refl refl)
                                                                                                     (rec ⟶A∨B D⟶ (<ₗₑₓ-of₂ (s≤s (m≤n+m _ _))) (⟶₀₋wk {[]} ⟶A∨B) (⟶₀₋ex {[]} D⟶) (⟶₀₋wk-preserves-size-⟶₀₋ {[]} ⟶A∨B) (⟶₀₋ex-preserves-size-⟶₀₋ {[]} D⟶))
      cut-elimination-helper′ trip    rec ⟶A∨B@(∨ₚ₀₋R₂ _)    (∧ₚ₀₋L₁ (there C∧D∈) C⟶)   refl refl = ∧ₚ₀₋L₁ C∧D∈ (rec ⟶A∨B C⟶ (<ₗₑₓ-of₂ ≤-refl) (⟶₀₋wk {[]} ⟶A∨B) (⟶₀₋ex {[]} C⟶) (⟶₀₋wk-preserves-size-⟶₀₋ {[]} ⟶A∨B) (⟶₀₋ex-preserves-size-⟶₀₋ {[]} C⟶))
      cut-elimination-helper′ trip    rec ⟶A∨B@(∨ₚ₀₋R₂ _)    (∧ₚ₀₋L₂ (there C∧D∈) D⟶)   refl refl = ∧ₚ₀₋L₂ C∧D∈ (rec ⟶A∨B D⟶ (<ₗₑₓ-of₂ ≤-refl) (⟶₀₋wk {[]} ⟶A∨B) (⟶₀₋ex {[]} D⟶) (⟶₀₋wk-preserves-size-⟶₀₋ {[]} ⟶A∨B) (⟶₀₋ex-preserves-size-⟶₀₋ {[]} D⟶))
      cut-elimination-helper′ trip    rec ⟶A∨B@(∨ₚ₀₋R₂ ⟶B)   (∨ₚ₀₋L (here refl) A⟶ B⟶)  refl refl = rec ⟶B B⟶E (<ₗₑₓ-of₀ (s≤s (m≤n+m _ _))) ⟶B B⟶E refl refl
        where
          B⟶E = rec ⟶A∨B B⟶ (<ₗₑₓ-of₂ (s≤s (m≤n+m _ _))) (⟶₀₋wk {[]} ⟶A∨B) (⟶₀₋ex {[]} B⟶) (⟶₀₋wk-preserves-size-⟶₀₋ {[]} ⟶A∨B) (⟶₀₋ex-preserves-size-⟶₀₋ {[]} B⟶)
      cut-elimination-helper′ trip    rec ⟶A∨B@(∨ₚ₀₋R₂ _)    (∨ₚ₀₋L (there C∨D∈) C⟶ D⟶) refl refl = ∨ₚ₀₋L C∨D∈
                                                                                                     (rec ⟶A∨B C⟶ (<ₗₑₓ-of₂ (m≤m+n _ _)) (⟶₀₋wk {[]} ⟶A∨B) (⟶₀₋ex {[]} C⟶) (⟶₀₋wk-preserves-size-⟶₀₋ {[]} ⟶A∨B) (⟶₀₋ex-preserves-size-⟶₀₋ {[]} C⟶))
                                                                                                     (rec ⟶A∨B D⟶ (<ₗₑₓ-of₂ (s≤s (m≤n+m _ _))) (⟶₀₋wk {[]} ⟶A∨B) (⟶₀₋ex {[]} D⟶) (⟶₀₋wk-preserves-size-⟶₀₋ {[]} ⟶A∨B) (⟶₀₋ex-preserves-size-⟶₀₋ {[]} D⟶))
      cut-elimination-helper′ trip    rec ⟶A∨B@(∨ₚ₀₋R₂ _)    (→ₚ₀₋L (there C→D∈) ⟶C D⟶) refl refl = →ₚ₀₋L C→D∈
                                                                                                     (rec ⟶A∨B ⟶C (<ₗₑₓ-of₂ (m≤m+n _ _)) ⟶A∨B ⟶C refl refl)
                                                                                                     (rec ⟶A∨B D⟶ (<ₗₑₓ-of₂ (s≤s (m≤n+m _ _))) (⟶₀₋wk {[]} ⟶A∨B) (⟶₀₋ex {[]} D⟶) (⟶₀₋wk-preserves-size-⟶₀₋ {[]} ⟶A∨B) (⟶₀₋ex-preserves-size-⟶₀₋ {[]} D⟶))
      cut-elimination-helper′ trip    rec ⟶A→B@(→ₚ₀₋R _)     (∧ₚ₀₋L₁ (there C∧D∈) C⟶)   refl refl = ∧ₚ₀₋L₁ C∧D∈ (rec ⟶A→B C⟶ (<ₗₑₓ-of₂ ≤-refl) (⟶₀₋wk {[]} ⟶A→B) (⟶₀₋ex {[]} C⟶) (⟶₀₋wk-preserves-size-⟶₀₋ {[]} ⟶A→B) (⟶₀₋ex-preserves-size-⟶₀₋ {[]} C⟶))
      cut-elimination-helper′ trip    rec ⟶A→B@(→ₚ₀₋R _)     (∧ₚ₀₋L₂ (there C∧D∈) D⟶)   refl refl = ∧ₚ₀₋L₂ C∧D∈ (rec ⟶A→B D⟶ (<ₗₑₓ-of₂ ≤-refl) (⟶₀₋wk {[]} ⟶A→B) (⟶₀₋ex {[]} D⟶) (⟶₀₋wk-preserves-size-⟶₀₋ {[]} ⟶A→B) (⟶₀₋ex-preserves-size-⟶₀₋ {[]} D⟶))
      cut-elimination-helper′ trip    rec ⟶A→B@(→ₚ₀₋R _)     (∨ₚ₀₋L (there C∨D∈) C⟶ D⟶) refl refl = ∨ₚ₀₋L C∨D∈
                                                                                                     (rec ⟶A→B C⟶ (<ₗₑₓ-of₂ (m≤m+n _ _)) (⟶₀₋wk {[]} ⟶A→B) (⟶₀₋ex {[]} C⟶) (⟶₀₋wk-preserves-size-⟶₀₋ {[]} ⟶A→B) (⟶₀₋ex-preserves-size-⟶₀₋ {[]} C⟶))
                                                                                                     (rec ⟶A→B D⟶ (<ₗₑₓ-of₂ (s≤s (m≤n+m _ _))) (⟶₀₋wk {[]} ⟶A→B) (⟶₀₋ex {[]} D⟶) (⟶₀₋wk-preserves-size-⟶₀₋ {[]} ⟶A→B) (⟶₀₋ex-preserves-size-⟶₀₋ {[]} D⟶))
      cut-elimination-helper′ trip    rec ⟶A→B@(→ₚ₀₋R A⟶B)   (→ₚ₀₋L (here refl) ⟶A B⟶)  refl refl = rec ⟶B B⟶E (<ₗₑₓ-of₀ (s≤s (m≤n+m _ _))) ⟶B B⟶E refl refl
        where
          ⟶A′ = rec ⟶A→B ⟶A (<ₗₑₓ-of₂ (m≤m+n _ _)) ⟶A→B ⟶A refl refl
          ⟶B = rec ⟶A′ A⟶B (<ₗₑₓ-of₀ (m≤m+n _ _)) ⟶A′ A⟶B refl refl
          B⟶E = rec ⟶A→B B⟶ (<ₗₑₓ-of₂ (s≤s (m≤n+m _ _))) (⟶₀₋wk {[]} ⟶A→B) (⟶₀₋ex {[]} B⟶) (⟶₀₋wk-preserves-size-⟶₀₋ {[]} ⟶A→B) (⟶₀₋ex-preserves-size-⟶₀₋ {[]} B⟶)
      cut-elimination-helper′ trip    rec ⟶A→B@(→ₚ₀₋R _)     (→ₚ₀₋L (there C→D∈) ⟶C D⟶) refl refl = →ₚ₀₋L C→D∈
                                                                                                     (rec ⟶A→B ⟶C (<ₗₑₓ-of₂ (m≤m+n _ _)) ⟶A→B ⟶C refl refl)
                                                                                                     (rec ⟶A→B D⟶ (<ₗₑₓ-of₂ (s≤s (m≤n+m _ _))) (⟶₀₋wk {[]} ⟶A→B) (⟶₀₋ex {[]} D⟶) (⟶₀₋wk-preserves-size-⟶₀₋ {[]} ⟶A→B) (⟶₀₋ex-preserves-size-⟶₀₋ {[]} D⟶))
      cut-elimination-helper′ trip    rec ⟶A                 (init₀₋ (here refl))       refl refl = ⟶A
      cut-elimination-helper′ trip    rec ⟶A                 (init₀₋ (there D∈))        refl refl = init₀₋ D∈
      cut-elimination-helper′ trip    rec ⟶A                 (⊥ₚ₀₋L (there ⊥∈))         refl refl = ⊥ₚ₀₋L ⊥∈
      cut-elimination-helper′ trip    rec ⟶A                 (∧ₚ₀₋R ⟶C ⟶D)              refl refl = ∧ₚ₀₋R (rec ⟶A ⟶C (<ₗₑₓ-of₂ (m≤m+n _ _)) ⟶A ⟶C refl refl) (rec ⟶A ⟶D (<ₗₑₓ-of₂ (s≤s (m≤n+m _ _))) ⟶A ⟶D refl refl)
      cut-elimination-helper′ trip    rec ⟶A                 (∨ₚ₀₋R₁ ⟶C)                refl refl = ∨ₚ₀₋R₁ (rec ⟶A ⟶C (<ₗₑₓ-of₂ ≤-refl) ⟶A ⟶C refl refl)
      cut-elimination-helper′ trip    rec ⟶A                 (∨ₚ₀₋R₂ ⟶D)                refl refl = ∨ₚ₀₋R₂ (rec ⟶A ⟶D (<ₗₑₓ-of₂ ≤-refl) ⟶A ⟶D refl refl)
      cut-elimination-helper′ trip    rec ⟶A                 (→ₚ₀₋R C⟶D)                refl refl = →ₚ₀₋R (rec ⟶A C⟶D (<ₗₑₓ-of₂ ≤-refl) (⟶₀₋wk {[]} ⟶A) (⟶₀₋ex {[]} C⟶D) (⟶₀₋wk-preserves-size-⟶₀₋ {[]} ⟶A) (⟶₀₋ex-preserves-size-⟶₀₋ {[]} C⟶D))

      cut-elimination-helper : ∀ trip (rec : ∀ trip′ → trip′ <ₗₑₓ trip → cut-goal trip′) → cut-goal trip
      cut-elimination-helper trip rec = cut-elimination-helper′ trip (λ {A} Seq Seq′ → rec (A , size-⟶₀₋ Seq , size-⟶₀₋ Seq′))

  cut-elimination-gen : ∀ (sz sz′ : ℕ) {A Γ E} (Seq : Γ ⟶₀₋ A) (Seq′ : A ∷ Γ ⟶₀₋ E) → sz ≡ size-⟶₀₋ Seq → sz′ ≡ size-⟶₀₋ Seq′ → Γ ⟶₀₋ E
  cut-elimination-gen sz sz′ {A} = Wfx.wfRec cut-goal (λ{ (A , sz , sz′) → CutRec.cut-elimination-helper (A , sz , sz′) }) (A , sz , sz′)
    where
      module Wfx = Wf.All (WfLex.×-wellFounded (On.wellFounded size-P₀ <-wellFounded) (WfLex.×-wellFounded <-wellFounded <-wellFounded)) lzero

cut-elimination : Γ ⟶₀₋ A → A ∷ Γ ⟶₀₋ E → Γ ⟶₀₋ E
cut-elimination {Γ} {A} {E} ⟶A A⟶ = cut-elimination-gen (size-⟶₀₋ ⟶A) (size-⟶₀₋ A⟶) ⟶A A⟶ refl refl

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
⟶₀⇒⟶₀₋ (cut₀ ⟶A A⟶)      = cut-elimination (⟶₀⇒⟶₀₋ ⟶A) (⟶₀⇒⟶₀₋ A⟶)

⟶₀-consistent : [] ⟶₀ ⊥ₚ₀ → ⊥
⟶₀-consistent ⟶⊥ = ⟶₀₋-consistent (⟶₀⇒⟶₀₋ ⟶⊥)

⊢₀-consistent : [] ⊢₀ ⊥ₚ₀ → ⊥
⊢₀-consistent ⊢⊥ = ⟶₀-consistent (⊢₀⇒⟶₀ ⊢⊥)
