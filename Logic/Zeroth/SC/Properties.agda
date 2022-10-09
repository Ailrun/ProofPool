-- Properties of Sequent Calculus without Cut
module Logic.Zeroth.SC.Properties where

open import Logic.Zeroth.SC

⟶₀₋-resp-∈⇒∈ : (∀ {A} → A ∈ Γ → A ∈ Γ′) → Γ ⟶₀₋ B → Γ′ ⟶₀₋ B
⟶₀₋-resp-∈⇒∈ f (init₀₋ B∈)         = init₀₋ (f B∈)
⟶₀₋-resp-∈⇒∈ f (⊥ₚ₀₋L  ⊥∈)         = ⊥ₚ₀₋L (f ⊥∈)
⟶₀₋-resp-∈⇒∈ f (∧ₚ₀₋R  ⟶B ⟶C)      = ∧ₚ₀₋R (⟶₀₋-resp-∈⇒∈ f ⟶B) (⟶₀₋-resp-∈⇒∈ f ⟶C)
⟶₀₋-resp-∈⇒∈ f (∧ₚ₀₋L₁ B∧C∈ B⟶)    = ∧ₚ₀₋L₁ (f B∧C∈) (⟶₀₋-resp-∈⇒∈ (∈⇒∈-ext f) B⟶)
⟶₀₋-resp-∈⇒∈ f (∧ₚ₀₋L₂ B∧C∈ C⟶)    = ∧ₚ₀₋L₂ (f B∧C∈) (⟶₀₋-resp-∈⇒∈ (∈⇒∈-ext f) C⟶)
⟶₀₋-resp-∈⇒∈ f (∨ₚ₀₋R₁ ⟶B)         = ∨ₚ₀₋R₁ (⟶₀₋-resp-∈⇒∈ f ⟶B)
⟶₀₋-resp-∈⇒∈ f (∨ₚ₀₋R₂ ⟶C)         = ∨ₚ₀₋R₂ (⟶₀₋-resp-∈⇒∈ f ⟶C)
⟶₀₋-resp-∈⇒∈ f (∨ₚ₀₋L  B∨C∈ B⟶ C⟶) = ∨ₚ₀₋L (f B∨C∈) (⟶₀₋-resp-∈⇒∈ (∈⇒∈-ext f) B⟶) (⟶₀₋-resp-∈⇒∈ (∈⇒∈-ext f) C⟶)
⟶₀₋-resp-∈⇒∈ f (→ₚ₀₋R  B⟶C)        = →ₚ₀₋R (⟶₀₋-resp-∈⇒∈ (∈⇒∈-ext f) B⟶C)
⟶₀₋-resp-∈⇒∈ f (→ₚ₀₋L  B→C∈ ⟶B C⟶) = →ₚ₀₋L (f B→C∈) (⟶₀₋-resp-∈⇒∈ f ⟶B) (⟶₀₋-resp-∈⇒∈ (∈⇒∈-ext f) C⟶)

⟶₀₋wk : Γ′ ++ Γ ⟶₀₋ B → Γ′ ++ A ∷ Γ ⟶₀₋ B
⟶₀₋wk {Γ′} ⟶B = ⟶₀₋-resp-∈⇒∈ (∈-++⇒∈-++-∷ Γ′ _) ⟶B

⟶₀₋wk′ : Γ′ ++ Γ ⟶₀₋ A → Γ′ ++ Γ″ ++ Γ ⟶₀₋ A
⟶₀₋wk′ {Γ′} ⟶A = ⟶₀₋-resp-∈⇒∈ (∈-++⇒∈-++-++ Γ′ _) ⟶A

⟶₀₋ct : Γ′ ++ A ∷ A ∷ Γ ⟶₀₋ B → Γ′ ++ A ∷ Γ ⟶₀₋ B
⟶₀₋ct {Γ′} ⟶B = ⟶₀₋-resp-∈⇒∈ (∈-++-dedupe₁ Γ′) ⟶B

⟶₀₋ex : Γ′ ++ A ∷ B ∷ Γ ⟶₀₋ C → Γ′ ++ B ∷ A ∷ Γ ⟶₀₋ C
⟶₀₋ex {Γ′} ⟶C = ⟶₀₋-resp-∈⇒∈ (∈-++-swap Γ′) ⟶C

∈⇒∈-preserves-size-⟶₀₋ : ∀ (f : ∀ {B} → B ∈ Γ → B ∈ Γ′) (Seq : Γ ⟶₀₋ A) → size-⟶₀₋ Seq ≡ size-⟶₀₋ (⟶₀₋-resp-∈⇒∈ f Seq)
∈⇒∈-preserves-size-⟶₀₋ f (init₀₋ B∈)         = refl
∈⇒∈-preserves-size-⟶₀₋ f (⊥ₚ₀₋L  ⊥∈)         = refl
∈⇒∈-preserves-size-⟶₀₋ f (∧ₚ₀₋R  ⟶B ⟶C)      = cong suc (cong₂ _+_ (∈⇒∈-preserves-size-⟶₀₋ f ⟶B) (∈⇒∈-preserves-size-⟶₀₋ f ⟶C))
∈⇒∈-preserves-size-⟶₀₋ f (∧ₚ₀₋L₁ B∧C∈ B⟶)    = cong suc (∈⇒∈-preserves-size-⟶₀₋ (∈⇒∈-ext f) B⟶)
∈⇒∈-preserves-size-⟶₀₋ f (∧ₚ₀₋L₂ B∧C∈ C⟶)    = cong suc (∈⇒∈-preserves-size-⟶₀₋ (∈⇒∈-ext f) C⟶)
∈⇒∈-preserves-size-⟶₀₋ f (∨ₚ₀₋R₁ ⟶B)         = cong suc (∈⇒∈-preserves-size-⟶₀₋ f ⟶B)
∈⇒∈-preserves-size-⟶₀₋ f (∨ₚ₀₋R₂ ⟶C)         = cong suc (∈⇒∈-preserves-size-⟶₀₋ f ⟶C)
∈⇒∈-preserves-size-⟶₀₋ f (∨ₚ₀₋L  B∨C∈ B⟶ C⟶) = cong suc (cong₂ _+_ (∈⇒∈-preserves-size-⟶₀₋ (∈⇒∈-ext f) B⟶) (∈⇒∈-preserves-size-⟶₀₋ (∈⇒∈-ext f) C⟶))
∈⇒∈-preserves-size-⟶₀₋ f (→ₚ₀₋R  B⟶C)        = cong suc (∈⇒∈-preserves-size-⟶₀₋ (∈⇒∈-ext f) B⟶C)
∈⇒∈-preserves-size-⟶₀₋ f (→ₚ₀₋L  B→C∈ ⟶B C⟶) = cong suc (cong₂ _+_ (∈⇒∈-preserves-size-⟶₀₋ f ⟶B) (∈⇒∈-preserves-size-⟶₀₋ (∈⇒∈-ext f) C⟶))

⟶₀₋wk-preserves-size-⟶₀₋ : ∀ (Seq : Γ′ ++ Γ ⟶₀₋ B) → size-⟶₀₋ Seq ≡ size-⟶₀₋ (⟶₀₋wk {Γ′} {A = A} Seq)
⟶₀₋wk-preserves-size-⟶₀₋ {Γ′} = ∈⇒∈-preserves-size-⟶₀₋ (∈-++⇒∈-++-∷ Γ′ _)

⟶₀₋wk′-preserves-size-⟶₀₋ : ∀ (Seq : Γ′ ++ Γ ⟶₀₋ B) → size-⟶₀₋ Seq ≡ size-⟶₀₋ (⟶₀₋wk′ {Γ′} {Γ″ = Γ″} Seq)
⟶₀₋wk′-preserves-size-⟶₀₋ {Γ′} = ∈⇒∈-preserves-size-⟶₀₋ (∈-++⇒∈-++-++ Γ′ _)

⟶₀₋ct-preserves-size-⟶₀₋ : ∀ (Seq : Γ′ ++ A ∷ A ∷ Γ ⟶₀₋ B) → size-⟶₀₋ Seq ≡ size-⟶₀₋ (⟶₀₋ct {Γ′} Seq)
⟶₀₋ct-preserves-size-⟶₀₋ {Γ′} = ∈⇒∈-preserves-size-⟶₀₋ (∈-++-dedupe₁ Γ′)

⟶₀₋ex-preserves-size-⟶₀₋ : ∀ (Seq : Γ′ ++ A ∷ B ∷ Γ ⟶₀₋ C) → size-⟶₀₋ Seq ≡ size-⟶₀₋ (⟶₀₋ex {Γ′} Seq)
⟶₀₋ex-preserves-size-⟶₀₋ {Γ′} = ∈⇒∈-preserves-size-⟶₀₋ (∈-++-swap Γ′)

⟶₀₋-consistency : [] ⟶₀₋ ⊥ₚ₀ → ⊥
⟶₀₋-consistency (init₀₋ ())
⟶₀₋-consistency (⊥ₚ₀₋L  ())
⟶₀₋-consistency (∧ₚ₀₋L₁ () _)
⟶₀₋-consistency (∧ₚ₀₋L₂ () _)
⟶₀₋-consistency (∨ₚ₀₋L  () _ _)
⟶₀₋-consistency (→ₚ₀₋L  () _ _)

-- Proof of cut elimination theorem
module _ where
  private
    _<ₗₑₓ_ : Rel (P₀ × ℕ × ℕ) 0ℓ
    _<ₗₑₓ_ = WfLex.×-Lex _≡_ (_<_ on size-P₀) (WfLex.×-Lex _≡_ _<_ _<_)

    <ₗₑₓ-of₀ : ∀ {Aₗ Aᵣ szₗ szᵣ szₗ′ szᵣ′} → size-P₀ Aₗ < size-P₀ Aᵣ → (Aₗ , szₗ , szₗ′) <ₗₑₓ (Aᵣ , szᵣ , szᵣ′)
    <ₗₑₓ-of₀ <-prf = inj₁ <-prf

    <ₗₑₓ-of₁ : ∀ {szₗ szᵣ szₗ′ szᵣ′} → szₗ < szᵣ → (A , szₗ , szₗ′) <ₗₑₓ (A , szᵣ , szᵣ′)
    <ₗₑₓ-of₁ <-prf = inj₂ (refl , inj₁ <-prf)

    <ₗₑₓ-of₂ : ∀ {sz szₗ′ szᵣ′} → szₗ′ < szᵣ′ → (A , sz , szₗ′) <ₗₑₓ (A , sz , szᵣ′)
    <ₗₑₓ-of₂ <-prf = inj₂ (refl , inj₂ (refl , <-prf))

    <ₗₑₓ-wellFounded : Wf.WellFounded _<ₗₑₓ_
    <ₗₑₓ-wellFounded = WfLex.×-wellFounded (On.wellFounded size-P₀ <-wellFounded) (WfLex.×-wellFounded <-wellFounded <-wellFounded)

    cut₀₋-goal : P₀ × ℕ × ℕ → Set
    cut₀₋-goal (A , sz , sz′) =
      ∀ {Γ E} (Seq : Γ ⟶₀₋ A) (Seq′ : A ∷ Γ ⟶₀₋ E) →
      sz ≡ size-⟶₀₋ Seq →
      sz′ ≡ size-⟶₀₋ Seq′ → 
      Γ ⟶₀₋ E

    module _ trip (rec : ∀ trip′ → trip′ <ₗₑₓ trip → cut₀₋-goal trip′) where
      rec-structural : ∀ {Γ A E} → (Seq : Γ ⟶₀₋ A) (Seq′ : A ∷ Γ ⟶₀₋ E) → (A , size-⟶₀₋ Seq , size-⟶₀₋ Seq′) <ₗₑₓ trip → Γ ⟶₀₋ E
      rec-structural {A = A} Seq Seq′ ord = rec (A , size-⟶₀₋ Seq , size-⟶₀₋ Seq′) ord Seq Seq′ refl refl

      rec-wk/ex      : ∀ {Γ A B E} → (Seq : Γ ⟶₀₋ A) (Seq′ : B ∷ A ∷ Γ ⟶₀₋ E) → (A , size-⟶₀₋ Seq , size-⟶₀₋ Seq′) <ₗₑₓ trip → B ∷ Γ ⟶₀₋ E
      rec-wk/ex      {A = A} Seq Seq′ ord = rec (A , size-⟶₀₋ Seq , size-⟶₀₋ Seq′) ord (⟶₀₋wk {[]} Seq) (⟶₀₋ex {[]} Seq′) (⟶₀₋wk-preserves-size-⟶₀₋ {[]} Seq) (⟶₀₋ex-preserves-size-⟶₀₋ {[]} Seq′)

      cut₀₋-gen : cut₀₋-goal trip
      -- When the sequent showing the cut formula ends with the `init₀₋` rule
      cut₀₋-gen (init₀₋ A∈)         A⟶                          refl refl = ⟶₀₋-resp-∈⇒∈ ∈⇒∈ A⟶
        where
          ∈⇒∈ : ∀ {B} → B ∈ proj₁ trip ∷ _ → B ∈ _
          ∈⇒∈ (here refl) = ∈-++⁺ʳ _ A∈
          ∈⇒∈ (there B∈)  = ∈-++⁺ʳ _ B∈
      -- When the sequent showing the cut formula ends with the `⊥ₚ₀₋L` rule
      cut₀₋-gen (⊥ₚ₀₋L  ⊥∈)         A⟶                          refl refl = ⊥ₚ₀₋L ⊥∈
      -- When the sequent showing the cut formula ends with any left rule,
      -- i.e. the rules where the cut formula cannot be the principal formula
      cut₀₋-gen (∧ₚ₀₋L₁ A∧B∈ A⟶)    C⟶                          refl refl = ∧ₚ₀₋L₁ A∧B∈ (rec-structural A⟶ (⟶₀₋wk {_ ∷ []} C⟶) (<ₗₑₓ-of₁ ≤-refl))
      cut₀₋-gen (∧ₚ₀₋L₂ A∧B∈ B⟶)    C⟶                          refl refl = ∧ₚ₀₋L₂ A∧B∈ (rec-structural B⟶ (⟶₀₋wk {_ ∷ []} C⟶) (<ₗₑₓ-of₁ ≤-refl))
      cut₀₋-gen (∨ₚ₀₋L  A∨B∈ A⟶ B⟶) C⟶                          refl refl = ∨ₚ₀₋L A∨B∈
                                                                              (rec-structural A⟶ (⟶₀₋wk {_ ∷ []} C⟶) (<ₗₑₓ-of₁ (m≤m+n _ _)))
                                                                              (rec-structural B⟶ (⟶₀₋wk {_ ∷ []} C⟶) (<ₗₑₓ-of₁ (s≤s (m≤n+m _ _))))
      cut₀₋-gen (→ₚ₀₋L  A→B∈ ⟶A B⟶) C⟶                          refl refl = →ₚ₀₋L A→B∈ ⟶A (rec-structural B⟶ (⟶₀₋wk {_ ∷ []} C⟶) (<ₗₑₓ-of₁ (s≤s (m≤n+m _ _))))
      -- When the sequent assuming the cut formula ends with the `init₀₋` rule
      cut₀₋-gen ⟶A                  (init₀₋ (here refl))        refl refl = ⟶A
      cut₀₋-gen ⟶A                  (init₀₋ (there D∈))         refl refl = init₀₋ D∈
      -- When the sequent assuming the cut formula ends with the `⊥ₚ₀₋L` rule
      -- `⊥ₚ₀₋L (here refl)` case (i.e. where the cut formula is `⊥ₚ₀`) is already covered by above cases
      cut₀₋-gen ⟶A                  (⊥ₚ₀₋L  (there ⊥∈))         refl refl = ⊥ₚ₀₋L ⊥∈
      -- When the sequent assuming the cut formula ends with any right rule,
      -- i.e. the rules where the cut formula cannot be the principal formula
      cut₀₋-gen ⟶A                  (∧ₚ₀₋R  ⟶C ⟶D)              refl refl = ∧ₚ₀₋R
                                                                              (rec-structural ⟶A ⟶C (<ₗₑₓ-of₂ (m≤m+n _ _)))
                                                                              (rec-structural ⟶A ⟶D (<ₗₑₓ-of₂ (s≤s (m≤n+m _ _))))
      cut₀₋-gen ⟶A                  (∨ₚ₀₋R₁ ⟶C)                 refl refl = ∨ₚ₀₋R₁ (rec-structural ⟶A ⟶C (<ₗₑₓ-of₂ ≤-refl))
      cut₀₋-gen ⟶A                  (∨ₚ₀₋R₂ ⟶D)                 refl refl = ∨ₚ₀₋R₂ (rec-structural ⟶A ⟶D (<ₗₑₓ-of₂ ≤-refl))
      cut₀₋-gen ⟶A                  (→ₚ₀₋R  C⟶D)                refl refl = →ₚ₀₋R (rec-wk/ex ⟶A C⟶D (<ₗₑₓ-of₂ ≤-refl))
      -- When the sequent assuming the cut formula ends with a left rule,
      -- but the rule does not use the cut formula as its principal formula
      cut₀₋-gen ⟶A∧B@(∧ₚ₀₋R  _  _)  (∧ₚ₀₋L₁ (there C∧D∈) C⟶)    refl refl = ∧ₚ₀₋L₁ C∧D∈ (rec-wk/ex ⟶A∧B C⟶ (<ₗₑₓ-of₂ ≤-refl))
      cut₀₋-gen ⟶A∧B@(∧ₚ₀₋R  _  _)  (∧ₚ₀₋L₂ (there C∧D∈) D⟶)    refl refl = ∧ₚ₀₋L₂ C∧D∈ (rec-wk/ex ⟶A∧B D⟶ (<ₗₑₓ-of₂ ≤-refl))
      cut₀₋-gen ⟶A∧B@(∧ₚ₀₋R  _  _)  (∨ₚ₀₋L  (there C∨D∈) C⟶ D⟶) refl refl = ∨ₚ₀₋L C∨D∈
                                                                              (rec-wk/ex ⟶A∧B C⟶ (<ₗₑₓ-of₂ (m≤m+n _ _)))
                                                                              (rec-wk/ex ⟶A∧B D⟶ (<ₗₑₓ-of₂ (s≤s (m≤n+m _ _))))
      cut₀₋-gen ⟶A∧B@(∧ₚ₀₋R  _  _)  (→ₚ₀₋L  (there C→D∈) ⟶C D⟶) refl refl = →ₚ₀₋L C→D∈
                                                                              (rec-structural ⟶A∧B ⟶C (<ₗₑₓ-of₂ (m≤m+n _ _)))
                                                                              (rec-wk/ex ⟶A∧B D⟶ (<ₗₑₓ-of₂ (s≤s (m≤n+m _ _))))
      cut₀₋-gen ⟶A∨B@(∨ₚ₀₋R₁ _)     (∧ₚ₀₋L₁ (there C∧D∈) C⟶)    refl refl = ∧ₚ₀₋L₁ C∧D∈ (rec-wk/ex ⟶A∨B C⟶ (<ₗₑₓ-of₂ ≤-refl))
      cut₀₋-gen ⟶A∨B@(∨ₚ₀₋R₁ _)     (∧ₚ₀₋L₂ (there C∧D∈) D⟶)    refl refl = ∧ₚ₀₋L₂ C∧D∈ (rec-wk/ex ⟶A∨B D⟶ (<ₗₑₓ-of₂ ≤-refl))
      cut₀₋-gen ⟶A∨B@(∨ₚ₀₋R₁ _)     (∨ₚ₀₋L  (there C∨D∈) C⟶ D⟶) refl refl = ∨ₚ₀₋L C∨D∈
                                                                              (rec-wk/ex ⟶A∨B C⟶ (<ₗₑₓ-of₂ (m≤m+n _ _)))
                                                                              (rec-wk/ex ⟶A∨B D⟶ (<ₗₑₓ-of₂ (s≤s (m≤n+m _ _))))
      cut₀₋-gen ⟶A∨B@(∨ₚ₀₋R₁ _)     (→ₚ₀₋L  (there C→D∈) ⟶C D⟶) refl refl = →ₚ₀₋L C→D∈
                                                                              (rec-structural ⟶A∨B ⟶C (<ₗₑₓ-of₂ (m≤m+n _ _)))
                                                                              (rec-wk/ex ⟶A∨B D⟶ (<ₗₑₓ-of₂ (s≤s (m≤n+m _ _))))
      cut₀₋-gen ⟶A∨B@(∨ₚ₀₋R₂ _)     (∧ₚ₀₋L₁ (there C∧D∈) C⟶)    refl refl = ∧ₚ₀₋L₁ C∧D∈ (rec-wk/ex ⟶A∨B C⟶ (<ₗₑₓ-of₂ ≤-refl))
      cut₀₋-gen ⟶A∨B@(∨ₚ₀₋R₂ _)     (∧ₚ₀₋L₂ (there C∧D∈) D⟶)    refl refl = ∧ₚ₀₋L₂ C∧D∈ (rec-wk/ex ⟶A∨B D⟶ (<ₗₑₓ-of₂ ≤-refl))
      cut₀₋-gen ⟶A∨B@(∨ₚ₀₋R₂ _)     (∨ₚ₀₋L  (there C∨D∈) C⟶ D⟶) refl refl = ∨ₚ₀₋L C∨D∈
                                                                              (rec-wk/ex ⟶A∨B C⟶ (<ₗₑₓ-of₂ (m≤m+n _ _)))
                                                                              (rec-wk/ex ⟶A∨B D⟶ (<ₗₑₓ-of₂ (s≤s (m≤n+m _ _))))
      cut₀₋-gen ⟶A∨B@(∨ₚ₀₋R₂ _)     (→ₚ₀₋L  (there C→D∈) ⟶C D⟶) refl refl = →ₚ₀₋L C→D∈
                                                                              (rec-structural ⟶A∨B ⟶C (<ₗₑₓ-of₂ (m≤m+n _ _)))
                                                                              (rec-wk/ex ⟶A∨B D⟶ (<ₗₑₓ-of₂ (s≤s (m≤n+m _ _))))
      cut₀₋-gen ⟶A→B@(→ₚ₀₋R  _)     (∧ₚ₀₋L₁ (there C∧D∈) C⟶)    refl refl = ∧ₚ₀₋L₁ C∧D∈ (rec-wk/ex ⟶A→B C⟶ (<ₗₑₓ-of₂ ≤-refl))
      cut₀₋-gen ⟶A→B@(→ₚ₀₋R  _)     (∧ₚ₀₋L₂ (there C∧D∈) D⟶)    refl refl = ∧ₚ₀₋L₂ C∧D∈ (rec-wk/ex ⟶A→B D⟶ (<ₗₑₓ-of₂ ≤-refl))
      cut₀₋-gen ⟶A→B@(→ₚ₀₋R  _)     (∨ₚ₀₋L  (there C∨D∈) C⟶ D⟶) refl refl = ∨ₚ₀₋L C∨D∈
                                                                              (rec-wk/ex ⟶A→B C⟶ (<ₗₑₓ-of₂ (m≤m+n _ _)))
                                                                              (rec-wk/ex ⟶A→B D⟶ (<ₗₑₓ-of₂ (s≤s (m≤n+m _ _))))
      cut₀₋-gen ⟶A→B@(→ₚ₀₋R  _)     (→ₚ₀₋L  (there C→D∈) ⟶C D⟶) refl refl = →ₚ₀₋L C→D∈
                                                                              (rec-structural ⟶A→B ⟶C (<ₗₑₓ-of₂ (m≤m+n _ _)))
                                                                              (rec-wk/ex ⟶A→B D⟶ (<ₗₑₓ-of₂ (s≤s (m≤n+m _ _))))
      -- When both the sequent showing the cut formula and the one assuming the cut formula
      -- end with rules that use the cut formula as their principal formulae
      cut₀₋-gen ⟶A∧B@(∧ₚ₀₋R  ⟶A ⟶B) (∧ₚ₀₋L₁ (here refl) A⟶)     refl refl = rec-structural ⟶A A⟶E (<ₗₑₓ-of₀ (m≤m+n _ _))
        where
          A⟶E = rec-wk/ex ⟶A∧B A⟶ (<ₗₑₓ-of₂ ≤-refl)
      cut₀₋-gen ⟶A∧B@(∧ₚ₀₋R  ⟶A ⟶B) (∧ₚ₀₋L₂ (here refl) B⟶)     refl refl = rec-structural ⟶B B⟶E (<ₗₑₓ-of₀ (s≤s (m≤n+m _ _)))
        where
          B⟶E = rec-wk/ex ⟶A∧B B⟶ (<ₗₑₓ-of₂ ≤-refl)
      cut₀₋-gen ⟶A∨B@(∨ₚ₀₋R₁ ⟶A)    (∨ₚ₀₋L  (here refl) A⟶ B⟶)  refl refl = rec-structural ⟶A A⟶E (<ₗₑₓ-of₀ (m≤m+n _ _))
        where
          A⟶E = rec-wk/ex ⟶A∨B A⟶ (<ₗₑₓ-of₂ (m≤m+n _ _))
      cut₀₋-gen ⟶A∨B@(∨ₚ₀₋R₂ ⟶B)    (∨ₚ₀₋L  (here refl) A⟶ B⟶)  refl refl = rec-structural ⟶B B⟶E (<ₗₑₓ-of₀ (s≤s (m≤n+m _ _)))
        where
          B⟶E = rec-wk/ex ⟶A∨B B⟶ (<ₗₑₓ-of₂ (s≤s (m≤n+m _ _)))
      cut₀₋-gen ⟶A→B@(→ₚ₀₋R  A⟶B)   (→ₚ₀₋L  (here refl) ⟶A B⟶)  refl refl = rec-structural ⟶B B⟶E (<ₗₑₓ-of₀ (s≤s (m≤n+m _ _)))
        where
          ⟶A′ = rec-structural ⟶A→B ⟶A (<ₗₑₓ-of₂ (m≤m+n _ _))
          ⟶B  = rec-structural ⟶A′ A⟶B (<ₗₑₓ-of₀ (m≤m+n _ _))
          B⟶E = rec-wk/ex ⟶A→B B⟶ (<ₗₑₓ-of₂ (s≤s (m≤n+m _ _)))

  -- cut elimination theorem
  cut₀₋ : Γ ⟶₀₋ A → A ∷ Γ ⟶₀₋ E → Γ ⟶₀₋ E
  cut₀₋ {Γ} {A} {E} ⟶A A⟶ = wfRec cut₀₋-goal cut₀₋-gen (A , size-⟶₀₋ ⟶A , size-⟶₀₋ A⟶) ⟶A A⟶ refl refl
    where
      open Wf.All <ₗₑₓ-wellFounded 0ℓ
