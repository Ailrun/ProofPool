-- Sequent Calculus without Cut
module Logic.Zeroth.SC where

open import Logic.Zeroth.Base
open import Logic.Zeroth.Syntax public

infixl 4 _⟶₀₋_

data _⟶₀₋_ : Ctx₀ → P₀ → Set where
  init₀₋ : A ∈ Γ →
           --------
           Γ ⟶₀₋ A

  ⊥ₚ₀₋L  : ⊥ₚ₀ ∈ Γ →
           ----------
           Γ ⟶₀₋ A

  ∧ₚ₀₋R  : Γ ⟶₀₋ A →
           Γ ⟶₀₋ B →
           --------------
           Γ ⟶₀₋ A ∧ₚ₀ B

  ∧ₚ₀₋L₁ : A ∧ₚ₀ B ∈ Γ →
           A ∷ Γ ⟶₀₋ C →
           --------------
           Γ ⟶₀₋ C

  ∧ₚ₀₋L₂ : A ∧ₚ₀ B ∈ Γ →
           B ∷ Γ ⟶₀₋ C →
           --------------
           Γ ⟶₀₋ C

  ∨ₚ₀₋R₁ : Γ ⟶₀₋ A →
           --------------
           Γ ⟶₀₋ A ∨ₚ₀ B

  ∨ₚ₀₋R₂ : Γ ⟶₀₋ B →
           --------------
           Γ ⟶₀₋ A ∨ₚ₀ B

  ∨ₚ₀₋L  : A ∨ₚ₀ B ∈ Γ →
           A ∷ Γ ⟶₀₋ C →
           B ∷ Γ ⟶₀₋ C →
           --------------
           Γ ⟶₀₋ C

  →ₚ₀₋R  : A ∷ Γ ⟶₀₋ B →
           --------------
           Γ ⟶₀₋ A →ₚ₀ B

  →ₚ₀₋L  : A →ₚ₀ B ∈ Γ →
           Γ ⟶₀₋ A →
           B ∷ Γ ⟶₀₋ C →
           --------------
           Γ ⟶₀₋ C

size-⟶₀₋ : Γ ⟶₀₋ A → ℕ
size-⟶₀₋ (init₀₋ B∈)        = 1
size-⟶₀₋ (⊥ₚ₀₋L ⊥∈)         = 1
size-⟶₀₋ (∧ₚ₀₋R ⟶B ⟶C)      = suc (size-⟶₀₋ ⟶B + size-⟶₀₋ ⟶C)
size-⟶₀₋ (∧ₚ₀₋L₁ B∧C∈ B⟶)   = suc (size-⟶₀₋ B⟶)
size-⟶₀₋ (∧ₚ₀₋L₂ B∧C∈ C⟶)   = suc (size-⟶₀₋ C⟶)
size-⟶₀₋ (∨ₚ₀₋R₁ ⟶B)        = suc (size-⟶₀₋ ⟶B)
size-⟶₀₋ (∨ₚ₀₋R₂ ⟶C)        = suc (size-⟶₀₋ ⟶C)
size-⟶₀₋ (∨ₚ₀₋L B∨C∈ B⟶ C⟶) = suc (size-⟶₀₋ B⟶ + size-⟶₀₋ C⟶)
size-⟶₀₋ (→ₚ₀₋R B⟶C)        = suc (size-⟶₀₋ B⟶C)
size-⟶₀₋ (→ₚ₀₋L B→C∈ ⟶B C⟶) = suc (size-⟶₀₋ ⟶B + size-⟶₀₋ C⟶)

*⟶₀₋* = Σ (Ctx₀ × P₀) λ{ (Γ , A) → Γ ⟶₀₋ A }

to-*⟶₀₋* : Γ ⟶₀₋ A → *⟶₀₋*
to-*⟶₀₋* {Γ} {A} ⟶A = (Γ , A) , ⟶A

size-⟶₀₋′ : *⟶₀₋* → ℕ
size-⟶₀₋′ (_ , ⟶A) = size-⟶₀₋ ⟶A

⟶₀₋-resp-∈⇒∈ : (∀ {A} → A ∈ Γ → A ∈ Γ′) → Γ ⟶₀₋ B → Γ′ ⟶₀₋ B
⟶₀₋-resp-∈⇒∈ f (init₀₋ B∈)        = init₀₋ (f B∈)
⟶₀₋-resp-∈⇒∈ f (⊥ₚ₀₋L ⊥∈)         = ⊥ₚ₀₋L (f ⊥∈)
⟶₀₋-resp-∈⇒∈ f (∧ₚ₀₋R ⟶B ⟶C)      = ∧ₚ₀₋R (⟶₀₋-resp-∈⇒∈ f ⟶B) (⟶₀₋-resp-∈⇒∈ f ⟶C)
⟶₀₋-resp-∈⇒∈ f (∧ₚ₀₋L₁ B∧C∈ B⟶)   = ∧ₚ₀₋L₁ (f B∧C∈) (⟶₀₋-resp-∈⇒∈ (∈⇒∈-ext f) B⟶)
⟶₀₋-resp-∈⇒∈ f (∧ₚ₀₋L₂ B∧C∈ C⟶)   = ∧ₚ₀₋L₂ (f B∧C∈) (⟶₀₋-resp-∈⇒∈ (∈⇒∈-ext f) C⟶)
⟶₀₋-resp-∈⇒∈ f (∨ₚ₀₋R₁ ⟶B)        = ∨ₚ₀₋R₁ (⟶₀₋-resp-∈⇒∈ f ⟶B)
⟶₀₋-resp-∈⇒∈ f (∨ₚ₀₋R₂ ⟶C)        = ∨ₚ₀₋R₂ (⟶₀₋-resp-∈⇒∈ f ⟶C)
⟶₀₋-resp-∈⇒∈ f (∨ₚ₀₋L B∨C∈ B⟶ C⟶) = ∨ₚ₀₋L (f B∨C∈) (⟶₀₋-resp-∈⇒∈ (∈⇒∈-ext f) B⟶) (⟶₀₋-resp-∈⇒∈ (∈⇒∈-ext f) C⟶)
⟶₀₋-resp-∈⇒∈ f (→ₚ₀₋R B⟶C)        = →ₚ₀₋R (⟶₀₋-resp-∈⇒∈ (∈⇒∈-ext f) B⟶C)
⟶₀₋-resp-∈⇒∈ f (→ₚ₀₋L B→C∈ ⟶B C⟶) = →ₚ₀₋L (f B→C∈) (⟶₀₋-resp-∈⇒∈ f ⟶B) (⟶₀₋-resp-∈⇒∈ (∈⇒∈-ext f) C⟶)

⟶₀₋wk : Γ′ ++ Γ ⟶₀₋ B → Γ′ ++ A ∷ Γ ⟶₀₋ B
⟶₀₋wk {Γ′} ⟶B = ⟶₀₋-resp-∈⇒∈ (∈-++-∷ Γ′ _) ⟶B

⟶₀₋wk′ : Γ′ ++ Γ ⟶₀₋ A → Γ′ ++ Γ″ ++ Γ ⟶₀₋ A
⟶₀₋wk′ {Γ′} ⟶A = ⟶₀₋-resp-∈⇒∈ (∈-++-++ Γ′ _) ⟶A

⟶₀₋ct : Γ′ ++ A ∷ A ∷ Γ ⟶₀₋ B → Γ′ ++ A ∷ Γ ⟶₀₋ B
⟶₀₋ct {Γ′} ⟶B = ⟶₀₋-resp-∈⇒∈ (∈-++-dedupe₁ Γ′) ⟶B

⟶₀₋ex : Γ′ ++ A ∷ B ∷ Γ ⟶₀₋ C → Γ′ ++ B ∷ A ∷ Γ ⟶₀₋ C
⟶₀₋ex {Γ′} ⟶C = ⟶₀₋-resp-∈⇒∈ (∈-++-swap Γ′) ⟶C

∈⇒∈-preserves-size-⟶₀₋ : ∀ (f : ∀ {B} → B ∈ Γ → B ∈ Γ′) (Seq : Γ ⟶₀₋ A) → size-⟶₀₋ Seq ≡ size-⟶₀₋ (⟶₀₋-resp-∈⇒∈ f Seq)
∈⇒∈-preserves-size-⟶₀₋ f (init₀₋ B∈)        = refl
∈⇒∈-preserves-size-⟶₀₋ f (⊥ₚ₀₋L ⊥∈)         = refl
∈⇒∈-preserves-size-⟶₀₋ f (∧ₚ₀₋R ⟶B ⟶C)      = cong suc (cong₂ _+_ (∈⇒∈-preserves-size-⟶₀₋ f ⟶B) (∈⇒∈-preserves-size-⟶₀₋ f ⟶C))
∈⇒∈-preserves-size-⟶₀₋ f (∧ₚ₀₋L₁ B∧C∈ B⟶)   = cong suc (∈⇒∈-preserves-size-⟶₀₋ (∈⇒∈-ext f) B⟶)
∈⇒∈-preserves-size-⟶₀₋ f (∧ₚ₀₋L₂ B∧C∈ C⟶)   = cong suc (∈⇒∈-preserves-size-⟶₀₋ (∈⇒∈-ext f) C⟶)
∈⇒∈-preserves-size-⟶₀₋ f (∨ₚ₀₋R₁ ⟶B)        = cong suc (∈⇒∈-preserves-size-⟶₀₋ f ⟶B)
∈⇒∈-preserves-size-⟶₀₋ f (∨ₚ₀₋R₂ ⟶C)        = cong suc (∈⇒∈-preserves-size-⟶₀₋ f ⟶C)
∈⇒∈-preserves-size-⟶₀₋ f (∨ₚ₀₋L B∨C∈ B⟶ C⟶) = cong suc (cong₂ _+_ (∈⇒∈-preserves-size-⟶₀₋ (∈⇒∈-ext f) B⟶) (∈⇒∈-preserves-size-⟶₀₋ (∈⇒∈-ext f) C⟶))
∈⇒∈-preserves-size-⟶₀₋ f (→ₚ₀₋R B⟶C)        = cong suc (∈⇒∈-preserves-size-⟶₀₋ (∈⇒∈-ext f) B⟶C)
∈⇒∈-preserves-size-⟶₀₋ f (→ₚ₀₋L B→C∈ ⟶B C⟶) = cong suc (cong₂ _+_ (∈⇒∈-preserves-size-⟶₀₋ f ⟶B) (∈⇒∈-preserves-size-⟶₀₋ (∈⇒∈-ext f) C⟶))

⟶₀₋wk-preserves-size-⟶₀₋ : ∀ (Seq : Γ′ ++ Γ ⟶₀₋ B) → size-⟶₀₋ Seq ≡ size-⟶₀₋ (⟶₀₋wk {Γ′} {A = A} Seq)
⟶₀₋wk-preserves-size-⟶₀₋ {Γ′} = ∈⇒∈-preserves-size-⟶₀₋ (∈-++-∷ Γ′ _)

⟶₀₋wk′-preserves-size-⟶₀₋ : ∀ (Seq : Γ′ ++ Γ ⟶₀₋ B) → size-⟶₀₋ Seq ≡ size-⟶₀₋ (⟶₀₋wk′ {Γ′} {Γ″ = Γ″} Seq)
⟶₀₋wk′-preserves-size-⟶₀₋ {Γ′} = ∈⇒∈-preserves-size-⟶₀₋ (∈-++-++ Γ′ _)

⟶₀₋ct-preserves-size-⟶₀₋ : ∀ (Seq : Γ′ ++ A ∷ A ∷ Γ ⟶₀₋ B) → size-⟶₀₋ Seq ≡ size-⟶₀₋ (⟶₀₋ct {Γ′} Seq)
⟶₀₋ct-preserves-size-⟶₀₋ {Γ′} = ∈⇒∈-preserves-size-⟶₀₋ (∈-++-dedupe₁ Γ′)

⟶₀₋ex-preserves-size-⟶₀₋ : ∀ (Seq : Γ′ ++ A ∷ B ∷ Γ ⟶₀₋ C) → size-⟶₀₋ Seq ≡ size-⟶₀₋ (⟶₀₋ex {Γ′} Seq)
⟶₀₋ex-preserves-size-⟶₀₋ {Γ′} = ∈⇒∈-preserves-size-⟶₀₋ (∈-++-swap Γ′)
