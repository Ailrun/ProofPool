open import Logic.First.Signature

module Logic.First.Syntax (Sig : Signature₁) where

open Signature₁ Sig public

infixl 12 _$ₚ₁_
infixl 11 ¬ₚ₁_
infixl 10 _∧ₚ₁_
infixl 9 _∨ₚ₁_
infixr 8 _→ₚ₁_
infixr 7 ∀ₚ₁_∙_

data Tm₁ : Set where
  varTm₁ : ℕ → Tm₁
  constTm₁ : TmConst₁ → List Tm₁ → Tm₁

data P₁ : Set where
  ⊥ₚ₁ : P₁
  _$ₚ₁_ : TmPred₁ → List Tm₁ → P₁
  _∧ₚ₁_ : P₁ → P₁ → P₁
  _∨ₚ₁_ : P₁ → P₁ → P₁
  _→ₚ₁_ : P₁ → P₁ → P₁
  ∀ₚ₁_∙_ : TmTy₁ → P₁ → P₁

¬ₚ₁_ = _→ₚ₁ ⊥ₚ₁

Ctx₁ = List (P₁ ⊎ TmTy₁)

variable
  Γ Γ′ Γ″ Δ Δ′ Δ″ Ψ Ψ′ Ψ″ : Ctx₁
  A A′ A″ B B′ B″ C C′ C″ D D′ D″ E E′ E″ : P₁
  x x′ x″ y y′ y″ z z′ z″ : ℕ
  v v′ v″ w w′ w″ : Tm₁
  vs vs′ vs″ ws ws′ : List Tm₁

  a a′ a″ b b′ b″ c c′ c″ : TmConst₁
  s s′ s″ t t′ t″ u u′ u″ : TmTy₁
  ss ss′ ss″ ts ts′ ts″ us us′ us″ : List TmTy₁
  f f′ f″ g g′ g″ h h′ h″ : TmPred₁

infix 4 _⦂_v∈₁ₜ_
infix 4 _⊢₁ₜ_∈₁ₜ_
infix 4 _⊢₁ₜ_*∈₁ₜ_

data _⦂_v∈₁ₜ_ : ℕ → TmTy₁ → Ctx₁ → Set where
  here : ----------------------
         0 ⦂ s v∈₁ₜ inj₂ s ∷ Γ

  there₁ : x ⦂ s v∈₁ₜ Γ →
           ----------------------
           x ⦂ s v∈₁ₜ inj₁ A ∷ Γ

  there₂ : x ⦂ s v∈₁ₜ Γ →
           --------------------------
           suc x ⦂ s v∈₁ₜ inj₂ t ∷ Γ

data _⊢₁ₜ_∈₁ₜ_ : Ctx₁ → Tm₁ → TmTy₁ → Set
data _⊢₁ₜ_*∈₁ₜ_ : Ctx₁ → List Tm₁ → List TmTy₁ → Set

data _⊢₁ₜ_∈₁ₜ_ where
  constTm₁ : a returns₁ₜ s →
             Γ ⊢₁ₜ vs *∈₁ₜ cargs₁ₜ a →
             --------------------------
             Γ ⊢₁ₜ constTm₁ a vs ∈₁ₜ s

  varTm₁   : x ⦂ s v∈₁ₜ Γ →
             -----------------------
             Γ ⊢₁ₜ varTm₁ x ∈₁ₜ s

data _⊢₁ₜ_*∈₁ₜ_ where
  [] : -----------------------
       Γ ⊢₁ₜ [] *∈₁ₜ []

  _∷_ : Γ ⊢₁ₜ v ∈₁ₜ s →
        Γ ⊢₁ₜ vs *∈₁ₜ ss →
        -------------------------
        Γ ⊢₁ₜ v ∷ vs *∈₁ₜ s ∷ ss

Tm₁-substₜ : Tm₁ → Tm₁ → ℕ → Tm₁
Tm₁*-substₜ : List Tm₁ → Tm₁ → ℕ → List Tm₁

Tm₁-substₜ (varTm₁ x) w y
  with x ≟ y
...  | yes _ = w
...  | no  _ = varTm₁ x
Tm₁-substₜ (constTm₁ a vs) w y = constTm₁ a (Tm₁*-substₜ vs w y)

Tm₁*-substₜ []       _ _ = []
Tm₁*-substₜ (v ∷ vs) w y = Tm₁-substₜ v w y ∷ Tm₁*-substₜ vs w y

Tm₁-wkₜ : Tm₁ → Tm₁
Tm₁*-wkₜ : List Tm₁ → List Tm₁

Tm₁-wkₜ (varTm₁ x) = varTm₁ (suc x)
Tm₁-wkₜ (constTm₁ a vs) = constTm₁ a (Tm₁*-wkₜ vs)

Tm₁*-wkₜ []       = []
Tm₁*-wkₜ (v ∷ vs) = Tm₁-wkₜ v ∷ Tm₁*-wkₜ vs

P₁-substₜ : P₁ → Tm₁ → ℕ → P₁
P₁-substₜ ⊥ₚ₁         _ _ = ⊥ₚ₁
P₁-substₜ (f $ₚ₁ vs)  w y = f $ₚ₁ Tm₁*-substₜ vs w y
P₁-substₜ (A ∧ₚ₁ B)   w y = P₁-substₜ A w y ∧ₚ₁ P₁-substₜ B w y
P₁-substₜ (A ∨ₚ₁ B)   w y = P₁-substₜ A w y ∨ₚ₁ P₁-substₜ B w y
P₁-substₜ (A →ₚ₁ B)   w y = P₁-substₜ A w y →ₚ₁ P₁-substₜ B w y
P₁-substₜ (∀ₚ₁ s ∙ A) w y = ∀ₚ₁ s ∙ P₁-substₜ A (Tm₁-wkₜ w) (suc y)

size-P₁ : P₁ → ℕ
size-P₁ ⊥ₚ₁       = 1
size-P₁ (_ $ₚ₁ _) = 1
size-P₁ (A ∧ₚ₁ B) = suc (size-P₁ A + size-P₁ B)
size-P₁ (A ∨ₚ₁ B) = suc (size-P₁ A + size-P₁ B)
size-P₁ (A →ₚ₁ B) = suc (size-P₁ A + size-P₁ B)
size-P₁ (∀ₚ₁ _ ∙ A) = suc (size-P₁ A)
