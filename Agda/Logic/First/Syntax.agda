open import Logic.First.Signature

module Logic.First.Syntax (Sig : Signature₁) where

open import Logic.Base public
open Logic.First.Signature using (Ty₁) public
open Signature₁ Sig public

infixr 8 _,ₜ₁_
infixr 7 _$ₜ₁_

data Tm₁ : Set where
  varₜ₁ : ℕ → Tm₁
  unitₜ₁ : Tm₁
  zeroₜ₁ : Tm₁
  sucₜ₁ : Tm₁ → Tm₁
  _$ₜ₁_ : Func₁ → Tm₁ → Tm₁
  _,ₜ₁_ : Tm₁ → Tm₁ → Tm₁

infixl 12 _$ₚ₁_
infixl 11 ¬ₚ₁_
infixl 10 _∧ₚ₁_
infixl 9 _∨ₚ₁_
infixr 8 _→ₚ₁_
infixr 7 ∀ₚ₁_∙_

data P₁ : Set where
  ⊥ₚ₁ : P₁
  _$ₚ₁_ : Pred₁ → Tm₁ → P₁
  _∧ₚ₁_ : P₁ → P₁ → P₁
  _∨ₚ₁_ : P₁ → P₁ → P₁
  _→ₚ₁_ : P₁ → P₁ → P₁
  ∀ₚ₁_∙_ : Ty₁ → P₁ → P₁

¬ₚ₁_ = _→ₚ₁ ⊥ₚ₁

CtxEntry₁ = P₁ ⊎ Ty₁
Ctx₁ = List CtxEntry₁

variable
  Γ Γ′ Γ″ Δ Δ′ Δ″ Ψ Ψ′ Ψ″ : Ctx₁
  A A′ A″ B B′ B″ C C′ C″ D D′ D″ E E′ E″ : P₁
  x x′ x″ y y′ y″ z z′ z″ : ℕ
  l l′ l″ m m′ m″ n n′ n″ : CtxEntry₁
  a a′ a″ b b′ b″ c c′ c″ : Tm₁
  v v′ v″ w w′ w″ : Tm₁
  vs vs′ vs″ ws ws′ : List Tm₁
  f f′ f″ g g′ g″ h h′ h″ : Func₁
  p p′ p″ q q′ q″ r r′ r″ : Pred₁
  s s′ s″ t t′ t″ u u′ u″ : Ty₁
  ss ss′ ss″ ts ts′ ts″ us us′ us″ : List Ty₁

infix 4 _⦂_v∈ₜ₁_
infix 4 _⊢ₜ₁_∈ₜ₁_

data _⦂_v∈ₜ₁_ : ℕ → Ty₁ → Ctx₁ → Set where
  here : ----------------------
         0 ⦂ s v∈ₜ₁ inj₂ s ∷ Γ

  there₁ : x ⦂ s v∈ₜ₁ Γ →
           ----------------------
           x ⦂ s v∈ₜ₁ inj₁ A ∷ Γ

  there₂ : x ⦂ s v∈ₜ₁ Γ →
           --------------------------
           suc x ⦂ s v∈ₜ₁ inj₂ t ∷ Γ

data _⊢ₜ₁_∈ₜ₁_ : Ctx₁ → Tm₁ → Ty₁ → Set where
  varₜ₁  : x ⦂ s v∈ₜ₁ Γ →
           --------------------
           Γ ⊢ₜ₁ varₜ₁ x ∈ₜ₁ s

  unitₜ₁ : --------------------
           Γ ⊢ₜ₁ unitₜ₁ ∈ₜ₁ 1ₜ₁

  zeroₜ₁ : ---------------------
           Γ ⊢ₜ₁ zeroₜ₁ ∈ₜ₁ ℕₜ₁

  sucₜ₁  : Γ ⊢ₜ₁ v ∈ₜ₁ ℕₜ₁ →
           ----------------------
           Γ ⊢ₜ₁ sucₜ₁ v ∈ₜ₁ ℕₜ₁

  _$ₜ₁_  : Γ ⊢ₜ₁ v ∈ₜ₁ fargₜ₁ f →
           ---------------------------
           Γ ⊢ₜ₁ f $ₜ₁ v ∈ₜ₁ fresₜ₁ f

  _,ₜ₁_  : Γ ⊢ₜ₁ v ∈ₜ₁ s →
           Γ ⊢ₜ₁ w ∈ₜ₁ t →
           --------------------------
           Γ ⊢ₜ₁ v ,ₜ₁ w ∈ₜ₁ s ×ₜ₁ t

Tm₁-substₜ : Tm₁ → Tm₁ → ℕ → Tm₁
Tm₁-substₜ (varₜ₁ x)  w y
  with x ≟ y
...  | yes _ = w
...  | no  _ = varₜ₁ x
Tm₁-substₜ unitₜ₁     _ _ = unitₜ₁
Tm₁-substₜ zeroₜ₁     _ _ = zeroₜ₁
Tm₁-substₜ (sucₜ₁ v)  w y = sucₜ₁ (Tm₁-substₜ v w y)
Tm₁-substₜ (f $ₜ₁ v)  w y = f $ₜ₁ Tm₁-substₜ v w y
Tm₁-substₜ (v ,ₜ₁ v′) w y = Tm₁-substₜ v w y ,ₜ₁ Tm₁-substₜ v′ w y

Tm₁-wkₜ : Tm₁ → Tm₁
Tm₁-wkₜ (varₜ₁ x) = varₜ₁ (suc x)
Tm₁-wkₜ unitₜ₁ = unitₜ₁
Tm₁-wkₜ zeroₜ₁ = zeroₜ₁
Tm₁-wkₜ (sucₜ₁ v) = sucₜ₁ (Tm₁-wkₜ v)
Tm₁-wkₜ (f $ₜ₁ v) = f $ₜ₁ Tm₁-wkₜ v
Tm₁-wkₜ (v ,ₜ₁ v′) = Tm₁-wkₜ v ,ₜ₁ Tm₁-wkₜ v′

P₁-substₜ : P₁ → Tm₁ → ℕ → P₁
P₁-substₜ ⊥ₚ₁         _ _ = ⊥ₚ₁
P₁-substₜ (f $ₚ₁ vs)  w y = f $ₚ₁ Tm₁-substₜ vs w y
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
