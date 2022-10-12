module Calculus.PolyLinear.Rules.Properties where

open import Calculus.PolyLinear.Syntax
open import Calculus.PolyLinear.Syntax.Properties
open import Calculus.PolyLinear.Rules
open import Data.Product
open import Relation.Binary.PropositionalEquality

𝕂∈-det : x ⦂ K′ 𝕂∈ Γ →
         x ⦂ K″ 𝕂∈ Γ →
         --------------
         K′ ≡ K″
𝕂∈-det (here refl) (here refl)    = refl
𝕂∈-det (there𝕋 x∈₀)  (there𝕋 x∈₁)
  rewrite 𝕂∈-det x∈₀ x∈₁          = refl
𝕂∈-det (there𝕂 x∈₀)  (there𝕂 x∈₁)
  rewrite 𝕂∈-det x∈₀ x∈₁          = refl

𝕋∈-det : x ⦂ T′ 𝕋∈ Γ / Γ′ →
         x ⦂ T″ 𝕋∈ Γ / Γ″ →
         -------------------
         T′ ≡ T″ × Γ′ ≡ Γ″
𝕋∈-det (here refl)   (here refl)    = refl , refl
𝕋∈-det (there𝕋 x∈₀)  (there𝕋 x∈₁)
  with refl , refl ← 𝕋∈-det x∈₀ x∈₁ = refl , refl
𝕋∈-det (there𝕂 x∈₀)  (there𝕂 x∈₁)
  with refl , refl ← 𝕋∈-det x∈₀ x∈₁ = refl , refl

T∈-preserves-extractℂ⁻ : x ⦂ T′ 𝕋∈ Γ / Γ′ →
                         ---------------------------
                         extractℂ⁻ Γ ≡ extractℂ⁻ Γ′
T∈-preserves-extractℂ⁻ (here _)    = refl
T∈-preserves-extractℂ⁻ (there𝕋 x∈) = cong (_ 𝕋∷_) (T∈-preserves-extractℂ⁻ x∈)
T∈-preserves-extractℂ⁻ (there𝕂 x∈) = cong (_ 𝕂∷_) (T∈-preserves-extractℂ⁻ x∈)

𝕋⊢-det : Γ 𝕋⊢ T ⦂ K′ →
         Γ 𝕋⊢ T ⦂ K″ →
         --------------
         K′ ≡ K″
𝕋⊢-det (tvarₗ x∈₀)  (tvarₗ x∈₁)  = 𝕂∈-det x∈₀ x∈₁
𝕋⊢-det (⊢T₀ ⊸ₗ ⊢U₀) (⊢T₁ ⊸ₗ ⊢U₁) = refl
𝕋⊢-det (!ₗ ⊢T₀)     (!ₗ ⊢T₁)     = refl
𝕋⊢-det (∀ₗ⋆∙ ⊢T₀)   (∀ₗ⋆∙ ⊢T₁)   = refl

𝕄⊢-det : Γ 𝕄⊢ M ⦂ T′ / Γ′ →
         Γ 𝕄⊢ M ⦂ T″ / Γ″ →
         -------------------
         T′ ≡ T″ × Γ′ ≡ Γ″
𝕄⊢-det (varₗ x∈₀)              (varₗ x∈₁)              = 𝕋∈-det x∈₀ x∈₁
𝕄⊢-det (λₗ _ ∘ ⊢M₀)            (λₗ _ ∘ ⊢M₁)
  with refl , refl ← 𝕄⊢-det ⊢M₀ ⊢M₁                    = refl , refl
𝕄⊢-det (⊢M₀ $ₗ∘ ⊢N₀)           (⊢M₁ $ₗ∘ ⊢N₁)
  with refl , refl ← 𝕄⊢-det ⊢M₀ ⊢M₁                    = refl , proj₂ (𝕄⊢-det ⊢N₀ ⊢N₁)
𝕄⊢-det (bangₗ ⊢M₀)             (bangₗ ⊢M₁)             = cong !ₗ_ (proj₁ (𝕄⊢-det ⊢M₀ ⊢M₁)) , refl
𝕄⊢-det (let-bangₗ ⊢M₀ inₗ ⊢N₀) (let-bangₗ ⊢M₁ inₗ ⊢N₁)
  with refl , refl ← 𝕄⊢-det ⊢M₀ ⊢M₁
    with refl , refl ← 𝕄⊢-det ⊢N₀ ⊢N₁                  = refl , refl
𝕄⊢-det (Λₗ⋆∙ ⊢M₀)              (Λₗ⋆∙ ⊢M₁)
  with refl , refl ← 𝕄⊢-det ⊢M₀ ⊢M₁                    = refl , refl
𝕄⊢-det (⊢M₀ $$ₗ∙ ⊢T₀)          (⊢M₁ $$ₗ∙ ⊢T₁)
  with refl , refl ← 𝕄⊢-det ⊢M₀ ⊢M₁                    = refl , refl

𝕄⊢-preserves-extractℂ⁻ : Γ 𝕄⊢ M ⦂ T′ / Γ′ →
                         ---------------------------
                         extractℂ⁻ Γ ≡ extractℂ⁻ Γ′
𝕄⊢-preserves-extractℂ⁻ (varₗ x∈)             = T∈-preserves-extractℂ⁻ x∈
𝕄⊢-preserves-extractℂ⁻ (λₗ _ ∘ ⊢M)           = ℂ⁻-𝕋∷-injectiveʳ (𝕄⊢-preserves-extractℂ⁻ ⊢M)
𝕄⊢-preserves-extractℂ⁻ (⊢M $ₗ∘ ⊢N)           = trans (𝕄⊢-preserves-extractℂ⁻ ⊢M) (𝕄⊢-preserves-extractℂ⁻ ⊢N)
𝕄⊢-preserves-extractℂ⁻ (bangₗ ⊢M)            = refl
𝕄⊢-preserves-extractℂ⁻ (let-bangₗ ⊢M inₗ ⊢N) = trans (𝕄⊢-preserves-extractℂ⁻ ⊢M) (ℂ⁻-𝕋∷-injectiveʳ (𝕄⊢-preserves-extractℂ⁻ ⊢N))
𝕄⊢-preserves-extractℂ⁻ (Λₗ⋆∙ ⊢M)             = ℂ⁻-𝕂∷-injectiveʳ (𝕄⊢-preserves-extractℂ⁻ ⊢M)
𝕄⊢-preserves-extractℂ⁻ (⊢M $$ₗ∙ ⊢T)          = 𝕄⊢-preserves-extractℂ⁻ ⊢M
