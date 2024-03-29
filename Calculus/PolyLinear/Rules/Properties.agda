module Calculus.PolyLinear.Rules.Properties where

open import Calculus.PolyLinear.Syntax
open import Calculus.PolyLinear.Syntax.Properties
open import Calculus.PolyLinear.Rules
open import Data.List
open import Data.List.Properties
open import Data.Product
open import Data.List.Relation.Binary.Pointwise hiding (refl)
open import Relation.Binary.PropositionalEquality

≤𝕌-trans : u  ≤𝕌 u′ →
           u′ ≤𝕌 u″ →
           -----------
           u  ≤𝕌 u″
≤𝕌-trans refl      ≤u″  = ≤u″
≤𝕌-trans 0/1ₗ≤1/1ₗ refl = 0/1ₗ≤1/1ₗ

≤𝕌-inc𝕌 : .{p : useable𝕌 u} → u ≤𝕌 inc𝕌 u p
≤𝕌-inc𝕌 {∞ₗ}   = refl
≤𝕌-inc𝕌 {0/1ₗ} = 0/1ₗ≤1/1ₗ

≤𝕌ℂ𝔼-refl : E ≤𝕌ℂ𝔼 E
≤𝕌ℂ𝔼-refl {K       /𝕂} = refl/𝕂
≤𝕌ℂ𝔼-refl {(T , u) /𝕋} = refl /𝕋

≤𝕌ℂ𝔼-trans : E  ≤𝕌ℂ𝔼 E′ →
             E′ ≤𝕌ℂ𝔼 E″ →
             -------------
             E  ≤𝕌ℂ𝔼 E″
≤𝕌ℂ𝔼-trans refl/𝕂   ≤E″      = ≤E″
≤𝕌ℂ𝔼-trans (≤u′ /𝕋) (≤u″ /𝕋) = ≤𝕌-trans ≤u′ ≤u″ /𝕋

/𝕋≤𝕌ℂ𝔼inc𝕌/𝕋 : .{p : useable𝕌 u} → (T , u) /𝕋 ≤𝕌ℂ𝔼 (T , inc𝕌 u p) /𝕋
/𝕋≤𝕌ℂ𝔼inc𝕌/𝕋 = ≤𝕌-inc𝕌 /𝕋

≤𝕌ℂ-refl : Γ ≤𝕌ℂ Γ
≤𝕌ℂ-refl {[]}    = []
≤𝕌ℂ-refl {_ ∷ _} = ≤𝕌ℂ𝔼-refl ∷ ≤𝕌ℂ-refl

≤𝕌ℂ-trans : Γ ≤𝕌ℂ Γ′ →
            Γ′ ≤𝕌ℂ Γ″ →
            ------------
            Γ ≤𝕌ℂ Γ″
≤𝕌ℂ-trans []          []          = []
≤𝕌ℂ-trans (≤E′ ∷ ≤Γ′) (≤E″ ∷ ≤Γ″) = ≤𝕌ℂ𝔼-trans ≤E′ ≤E″ ∷ ≤𝕌ℂ-trans ≤Γ′ ≤Γ″

𝕂∈-det : x ⦂ K′ 𝕂∈ Γ →
         x ⦂ K″ 𝕂∈ Γ →
         --------------
         K′ ≡ K″
𝕂∈-det (here refl) (here refl) = refl
𝕂∈-det (there x∈₀) (there x∈₁) = 𝕂∈-det x∈₀ x∈₁

𝕋∈-det : x ⦂ T′ 𝕋∈ Γ / Γ′ →
         x ⦂ T″ 𝕋∈ Γ / Γ″ →
         -------------------
         T′ ≡ T″ × Γ′ ≡ Γ″
𝕋∈-det (here refl) (here refl)      = refl , refl
𝕋∈-det (there x∈₀) (there x∈₁)
  with refl , refl ← 𝕋∈-det x∈₀ x∈₁ = refl , refl

𝕋∈-det₁ : x ⦂ T′ 𝕋∈ Γ / Γ′ →
          x ⦂ T″ 𝕋∈ Γ / Γ″ →
          -------------------
          T′ ≡ T″
𝕋∈-det₁ x∈₀ x∈₁ = proj₁ (𝕋∈-det x∈₀ x∈₁)

𝕋∈-det₂ : x ⦂ T′ 𝕋∈ Γ / Γ′ →
          x ⦂ T″ 𝕋∈ Γ / Γ″ →
          -------------------
          Γ′ ≡ Γ″
𝕋∈-det₂ x∈₀ x∈₁ = proj₂ (𝕋∈-det x∈₀ x∈₁)

T∈-preserves-extractℂ⁻ : x ⦂ T′ 𝕋∈ Γ / Γ′ →
                         ---------------------------
                         extractℂ⁻ Γ ≡ extractℂ⁻ Γ′
T∈-preserves-extractℂ⁻ {Γ = _ ∷ _}    (here _)   = refl
T∈-preserves-extractℂ⁻ {Γ = _ /𝕂 ∷ _} (there x∈) = cong (_ ∷_) (T∈-preserves-extractℂ⁻ x∈)
T∈-preserves-extractℂ⁻ {Γ = _ /𝕋 ∷ _} (there x∈) = cong (_ ∷_) (T∈-preserves-extractℂ⁻ x∈)

T∈⇒≤𝕌 : x ⦂ T′ 𝕋∈ Γ / Γ′ →
        ---------------------------
        Γ ≤𝕌ℂ Γ′
T∈⇒≤𝕌 (here _)   = /𝕋≤𝕌ℂ𝔼inc𝕌/𝕋 ∷ ≤𝕌ℂ-refl
T∈⇒≤𝕌 (there x∈) = ≤𝕌ℂ𝔼-refl ∷ T∈⇒≤𝕌 x∈

𝕋⊢-det : Γ 𝕋⊢ T ⦂ K′ →
         Γ 𝕋⊢ T ⦂ K″ →
         --------------
         K′ ≡ K″
𝕋⊢-det (tvarₗ _ x∈₀) (tvarₗ _ x∈₁) = 𝕂∈-det x∈₀ x∈₁
𝕋⊢-det (⊢T₀ ⊸ₗ ⊢U₀)  (⊢T₁ ⊸ₗ ⊢U₁)  = refl
𝕋⊢-det (!ₗ ⊢T₀)      (!ₗ ⊢T₁)      = refl
𝕋⊢-det (∀ₗ⋆∙ ⊢T₀)    (∀ₗ⋆∙ ⊢T₁)    = refl

𝕄⊢-det : Γ 𝕄⊢ M ⦂ T′ / Γ′ →
         Γ 𝕄⊢ M ⦂ T″ / Γ″ →
         -------------------
         T′ ≡ T″ × Γ′ ≡ Γ″
𝕄⊢-det (varₗ x∈₀)              (varₗ x∈₁)              = 𝕋∈-det x∈₀ x∈₁
𝕄⊢-det (λₗ _ ∘ ⊢M₀)            (λₗ _ ∘ ⊢M₁)
  with T′≡ , refl ← 𝕄⊢-det ⊢M₀ ⊢M₁
    with refl ← wk𝕋-injective _ _ _ _ T′≡              = refl , refl
𝕄⊢-det (⊢M₀ $ₗ∘ ⊢N₀)           (⊢M₁ $ₗ∘ ⊢N₁)
  with refl , refl ← 𝕄⊢-det ⊢M₀ ⊢M₁                    = refl , proj₂ (𝕄⊢-det ⊢N₀ ⊢N₁)
𝕄⊢-det (bangₗ ⊢M₀)             (bangₗ ⊢M₁)             = cong !ₗ_ (proj₁ (𝕄⊢-det ⊢M₀ ⊢M₁)) , refl
𝕄⊢-det (let-bangₗ ⊢M₀ inₗ ⊢N₀) (let-bangₗ ⊢M₁ inₗ ⊢N₁)
  with refl , refl ← 𝕄⊢-det ⊢M₀ ⊢M₁
    with T′≡ , refl ← 𝕄⊢-det ⊢N₀ ⊢N₁
      with refl ← wk𝕋-injective _ _ _ _ T′≡            = refl , refl
𝕄⊢-det (Λₗ⋆∙ ⊢M₀)              (Λₗ⋆∙ ⊢M₁)
  with refl , refl ← 𝕄⊢-det ⊢M₀ ⊢M₁                    = refl , refl
𝕄⊢-det (⊢M₀ $$ₗ∙ ⊢T₀)          (⊢M₁ $$ₗ∙ ⊢T₁)
  with refl , refl ← 𝕄⊢-det ⊢M₀ ⊢M₁                    = refl , refl

𝕄⊢-det₁ : Γ 𝕄⊢ M ⦂ T′ / Γ′ →
          Γ 𝕄⊢ M ⦂ T″ / Γ″ →
          -------------------
          T′ ≡ T″
𝕄⊢-det₁ ⊢M₀ ⊢M₁ = proj₁ (𝕄⊢-det ⊢M₀ ⊢M₁)

𝕄⊢-det₂ : Γ 𝕄⊢ M ⦂ T′ / Γ′ →
          Γ 𝕄⊢ M ⦂ T″ / Γ″ →
          -------------------
          Γ′ ≡ Γ″
𝕄⊢-det₂ ⊢M₀ ⊢M₁ = proj₂ (𝕄⊢-det ⊢M₀ ⊢M₁)

𝕄⊢-preserves-extractℂ⁻ : Γ 𝕄⊢ M ⦂ T′ / Γ′ →
                         ---------------------------
                         extractℂ⁻ Γ ≡ extractℂ⁻ Γ′
𝕄⊢-preserves-extractℂ⁻ (varₗ x∈)             = T∈-preserves-extractℂ⁻ x∈
𝕄⊢-preserves-extractℂ⁻ (λₗ _ ∘ ⊢M)           = ∷-injectiveʳ (𝕄⊢-preserves-extractℂ⁻ ⊢M)
𝕄⊢-preserves-extractℂ⁻ (⊢M $ₗ∘ ⊢N)           = trans (𝕄⊢-preserves-extractℂ⁻ ⊢M) (𝕄⊢-preserves-extractℂ⁻ ⊢N)
𝕄⊢-preserves-extractℂ⁻ (bangₗ ⊢M)            = refl
𝕄⊢-preserves-extractℂ⁻ (let-bangₗ ⊢M inₗ ⊢N) = trans (𝕄⊢-preserves-extractℂ⁻ ⊢M) (∷-injectiveʳ (𝕄⊢-preserves-extractℂ⁻ ⊢N))
𝕄⊢-preserves-extractℂ⁻ (Λₗ⋆∙ ⊢M)             = ∷-injectiveʳ (𝕄⊢-preserves-extractℂ⁻ ⊢M)
𝕄⊢-preserves-extractℂ⁻ (⊢M $$ₗ∙ ⊢T)          = 𝕄⊢-preserves-extractℂ⁻ ⊢M

𝕄⊢⇒≤𝕌ℂ : Γ 𝕄⊢ M ⦂ T′ / Γ′ →
        ---------------------------
        Γ ≤𝕌ℂ Γ′
𝕄⊢⇒≤𝕌ℂ (varₗ x∈)             = T∈⇒≤𝕌 x∈
𝕄⊢⇒≤𝕌ℂ (λₗ _ ∘ ⊢M)
  with _ ∷ Γ≤ ← 𝕄⊢⇒≤𝕌ℂ ⊢M    = Γ≤
𝕄⊢⇒≤𝕌ℂ (⊢M $ₗ∘ ⊢N)           = ≤𝕌ℂ-trans (𝕄⊢⇒≤𝕌ℂ ⊢M) (𝕄⊢⇒≤𝕌ℂ ⊢N)
𝕄⊢⇒≤𝕌ℂ (bangₗ ⊢M)            = 𝕄⊢⇒≤𝕌ℂ ⊢M
𝕄⊢⇒≤𝕌ℂ (let-bangₗ ⊢M inₗ ⊢N)
  with _ ∷ Γ′≤ ← 𝕄⊢⇒≤𝕌ℂ ⊢N   = ≤𝕌ℂ-trans (𝕄⊢⇒≤𝕌ℂ ⊢M) Γ′≤
𝕄⊢⇒≤𝕌ℂ (Λₗ⋆∙ ⊢M)
  with _ ∷ Γ≤ ← 𝕄⊢⇒≤𝕌ℂ ⊢M    = Γ≤
𝕄⊢⇒≤𝕌ℂ (⊢M $$ₗ∙ ⊢T)          = 𝕄⊢⇒≤𝕌ℂ ⊢M
