module Calculus.PolyLinear.Syntax.Properties where

open import Calculus.PolyLinear.Syntax
open import Data.Nat
open import Data.Product using (_,_; uncurry)
open import Data.Unit using (tt)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary hiding (Irrelevant)
open import Relation.Nullary.Decidable using () renaming (map′ to Dec-map′)
open import Relation.Nullary.Product

𝕂-≡-dec : DecidableEquality 𝕂
𝕂-≡-dec Tyₗ Tyₗ = yes refl

𝕋-≡-dec : DecidableEquality 𝕋
𝕋-≡-dec (tvarₗ x₀)   (tvarₗ x₁)   = Dec-map′ (cong tvarₗ) (λ{ refl → refl }) (x₀ ≟ x₁)
𝕋-≡-dec (tvarₗ x₀)   (T₁ ⊸ₗ U₁)   = no λ()
𝕋-≡-dec (tvarₗ x₀)   (!ₗ T₁)      = no λ()
𝕋-≡-dec (tvarₗ x₀)   (∀ₗ K₁ ∙ T₁) = no λ()
𝕋-≡-dec (T₀ ⊸ₗ U₀)   (tvarₗ x₁)   = no λ()
𝕋-≡-dec (T₀ ⊸ₗ U₀)   (T₁ ⊸ₗ U₁)   = Dec-map′ (uncurry (cong₂ _⊸ₗ_)) (λ{ refl → refl , refl }) ((𝕋-≡-dec T₀ T₁) ×-dec (𝕋-≡-dec U₀ U₁))
𝕋-≡-dec (T₀ ⊸ₗ U₀)   (!ₗ T₁)      = no λ()
𝕋-≡-dec (T₀ ⊸ₗ U₀)   (∀ₗ K₁ ∙ T₁) = no λ()
𝕋-≡-dec (!ₗ T₀)      (tvarₗ x₁)   = no λ()
𝕋-≡-dec (!ₗ T₀)      (T₁ ⊸ₗ U₁)   = no λ()
𝕋-≡-dec (!ₗ T₀)      (!ₗ T₁)      = Dec-map′ (cong !ₗ_) (λ{ refl → refl }) (𝕋-≡-dec T₀ T₁)
𝕋-≡-dec (!ₗ T₀)      (∀ₗ K₁ ∙ T₁) = no λ()
𝕋-≡-dec (∀ₗ K₀ ∙ T₀) (tvarₗ x₁)   = no λ()
𝕋-≡-dec (∀ₗ K₀ ∙ T₀) (T₁ ⊸ₗ U₁)   = no λ()
𝕋-≡-dec (∀ₗ K₀ ∙ T₀) (!ₗ T₁)      = no λ()
𝕋-≡-dec (∀ₗ K₀ ∙ T₀) (∀ₗ K₁ ∙ T₁) = Dec-map′ (uncurry (cong₂ ∀ₗ_∙_)) (λ{ refl → refl , refl }) ((𝕂-≡-dec K₀ K₁) ×-dec (𝕋-≡-dec T₀ T₁))

𝕌-≡-dec : DecidableEquality 𝕌
𝕌-≡-dec ∞ₗ   ∞ₗ   = yes refl
𝕌-≡-dec ∞ₗ   0/1ₗ = no λ ()
𝕌-≡-dec ∞ₗ   1/1ₗ = no λ ()
𝕌-≡-dec 0/1ₗ ∞ₗ   = no λ ()
𝕌-≡-dec 0/1ₗ 0/1ₗ = yes refl
𝕌-≡-dec 0/1ₗ 1/1ₗ = no λ ()
𝕌-≡-dec 1/1ₗ ∞ₗ   = no λ ()
𝕌-≡-dec 1/1ₗ 0/1ₗ = no λ ()
𝕌-≡-dec 1/1ₗ 1/1ₗ = yes refl

ℂ-≡-dec : DecidableEquality ℂ
ℂ-≡-dec []                []                = yes refl
ℂ-≡-dec []                (K₁        𝕂∷ Γ₁) = no (λ ())
ℂ-≡-dec []                ((T₁ , u₁) 𝕋∷ Γ₁) = no (λ ())
ℂ-≡-dec (K₀        𝕂∷ Γ₀) []                = no (λ ())
ℂ-≡-dec (K₀        𝕂∷ Γ₀) (K₁        𝕂∷ Γ₁) = Dec-map′ (λ{ (refl , refl) → refl }) (λ{ refl → refl , refl }) ((𝕂-≡-dec K₀ K₁) ×-dec (ℂ-≡-dec Γ₀ Γ₁))
ℂ-≡-dec (K₀        𝕂∷ Γ₀) ((T₁ , u₁) 𝕋∷ Γ₁) = no (λ ())
ℂ-≡-dec ((T₀ , u₀) 𝕋∷ Γ₀) []                = no (λ ())
ℂ-≡-dec ((T₀ , u₀) 𝕋∷ Γ₀) (K₁        𝕂∷ Γ₁) = no (λ ())
ℂ-≡-dec ((T₀ , u₀) 𝕋∷ Γ₀) ((T₁ , u₁) 𝕋∷ Γ₁) = Dec-map′ (λ{ (refl , refl , refl) → refl }) (λ{ refl → refl , refl , refl }) ((𝕋-≡-dec T₀ T₁) ×-dec (𝕌-≡-dec u₀ u₁) ×-dec (ℂ-≡-dec Γ₀ Γ₁))

useable𝕌-dec : ∀ u → Dec (useable𝕌 u)
useable𝕌-dec ∞ₗ   = yes tt
useable𝕌-dec 0/1ₗ = yes tt
useable𝕌-dec 1/1ₗ = no λ()

𝕋-⊸ₗ-injectiveˡ : T ⊸ₗ U ≡ T′ ⊸ₗ U′ →
                  T ≡ T′
𝕋-⊸ₗ-injectiveˡ refl = refl

𝕋-⊸ₗ-injectiveʳ : T ⊸ₗ U ≡ T′ ⊸ₗ U′ →
                  U ≡ U′
𝕋-⊸ₗ-injectiveʳ refl = refl

𝕋-!ₗ-injective : !ₗ T ≡ !ₗ T′ →
                 T ≡ T′
𝕋-!ₗ-injective refl = refl

𝕋-∀ₗ∙-injectiveˡ : ∀ₗ K ∙ T ≡ ∀ₗ K′ ∙ T′ →
                   K ≡ K′
𝕋-∀ₗ∙-injectiveˡ refl = refl

𝕋-∀ₗ∙-injectiveʳ : ∀ₗ K ∙ T ≡ ∀ₗ K′ ∙ T′ →
                   T ≡ T′
𝕋-∀ₗ∙-injectiveʳ refl = refl

ℂ-𝕋∷-injectiveˡ : _≡_ {A = ℂ} ((T , u) 𝕋∷ Γ) ((T′ , u′) 𝕋∷ Γ′) →
                  -----------------------------------------------
                  (T , u) ≡ (T′ , u′)
ℂ-𝕋∷-injectiveˡ refl = refl

ℂ-𝕋∷-injectiveˡ₁ : _≡_ {A = ℂ} ((T , u) 𝕋∷ Γ) ((T′ , u′) 𝕋∷ Γ′) →
                   -----------------------------------------------
                   T ≡ T′
ℂ-𝕋∷-injectiveˡ₁ refl = refl

ℂ-𝕋∷-injectiveˡ₂ : _≡_ {A = ℂ} ((T , u) 𝕋∷ Γ) ((T′ , u′) 𝕋∷ Γ′) →
                   -----------------------------------------------
                   u ≡ u′
ℂ-𝕋∷-injectiveˡ₂ refl = refl

ℂ-𝕋∷-injectiveʳ : _≡_ {A = ℂ} ((T , u) 𝕋∷ Γ) ((T′ , u′) 𝕋∷ Γ′) →
                  -----------------------------------------------
                  Γ ≡ Γ′
ℂ-𝕋∷-injectiveʳ refl = refl

ℂ-𝕂∷-injectiveˡ : _≡_ {A = ℂ} (K 𝕂∷ Γ) (K′ 𝕂∷ Γ′) →
                  ----------------------------------
                  K ≡ K′
ℂ-𝕂∷-injectiveˡ refl = refl

ℂ-𝕂∷-injectiveʳ : _≡_ {A = ℂ} (K 𝕂∷ Γ) (K′ 𝕂∷ Γ′) →
                  ----------------------------------
                  Γ ≡ Γ′
ℂ-𝕂∷-injectiveʳ refl = refl

ℂ⁻-𝕋∷-injectiveˡ : _≡_ {A = ℂ⁻} (T 𝕋∷ Γ⁻) (T′ 𝕋∷ Γ⁻′) →
                   T ≡ T′
ℂ⁻-𝕋∷-injectiveˡ refl = refl

ℂ⁻-𝕋∷-injectiveʳ : _≡_ {A = ℂ⁻} (T 𝕋∷ Γ⁻) (T′ 𝕋∷ Γ⁻′) →
                   Γ⁻ ≡ Γ⁻′
ℂ⁻-𝕋∷-injectiveʳ refl = refl

ℂ⁻-𝕂∷-injectiveˡ : _≡_ {A = ℂ⁻} (K 𝕂∷ Γ⁻) (K′ 𝕂∷ Γ⁻′) →
                   K ≡ K′
ℂ⁻-𝕂∷-injectiveˡ refl = refl

ℂ⁻-𝕂∷-injectiveʳ : _≡_ {A = ℂ⁻} (K 𝕂∷ Γ⁻) (K′ 𝕂∷ Γ⁻′) →
                   Γ⁻ ≡ Γ⁻′
ℂ⁻-𝕂∷-injectiveʳ refl = refl
