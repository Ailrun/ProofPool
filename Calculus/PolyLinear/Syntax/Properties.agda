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

useable𝕌-dec : ∀ u → Dec (useable𝕌 u)
useable𝕌-dec ∞ₗ   = yes tt
useable𝕌-dec 0/1ₗ = yes tt
useable𝕌-dec 1/1ₗ = no λ()

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
