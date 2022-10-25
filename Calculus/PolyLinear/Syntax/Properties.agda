module Calculus.PolyLinear.Syntax.Properties where

open import Calculus.PolyLinear.Syntax
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Tactic.RingSolver as ℕTactic
open import Data.List
open import Data.List.Properties
open import Data.Product using (_×_; _,_; curry; uncurry; proj₁; proj₂)
open import Data.Unit using (tt)
open import Function
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary hiding (Irrelevant)
open import Relation.Nullary.Decidable using (dec-yes; dec-yes-irr; dec-no) renaming (map′ to Dec-map′)

𝕋-tvarₗ-injective : tvarₗ x ≡ tvarₗ x′ →
                    x ≡ x′
𝕋-tvarₗ-injective refl = refl

𝕋-⊸ₗ-injectiveˡ : T ⊸ₗ U ≡ T′ ⊸ₗ U′ →
                  T ≡ T′
𝕋-⊸ₗ-injectiveˡ refl = refl

𝕋-⊸ₗ-injectiveʳ : T ⊸ₗ U ≡ T′ ⊸ₗ U′ →
                  U ≡ U′
𝕋-⊸ₗ-injectiveʳ refl = refl

𝕋-⊸ₗ-injective : T ⊸ₗ U ≡ T′ ⊸ₗ U′ →
                 T ≡ T′ × U ≡ U′
𝕋-⊸ₗ-injective refl = refl , refl

𝕋-!ₗ-injective : !ₗ T ≡ !ₗ T′ →
                 T ≡ T′
𝕋-!ₗ-injective refl = refl

𝕋-∀ₗ∙-injectiveˡ : ∀ₗ K ∙ T ≡ ∀ₗ K′ ∙ T′ →
                   K ≡ K′
𝕋-∀ₗ∙-injectiveˡ refl = refl

𝕋-∀ₗ∙-injectiveʳ : ∀ₗ K ∙ T ≡ ∀ₗ K′ ∙ T′ →
                   T ≡ T′
𝕋-∀ₗ∙-injectiveʳ refl = refl

𝕋-∀ₗ∙-injective : ∀ₗ K ∙ T ≡ ∀ₗ K′ ∙ T′ →
                  K ≡ K′ × T ≡ T′
𝕋-∀ₗ∙-injective refl = refl , refl

ℂ𝔼-/𝕂-injective : _≡_ {A = ℂ𝔼} (K /𝕂) (K′ /𝕂) →
                  K ≡ K′
ℂ𝔼-/𝕂-injective refl = refl

ℂ𝔼-/𝕋-injective₁ : _≡_ {A = ℂ𝔼} ((T , u) /𝕋) ((T′ , u′) /𝕋) →
                   T ≡ T′
ℂ𝔼-/𝕋-injective₁ refl = refl

ℂ𝔼-/𝕋-injective₂ : _≡_ {A = ℂ𝔼} ((T , u) /𝕋) ((T′ , u′) /𝕋) →
                   u ≡ u′
ℂ𝔼-/𝕋-injective₂ refl = refl

ℂ𝔼-/𝕋-injective : _≡_ {A = ℂ𝔼} ((T , u) /𝕋) ((T′ , u′) /𝕋) →
                  T ≡ T′ × u ≡ u′
ℂ𝔼-/𝕋-injective refl = refl , refl

ℂ𝔼⁻-/𝕂-injective : _≡_ {A = ℂ𝔼⁻} (K /𝕂) (K′ /𝕂) →
                   K ≡ K′
ℂ𝔼⁻-/𝕂-injective refl = refl

ℂ𝔼⁻-/𝕋-injective : _≡_ {A = ℂ𝔼⁻} (T /𝕋) (T′ /𝕋) →
                   T ≡ T′
ℂ𝔼⁻-/𝕋-injective refl = refl

𝕄-varₗ-injective : varₗ x ≡ varₗ x′ →
                   x ≡ x′
𝕄-varₗ-injective refl = refl

𝕄-λₗ∘-injectiveˡ : λₗ T ∘ M ≡ λₗ T′ ∘ M′ →
                   T ≡ T′
𝕄-λₗ∘-injectiveˡ refl = refl

𝕄-λₗ∘-injectiveʳ : λₗ T ∘ M ≡ λₗ T′ ∘ M′ →
                   M ≡ M′
𝕄-λₗ∘-injectiveʳ refl = refl

𝕄-$ₗ∘-injectiveˡ : M $ₗ∘ N ≡ M′ $ₗ∘ N′ →
                   M ≡ M′
𝕄-$ₗ∘-injectiveˡ refl = refl

𝕄-$ₗ∘-injectiveʳ : M $ₗ∘ N ≡ M′ $ₗ∘ N′ →
                   N ≡ N′
𝕄-$ₗ∘-injectiveʳ refl = refl

𝕄-bangₗ-injective : bangₗ M ≡ bangₗ M′ →
                     M ≡ M′
𝕄-bangₗ-injective refl = refl

𝕄-let-bangₗ-inₗ-injectiveˡ : let-bangₗ M inₗ N ≡ let-bangₗ M′ inₗ N′ →
                             M ≡ M′
𝕄-let-bangₗ-inₗ-injectiveˡ refl = refl

𝕄-let-bangₗ-inₗ-injectiveʳ : let-bangₗ M inₗ N ≡ let-bangₗ M′ inₗ N′ →
                             N ≡ N′
𝕄-let-bangₗ-inₗ-injectiveʳ refl = refl

𝕄-Λₗ∙-injectiveˡ : Λₗ K ∙ M ≡ Λₗ K′ ∙ M′ →
                   K ≡ K′
𝕄-Λₗ∙-injectiveˡ refl = refl

𝕄-Λₗ∙-injectiveʳ : Λₗ K ∙ M ≡ Λₗ K′ ∙ M′ →
                   M ≡ M′
𝕄-Λₗ∙-injectiveʳ refl = refl

𝕄-$$ₗ∙-injectiveˡ : M $$ₗ∙ T ≡ M′ $$ₗ∙ T′ →
                    M ≡ M′
𝕄-$$ₗ∙-injectiveˡ refl = refl

𝕄-$$ₗ∙-injectiveʳ : M $$ₗ∙ T ≡ M′ $$ₗ∙ T′ →
                    T ≡ T′
𝕄-$$ₗ∙-injectiveʳ refl = refl

𝕂-≡-dec : DecidableEquality 𝕂
𝕂-≡-dec Tyₗ Tyₗ = yes refl

𝕋-≡-dec : DecidableEquality 𝕋
𝕋-≡-dec (tvarₗ x₀)   (tvarₗ x₁)   = Dec-map′ (cong tvarₗ) 𝕋-tvarₗ-injective (x₀ ≟ x₁)
𝕋-≡-dec (tvarₗ x₀)   (T₁ ⊸ₗ U₁)   = no λ()
𝕋-≡-dec (tvarₗ x₀)   (!ₗ T₁)      = no λ()
𝕋-≡-dec (tvarₗ x₀)   (∀ₗ K₁ ∙ T₁) = no λ()
𝕋-≡-dec (T₀ ⊸ₗ U₀)   (tvarₗ x₁)   = no λ()
𝕋-≡-dec (T₀ ⊸ₗ U₀)   (T₁ ⊸ₗ U₁)   = Dec-map′ (uncurry (cong₂ _⊸ₗ_)) 𝕋-⊸ₗ-injective ((𝕋-≡-dec T₀ T₁) ×-dec (𝕋-≡-dec U₀ U₁))
𝕋-≡-dec (T₀ ⊸ₗ U₀)   (!ₗ T₁)      = no λ()
𝕋-≡-dec (T₀ ⊸ₗ U₀)   (∀ₗ K₁ ∙ T₁) = no λ()
𝕋-≡-dec (!ₗ T₀)      (tvarₗ x₁)   = no λ()
𝕋-≡-dec (!ₗ T₀)      (T₁ ⊸ₗ U₁)   = no λ()
𝕋-≡-dec (!ₗ T₀)      (!ₗ T₁)      = Dec-map′ (cong !ₗ_) 𝕋-!ₗ-injective (𝕋-≡-dec T₀ T₁)
𝕋-≡-dec (!ₗ T₀)      (∀ₗ K₁ ∙ T₁) = no λ()
𝕋-≡-dec (∀ₗ K₀ ∙ T₀) (tvarₗ x₁)   = no λ()
𝕋-≡-dec (∀ₗ K₀ ∙ T₀) (T₁ ⊸ₗ U₁)   = no λ()
𝕋-≡-dec (∀ₗ K₀ ∙ T₀) (!ₗ T₁)      = no λ()
𝕋-≡-dec (∀ₗ K₀ ∙ T₀) (∀ₗ K₁ ∙ T₁) = Dec-map′ (uncurry (cong₂ ∀ₗ_∙_)) 𝕋-∀ₗ∙-injective ((𝕂-≡-dec K₀ K₁) ×-dec (𝕋-≡-dec T₀ T₁))

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

ℂ𝔼-≡-dec : DecidableEquality ℂ𝔼
ℂ𝔼-≡-dec (K₀        /𝕂) (K₁        /𝕂) = Dec-map′ (cong _/𝕂) ℂ𝔼-/𝕂-injective (𝕂-≡-dec K₀ K₁)
ℂ𝔼-≡-dec (_         /𝕂) (_         /𝕋) = no (λ ())
ℂ𝔼-≡-dec (_         /𝕋) (_         /𝕂) = no (λ ())
ℂ𝔼-≡-dec ((T₀ , u₀) /𝕋) ((T₁ , u₁) /𝕋) = Dec-map′ (uncurry (cong₂ (curry _/𝕋))) ℂ𝔼-/𝕋-injective ((𝕋-≡-dec T₀ T₁) ×-dec (𝕌-≡-dec u₀ u₁))

ℂ𝔼⁻-≡-dec : DecidableEquality ℂ𝔼⁻
ℂ𝔼⁻-≡-dec (K₀ /𝕂) (K₁ /𝕂) = Dec-map′ (cong _/𝕂) ℂ𝔼⁻-/𝕂-injective (𝕂-≡-dec K₀ K₁)
ℂ𝔼⁻-≡-dec (_  /𝕂) (_  /𝕋) = no (λ ())
ℂ𝔼⁻-≡-dec (_  /𝕋) (_  /𝕂) = no (λ ())
ℂ𝔼⁻-≡-dec (T₀ /𝕋) (T₁ /𝕋) = Dec-map′ (cong _/𝕋) ℂ𝔼⁻-/𝕋-injective (𝕋-≡-dec T₀ T₁)

ℂ-≡-dec : DecidableEquality ℂ
ℂ-≡-dec = ≡-dec ℂ𝔼-≡-dec

ℂ⁻-≡-dec : DecidableEquality ℂ⁻
ℂ⁻-≡-dec = ≡-dec ℂ𝔼⁻-≡-dec

useable𝕌-dec : ∀ u → Dec (useable𝕌 u)
useable𝕌-dec ∞ₗ   = yes tt
useable𝕌-dec 0/1ₗ = yes tt
useable𝕌-dec 1/1ₗ = no λ()

wkℕ-injective : ∀ (x₀ x₁ : ℕ) n x →
                wk∣ n ↑ x ∣ x₀ ≡ wk∣ n ↑ x ∣ x₁ →
                --------------------------------
                x₀ ≡ x₁
wkℕ-injective x₀ x₁ n x wk≡
  with x₀ ≥? x | x₁ ≥? x
...  | yes _   | yes _                       = +-cancelˡ-≡ _ _ _ wk≡
...  | yes x₀≥ | no  x₁≱ with refl ← wk≡     = case (x₁≱ (≤-trans x₀≥ (m≤n+m x₀ _))) of λ()
...  | no  x₀≱ | yes x₁≥ with refl ← wk≡     = case (x₀≱ (≤-trans x₁≥ (m≤n+m x₁ _))) of λ()
...  | no  _   | no  _                       = wk≡

wk𝕂-injective : ∀ (K₀ K₁ : 𝕂) n x →
                wk∣ n ↑ x ∣ K₀ ≡ wk∣ n ↑ x ∣ K₁ →
                --------------------------------
                K₀ ≡ K₁
wk𝕂-injective Tyₗ Tyₗ n m wk≡ = refl

wk𝕋-injective : ∀ (T₀ T₁ : 𝕋) n x →
                wk∣ n ↑ x ∣ T₀ ≡ wk∣ n ↑ x ∣ T₁ →
                --------------------------------
                T₀ ≡ T₁
wk𝕋-injective (tvarₗ x₀)   (tvarₗ x₁)   n x wk≡            = cong tvarₗ (wkℕ-injective _ _ n x (𝕋-tvarₗ-injective wk≡))
wk𝕋-injective (T₀ ⊸ₗ U₀)   (T₁ ⊸ₗ U₁)   n x wk≡
  with refl ← wk𝕋-injective _ _ _ _ (𝕋-⊸ₗ-injectiveˡ wk≡)
     | refl ← wk𝕋-injective _ _ _ _ (𝕋-⊸ₗ-injectiveʳ wk≡)  = refl
wk𝕋-injective (!ₗ T₀)      (!ₗ T₁)      n x wk≡
  with refl ← wk𝕋-injective _ _ _ _ (𝕋-!ₗ-injective wk≡)   = refl
wk𝕋-injective (∀ₗ K₀ ∙ T₀) (∀ₗ K₁ ∙ T₁) n x wk≡
  with refl ← wk𝕂-injective _ _ n x (𝕋-∀ₗ∙-injectiveˡ wk≡)
     | refl ← wk𝕋-injective _ _ _ _ (𝕋-∀ₗ∙-injectiveʳ wk≡) = refl

wk𝕄-injective : ∀ (M₀ M₁ : 𝕄) n x →
                wk∣ n ↑ x ∣ M₀ ≡ wk∣ n ↑ x ∣ M₁ →
                --------------------------------
                M₀ ≡ M₁
wk𝕄-injective (varₗ x₀)             (varₗ x₁)             n x wk≡    = cong varₗ (wkℕ-injective _ _ n x (𝕄-varₗ-injective wk≡))
wk𝕄-injective (λₗ T₀ ∘ M₀)          (λₗ T₁ ∘ M₁)          n x wk≡
  with refl ← wk𝕋-injective _ _ _ _ (𝕄-λₗ∘-injectiveˡ wk≡)
     | refl ← wk𝕄-injective _ _ _ _ (𝕄-λₗ∘-injectiveʳ wk≡)           = refl
wk𝕄-injective (M₀ $ₗ∘ N₀)           (M₁ $ₗ∘ N₁)           n x wk≡
  with refl ← wk𝕄-injective _ _ _ _ (𝕄-$ₗ∘-injectiveˡ wk≡)
     | refl ← wk𝕄-injective _ _ _ _ (𝕄-$ₗ∘-injectiveʳ wk≡)           = refl
wk𝕄-injective (bangₗ M₀)            (bangₗ M₁)            n x wk≡
  with refl ← wk𝕄-injective _ _ _ _ (𝕄-bangₗ-injective wk≡)          = refl
wk𝕄-injective (let-bangₗ M₀ inₗ N₀) (let-bangₗ M₁ inₗ N₁) n x wk≡
  with refl ← wk𝕄-injective _ _ _ _ (𝕄-let-bangₗ-inₗ-injectiveˡ wk≡)
     | refl ← wk𝕄-injective _ _ _ _ (𝕄-let-bangₗ-inₗ-injectiveʳ wk≡) = refl
wk𝕄-injective (Λₗ K₀ ∙ M₀)          (Λₗ K₁ ∙ M₁)          n x wk≡
  with refl ← wk𝕂-injective _ _ n x (𝕄-Λₗ∙-injectiveˡ wk≡)
     | refl ← wk𝕄-injective _ _ _ _ (𝕄-Λₗ∙-injectiveʳ wk≡)           = refl
wk𝕄-injective (M₀ $$ₗ∙ T₀)          (M₁ $$ₗ∙ T₁)          n x wk≡
  with refl ← wk𝕄-injective _ _ _ _ (𝕄-$$ₗ∙-injectiveˡ wk≡)
     | refl ← wk𝕋-injective _ _ _ _ (𝕄-$$ₗ∙-injectiveʳ wk≡)          = refl

wkℕ∣0↑x∣≡id : ∀ (y : ℕ) x →
              wk∣ 0 ↑ x ∣ y ≡ y
wkℕ∣0↑x∣≡id y x
  with y ≥? x
...  | yes _ = refl
...  | no  _ = refl

wk𝕂∣0↑x∣≡id : ∀ (K : 𝕂) x →
              wk∣ 0 ↑ x ∣ K ≡ K
wk𝕂∣0↑x∣≡id Tyₗ x = refl

wk𝕋∣0↑x∣≡id : ∀ (T : 𝕋) x →
              wk∣ 0 ↑ x ∣ T ≡ T
wk𝕋∣0↑x∣≡id (tvarₗ y) x = cong tvarₗ (wkℕ∣0↑x∣≡id y x)
wk𝕋∣0↑x∣≡id (T ⊸ₗ U) x = cong₂ _⊸ₗ_ (wk𝕋∣0↑x∣≡id T x) (wk𝕋∣0↑x∣≡id U x)
wk𝕋∣0↑x∣≡id (!ₗ T) x = cong !ₗ_ (wk𝕋∣0↑x∣≡id T x)
wk𝕋∣0↑x∣≡id (∀ₗ K ∙ T) x = cong₂ (∀ₗ_∙_) (wk𝕂∣0↑x∣≡id K x) (wk𝕋∣0↑x∣≡id T (suc x))

wk𝕄∣0↑x∣≡id : ∀ (M : 𝕄) x →
              wk∣ 0 ↑ x ∣ M ≡ M
wk𝕄∣0↑x∣≡id (varₗ y)            x = cong varₗ (wkℕ∣0↑x∣≡id y x)
wk𝕄∣0↑x∣≡id (λₗ T ∘ M)          x = cong₂ λₗ_∘_ (wk𝕋∣0↑x∣≡id T x) (wk𝕄∣0↑x∣≡id M (suc x))
wk𝕄∣0↑x∣≡id (M $ₗ∘ N)           x = cong₂ _$ₗ∘_ (wk𝕄∣0↑x∣≡id M x) (wk𝕄∣0↑x∣≡id N x)
wk𝕄∣0↑x∣≡id (bangₗ M)           x = cong bangₗ (wk𝕄∣0↑x∣≡id M x)
wk𝕄∣0↑x∣≡id (let-bangₗ M inₗ N) x = cong₂ let-bangₗ_inₗ_ (wk𝕄∣0↑x∣≡id M x) (wk𝕄∣0↑x∣≡id N (suc x))
wk𝕄∣0↑x∣≡id (Λₗ K ∙ M)          x = cong₂ Λₗ_∙_ (wk𝕂∣0↑x∣≡id K x) (wk𝕄∣0↑x∣≡id M (suc x))
wk𝕄∣0↑x∣≡id (M $$ₗ∙ T)          x = cong₂ _$$ₗ∙_ (wk𝕄∣0↑x∣≡id M x) (wk𝕋∣0↑x∣≡id T x)

private
  dec-yes-≤? : ∀ {n m} →
               (p : n ≤ m) →
               (n ≤? m) ≡ yes p
  dec-yes-≤? = dec-yes-irr (_ ≤? _) ≤-irrelevant

  dec-no-≤? : ∀ {n m} →
              (p : n ≰ m) →
              (n ≤? m) ≡ no p
  dec-no-≤? = dec-no (_ ≤? _)

≤≤⇒wkℕwkℕ-compose : ∀ (z : ℕ) {n x} m {y} →
                    x ≤ y →
                    y ≤ n + x →
                    wk∣ m ↑ y ∣ wk∣ n ↑ x ∣ z ≡ wk∣ m + n ↑ x ∣ z
≤≤⇒wkℕwkℕ-compose z {n = n} {x = x} m {y = y} x≤y y≤n+x
  with z ≥? x
...  | yes z≥x
    rewrite dec-yes-≤? (≤-trans y≤n+x (+-monoʳ-≤ n z≥x))
          | +-assoc m n z                                = refl
...  | no  z≱x
    rewrite dec-no-≤? (<⇒≱ (<-transˡ (≰⇒> z≱x) x≤y))     = refl

≤≤⇒wk𝕂wk𝕂-compose : ∀ (K : 𝕂) {n x} m {y} →
                    x ≤ y →
                    y ≤ n + x →
                    wk∣ m ↑ y ∣ wk∣ n ↑ x ∣ K ≡ wk∣ m + n ↑ x ∣ K
≤≤⇒wk𝕂wk𝕂-compose Tyₗ m x≤y y≤n+x = refl

≤≤⇒wk𝕋wk𝕋-compose : ∀ (T : 𝕋) {n x} m {y} →
                    x ≤ y →
                    y ≤ n + x →
                    wk∣ m ↑ y ∣ wk∣ n ↑ x ∣ T ≡ wk∣ m + n ↑ x ∣ T
≤≤⇒wk𝕋wk𝕋-compose (tvarₗ z)  m     x≤y y≤n+x = cong tvarₗ (≤≤⇒wkℕwkℕ-compose z m x≤y y≤n+x)
≤≤⇒wk𝕋wk𝕋-compose (T ⊸ₗ U)   m     x≤y y≤n+x = cong₂ _⊸ₗ_
                                                 (≤≤⇒wk𝕋wk𝕋-compose T m x≤y y≤n+x)
                                                 (≤≤⇒wk𝕋wk𝕋-compose U m x≤y y≤n+x)
≤≤⇒wk𝕋wk𝕋-compose (!ₗ T)     m     x≤y y≤n+x = cong !ₗ_ (≤≤⇒wk𝕋wk𝕋-compose T m x≤y y≤n+x)
≤≤⇒wk𝕋wk𝕋-compose (∀ₗ K ∙ T) m {y} x≤y y≤n+x = cong₂ ∀ₗ_∙_
                                                 (≤≤⇒wk𝕂wk𝕂-compose K m x≤y y≤n+x)
                                                 (≤≤⇒wk𝕋wk𝕋-compose T m (s≤s x≤y) (subst (suc y ≤_) (sym (+-suc _ _)) (s≤s y≤n+x)))

≤≤⇒wk𝕄wk𝕄-compose : ∀ (M : 𝕄) {n x} m {y} →
                    x ≤ y →
                    y ≤ n + x →
                    wk∣ m ↑ y ∣ wk∣ n ↑ x ∣ M ≡ wk∣ m + n ↑ x ∣ M
≤≤⇒wk𝕄wk𝕄-compose (varₗ z)            m     x≤y y≤n+x = cong varₗ (≤≤⇒wkℕwkℕ-compose z m x≤y y≤n+x)
≤≤⇒wk𝕄wk𝕄-compose (λₗ T ∘ M)          m {y} x≤y y≤n+x = cong₂ λₗ_∘_
                                                          (≤≤⇒wk𝕋wk𝕋-compose T m x≤y y≤n+x)
                                                          (≤≤⇒wk𝕄wk𝕄-compose M m (s≤s x≤y) (subst (suc y ≤_) (sym (+-suc _ _)) (s≤s y≤n+x)))
≤≤⇒wk𝕄wk𝕄-compose (M $ₗ∘ N)           m     x≤y y≤n+x = cong₂ _$ₗ∘_
                                                          (≤≤⇒wk𝕄wk𝕄-compose M m x≤y y≤n+x)
                                                          (≤≤⇒wk𝕄wk𝕄-compose N m x≤y y≤n+x)
≤≤⇒wk𝕄wk𝕄-compose (bangₗ M)           m     x≤y y≤n+x = cong bangₗ (≤≤⇒wk𝕄wk𝕄-compose M m x≤y y≤n+x)
≤≤⇒wk𝕄wk𝕄-compose (let-bangₗ M inₗ N) m {y} x≤y y≤n+x = cong₂ let-bangₗ_inₗ_
                                                          (≤≤⇒wk𝕄wk𝕄-compose M m x≤y y≤n+x)
                                                          (≤≤⇒wk𝕄wk𝕄-compose N m (s≤s x≤y) (subst (suc y ≤_) (sym (+-suc _ _)) (s≤s y≤n+x)))
≤≤⇒wk𝕄wk𝕄-compose (Λₗ K ∙ M)          m {y} x≤y y≤n+x = cong₂ Λₗ_∙_
                                                          (≤≤⇒wk𝕂wk𝕂-compose K m x≤y y≤n+x)
                                                          (≤≤⇒wk𝕄wk𝕄-compose M m (s≤s x≤y) (subst (suc y ≤_) (sym (+-suc _ _)) (s≤s y≤n+x)))
≤≤⇒wk𝕄wk𝕄-compose (M $$ₗ∙ T)          m     x≤y y≤n+x = cong₂ _$$ₗ∙_
                                                          (≤≤⇒wk𝕄wk𝕄-compose M m x≤y y≤n+x)
                                                          (≤≤⇒wk𝕋wk𝕋-compose T m x≤y y≤n+x)

≥⇒wkℕwkℕ-commute : ∀ (z : ℕ) {n x} m {y} →
                   x ≥ y →
                   wk∣ m ↑ y ∣ wk∣ n ↑ x ∣ z ≡ wk∣ n ↑ x + m ∣ wk∣ m ↑ y ∣ z
≥⇒wkℕwkℕ-commute z {n = n} {x = x} m {y = y} x≥y
  with z ≥? x
...  | yes z≥x
    with z≥y ← ≤-trans x≥y z≥x
      rewrite dec-yes-≤? z≥y
            | +-comm x m
            | dec-yes-≤? (+-monoʳ-≤ m z≥x)
            | dec-yes-≤? (≤-trans z≥y (m≤n+m _ n)) = prf
  where
    prf : m + (n + z) ≡ n + (m + z)
    prf = ℕTactic.solve (z ∷ m ∷ n ∷ [])
≥⇒wkℕwkℕ-commute z {n = n} {x = x} m {y = y} x>y
     | no  z≱x
    with z<x ← ≰⇒> z≱x
      with z ≥? y
...      | yes z≥y
        with m+z<m+x ← +-monoʳ-< m z<x
          rewrite +-comm x m
                | dec-no-≤? (<⇒≱ m+z<m+x)          = refl
...      | no  z≱y
        with z<m+x ← <-transˡ z<x (m≤n+m _ m)
          rewrite +-comm x m
                | dec-no-≤? (<⇒≱ z<m+x)            = refl

≥⇒wkℕwkℕ-commute′ : ∀ (z : ℕ) {n x} m {y} →
                    x ≥ y →
                    wk∣ m ↑ y ∣ wk∣ n ↑ x ∣ z ≡ wk∣ n ↑ m + x ∣ wk∣ m ↑ y ∣ z
≥⇒wkℕwkℕ-commute′ z {n} {x} m {y} x>y
  rewrite +-comm m x = ≥⇒wkℕwkℕ-commute z {n} {x} m {y} x>y

≥⇒wk𝕂wk𝕂-commute : ∀ (K : 𝕂) {n x} m {y} →
                   x ≥ y →
                   wk∣ m ↑ y ∣ wk∣ n ↑ x ∣ K ≡ wk∣ n ↑ x + m ∣ wk∣ m ↑ y ∣ K
≥⇒wk𝕂wk𝕂-commute Tyₗ m x>y = refl

≥⇒wk𝕂wk𝕂-commute′ : ∀ (K : 𝕂) {n x} m {y} →
                    x ≥ y →
                    wk∣ m ↑ y ∣ wk∣ n ↑ x ∣ K ≡ wk∣ n ↑ m + x ∣ wk∣ m ↑ y ∣ K
≥⇒wk𝕂wk𝕂-commute′ K {n} {x} m {y} x>y
  rewrite +-comm m x = ≥⇒wk𝕂wk𝕂-commute K {n} {x} m {y} x>y

≥⇒wk𝕋wk𝕋-commute : ∀ (T : 𝕋) {n x} m {y} →
                   x ≥ y →
                   wk∣ m ↑ y ∣ wk∣ n ↑ x ∣ T ≡ wk∣ n ↑ x + m ∣ wk∣ m ↑ y ∣ T
≥⇒wk𝕋wk𝕋-commute (tvarₗ x)          m     x>y = cong tvarₗ (≥⇒wkℕwkℕ-commute x m x>y)
≥⇒wk𝕋wk𝕋-commute (T ⊸ₗ T₁)          m     x>y = cong₂ _⊸ₗ_ (≥⇒wk𝕋wk𝕋-commute T m x>y) (≥⇒wk𝕋wk𝕋-commute T₁ m x>y)
≥⇒wk𝕋wk𝕋-commute (!ₗ T)             m     x>y = cong !ₗ_ (≥⇒wk𝕋wk𝕋-commute T m x>y)
≥⇒wk𝕋wk𝕋-commute (∀ₗ K ∙ T) {n} {x} m {y} x>y = cong₂ ∀ₗ_∙_
                                                  (≥⇒wk𝕂wk𝕂-commute K {n = n} m x>y)
                                                  (≥⇒wk𝕋wk𝕋-commute T m (s≤s x>y))

≥⇒wk𝕋wk𝕋-commute′ : ∀ (T : 𝕋) {n x} m {y} →
                    x ≥ y →
                    wk∣ m ↑ y ∣ wk∣ n ↑ x ∣ T ≡ wk∣ n ↑ m + x ∣ wk∣ m ↑ y ∣ T
≥⇒wk𝕋wk𝕋-commute′ T {n} {x} m {y} x>y
  rewrite +-comm m x = ≥⇒wk𝕋wk𝕋-commute T {n} {x} m {y} x>y

≥⇒wk𝕄wk𝕄-commute : ∀ (M : 𝕄) {n x} m {y} →
                   x ≥ y →
                   wk∣ m ↑ y ∣ wk∣ n ↑ x ∣ M ≡ wk∣ n ↑ x + m ∣ wk∣ m ↑ y ∣ M
≥⇒wk𝕄wk𝕄-commute (varₗ x) m x>y = cong varₗ (≥⇒wkℕwkℕ-commute x m x>y)
≥⇒wk𝕄wk𝕄-commute (λₗ T ∘ M) m x>y = cong₂ λₗ_∘_ (≥⇒wk𝕋wk𝕋-commute T m x>y) (≥⇒wk𝕄wk𝕄-commute M m (s≤s x>y))
≥⇒wk𝕄wk𝕄-commute (M $ₗ∘ N) m x>y = cong₂ _$ₗ∘_ (≥⇒wk𝕄wk𝕄-commute M m x>y) (≥⇒wk𝕄wk𝕄-commute N m x>y)
≥⇒wk𝕄wk𝕄-commute (bangₗ M) m x>y = cong bangₗ (≥⇒wk𝕄wk𝕄-commute M m x>y)
≥⇒wk𝕄wk𝕄-commute (let-bangₗ M inₗ N) m x>y = cong₂ let-bangₗ_inₗ_ (≥⇒wk𝕄wk𝕄-commute M m x>y) (≥⇒wk𝕄wk𝕄-commute N m (s≤s x>y))
≥⇒wk𝕄wk𝕄-commute (Λₗ K ∙ M) {n} m x>y = cong₂ Λₗ_∙_ (≥⇒wk𝕂wk𝕂-commute K {n} m x>y) (≥⇒wk𝕄wk𝕄-commute M m (s≤s x>y))
≥⇒wk𝕄wk𝕄-commute (M $$ₗ∙ T) m x>y = cong₂ _$$ₗ∙_ (≥⇒wk𝕄wk𝕄-commute M m x>y) (≥⇒wk𝕋wk𝕋-commute T m x>y)

≥⇒wk𝕊𝔼wk𝕊𝔼-commute : ∀ (s : 𝕊𝔼) {n x} m {y} →
                     x ≥ y →
                     wk∣ m ↑ y ∣ wk∣ n ↑ x ∣ s ≡ wk∣ n ↑ x + m ∣ wk∣ m ↑ y ∣ s
≥⇒wk𝕊𝔼wk𝕊𝔼-commute (T /𝕋) m x>y = cong _/𝕋 (≥⇒wk𝕋wk𝕋-commute T m x>y)
≥⇒wk𝕊𝔼wk𝕊𝔼-commute (M /𝕄) m x>y = cong _/𝕄 (≥⇒wk𝕄wk𝕄-commute M m x>y)

≥⇒wk𝕊𝔼wk𝕊𝔼-commute′ : ∀ (s : 𝕊𝔼) {n x} m {y} →
                      x ≥ y →
                      wk∣ m ↑ y ∣ wk∣ n ↑ x ∣ s ≡ wk∣ n ↑ m + x ∣ wk∣ m ↑ y ∣ s
≥⇒wk𝕊𝔼wk𝕊𝔼-commute′ s {n} {x} m {y} x>y
  rewrite +-comm m x = ≥⇒wk𝕊𝔼wk𝕊𝔼-commute s {n} {x} m {y} x>y

≤⇒wk𝕂s𝕂-exchange : ∀ (K : 𝕂) {x} m {y} →
                   x ≤ y →
                   wk∣ m ↑ y ∣ s∣ s / x ∣ K ≡ s∣ wk∣ m ↑ y ∣ s / x ∣ wk∣ m ↑ suc y ∣ K
≤⇒wk𝕂s𝕂-exchange Tyₗ m x≤y = refl

≤⇒wk𝕋s𝕋-exchange : ∀ (T : 𝕋) {x} m {y} →
                   x ≤ y →
                   wk∣ m ↑ y ∣ s∣ s / x ∣ T ≡ s∣ wk∣ m ↑ y ∣ s / x ∣ wk∣ m ↑ suc y ∣ T
≤⇒wk𝕋s𝕋-exchange {s = s} (tvarₗ z) {x} m {y} x≤y
  with z ≥? x in ≥?≡
...  | no  z≱x
    with z<y ← <-transˡ (≰⇒> z≱x) x≤y
      rewrite dec-no-≤? (<⇒≯ z<y)
            | dec-no-≤? (<⇒≱ z<y)
            | ≥?≡                       = refl
...  | yes z≥x
    with z ≟ x in ≟≡
...    | yes refl
      rewrite dec-no-≤? (≤⇒≯ x≤y)
            | ≥?≡
            | ≟≡
        with s
...        | T /𝕋 = refl
...        | _ /𝕄 = refl
≤⇒wk𝕋s𝕋-exchange         (tvarₗ z) {x} m {y} x≤y
     | yes z≥x
       | no  z≢x
      with y <? z
...      | yes y<z
        rewrite dec-yes-≤? (<⇒≤pred y<z)
              | dec-yes-≤? (m≤n⇒m≤o+n m z≥x)
              | dec-no (_ ≟ _) (>⇒≢ (m≤n⇒m≤o+n m (<-transʳ x≤y y<z)))
              | +-∸-assoc m (≤-trans (s≤s z≤n) y<z) = refl
...      | no  y≮z
        rewrite dec-no-≤? (<⇒≱ (<-transˡ (∸-monoʳ-< ≤-refl (≤-trans (s≤s z≤n) (≤∧≢⇒< z≥x (≢-sym z≢x)))) (≮⇒≥ y≮z)))
              | ≥?≡
              | ≟≡ = refl
≤⇒wk𝕋s𝕋-exchange (T ⊸ₗ U) m x≤y = cong₂ _⊸ₗ_ (≤⇒wk𝕋s𝕋-exchange T m x≤y) (≤⇒wk𝕋s𝕋-exchange U m x≤y)
≤⇒wk𝕋s𝕋-exchange (!ₗ T) m x≤y = cong !ₗ_ (≤⇒wk𝕋s𝕋-exchange T m x≤y)
≤⇒wk𝕋s𝕋-exchange {s = s} (∀ₗ K ∙ T) m {y} x≤y = cong₂ ∀ₗ_∙_ (≤⇒wk𝕂s𝕂-exchange {s = s} K m x≤y) (trans (≤⇒wk𝕋s𝕋-exchange T m (s≤s x≤y)) (cong-app (cong s𝕋∣𝕊𝔼_/ _ ∣_ (sym (≥⇒wk𝕊𝔼wk𝕊𝔼-commute′ _ _ z≤n))) (wk𝕋∣ m ↑ suc (suc y) ∣ T)))

s𝕂∣/x∣wk𝕂∣1↑x∣-inverseˡ : ∀ (s : 𝕊𝔼) (K : 𝕂) x →
                           s∣ s / x ∣ wk∣ 1 ↑ x ∣ K ≡ K
s𝕂∣/x∣wk𝕂∣1↑x∣-inverseˡ s Tyₗ x = refl

s𝕋∣/x∣wk𝕋∣1↑x∣-inverseˡ : ∀ (s : 𝕊𝔼) (U : 𝕋) x →
                           s∣ s / x ∣ wk∣ 1 ↑ x ∣ U ≡ U
s𝕋∣/x∣wk𝕋∣1↑x∣-inverseˡ s (tvarₗ y)  x
  with y ≥? x in ≥?≡
...  | no  _
    rewrite ≥?≡                            = refl
...  | yes y≥x
    rewrite dec-yes-≤? (≤-trans y≥x (n≤1+n _))
          | dec-no (_ ≟ _) (>⇒≢ (s≤s y≥x)) = refl
s𝕋∣/x∣wk𝕋∣1↑x∣-inverseˡ s (U ⊸ₗ V)   x    = cong₂ _⊸ₗ_ (s𝕋∣/x∣wk𝕋∣1↑x∣-inverseˡ s U x) (s𝕋∣/x∣wk𝕋∣1↑x∣-inverseˡ s V x)
s𝕋∣/x∣wk𝕋∣1↑x∣-inverseˡ s (!ₗ U)     x    = cong !ₗ_ (s𝕋∣/x∣wk𝕋∣1↑x∣-inverseˡ s U x)
s𝕋∣/x∣wk𝕋∣1↑x∣-inverseˡ s (∀ₗ K ∙ U) x    = cong₂ (∀ₗ_∙_) (s𝕂∣/x∣wk𝕂∣1↑x∣-inverseˡ s K x) (s𝕋∣/x∣wk𝕋∣1↑x∣-inverseˡ (wk∣ 1 ↑ 0 ∣ s) U (suc x))

s𝕄∣/x∣wk𝕄∣1↑x∣-inverseˡ : ∀ (s : 𝕊𝔼) (N : 𝕄) x →
                           s∣ s / x ∣ wk∣ 1 ↑ x ∣ N ≡ N
s𝕄∣/x∣wk𝕄∣1↑x∣-inverseˡ s (varₗ y)            x
  with y ≥? x in ≥?≡
...  | no  _
    rewrite ≥?≡                                  = refl
...  | yes y≥x
    rewrite dec-yes-≤? (≤-trans y≥x (n≤1+n _))
          | dec-no (_ ≟ _) (>⇒≢ (s≤s y≥x))       = refl
s𝕄∣/x∣wk𝕄∣1↑x∣-inverseˡ s (λₗ U ∘ N)          x = cong₂ λₗ_∘_ (s𝕋∣/x∣wk𝕋∣1↑x∣-inverseˡ s U x) (s𝕄∣/x∣wk𝕄∣1↑x∣-inverseˡ (wk∣ 1 ↑ 0 ∣ s) N (suc x))
s𝕄∣/x∣wk𝕄∣1↑x∣-inverseˡ s (N $ₗ∘ O)           x = cong₂ _$ₗ∘_ (s𝕄∣/x∣wk𝕄∣1↑x∣-inverseˡ s N x) (s𝕄∣/x∣wk𝕄∣1↑x∣-inverseˡ s O x)
s𝕄∣/x∣wk𝕄∣1↑x∣-inverseˡ s (bangₗ N)           x = cong bangₗ (s𝕄∣/x∣wk𝕄∣1↑x∣-inverseˡ s N x)
s𝕄∣/x∣wk𝕄∣1↑x∣-inverseˡ s (let-bangₗ N inₗ O) x = cong₂ let-bangₗ_inₗ_ (s𝕄∣/x∣wk𝕄∣1↑x∣-inverseˡ s N x) (s𝕄∣/x∣wk𝕄∣1↑x∣-inverseˡ (wk∣ 1 ↑ 0 ∣ s) O (suc x))
s𝕄∣/x∣wk𝕄∣1↑x∣-inverseˡ s (Λₗ K ∙ N)          x = cong₂ (Λₗ_∙_) (s𝕂∣/x∣wk𝕂∣1↑x∣-inverseˡ s K x) (s𝕄∣/x∣wk𝕄∣1↑x∣-inverseˡ (wk∣ 1 ↑ 0 ∣ s) N (suc x))
s𝕄∣/x∣wk𝕄∣1↑x∣-inverseˡ s (N $$ₗ∙ U)          x = cong₂ _$$ₗ∙_ (s𝕄∣/x∣wk𝕄∣1↑x∣-inverseˡ s N x) (s𝕋∣/x∣wk𝕋∣1↑x∣-inverseˡ s U x)
