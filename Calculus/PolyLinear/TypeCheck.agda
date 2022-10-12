module Calculus.PolyLinear.TypeCheck where

open import Calculus.PolyLinear.Syntax
open import Calculus.PolyLinear.Syntax.Properties
open import Calculus.PolyLinear.Rules
open import Calculus.PolyLinear.Rules.Properties
open import Data.Nat
open import Data.Product renaming (map to ×-map; map₂ to ×-map₂)
open import Data.Sum
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable using () renaming (map′ to Dec-map′)
open import Relation.Nullary.Product

𝕂∈-infer : ∀ x Γ → Dec (∃ λ K → x ⦂ K 𝕂∈ Γ)
𝕂∈-infer x       []       = no λ()
𝕂∈-infer x       (_ 𝕋∷ Γ) = Dec-map′ (×-map₂ there𝕋) (×-map₂ λ{ (there𝕋 x∈) → x∈ }) (𝕂∈-infer x Γ)
𝕂∈-infer zero    (K 𝕂∷ Γ) = yes (K , here refl)
𝕂∈-infer (suc x) (K 𝕂∷ Γ) = Dec-map′ (×-map₂ there𝕂) (×-map₂ λ{ (there𝕂 x∈) → x∈ }) (𝕂∈-infer x Γ)

𝕋∈-infer : ∀ x Γ → Dec (∃₂ λ T Γ′ → x ⦂ T 𝕋∈ Γ / Γ′)
𝕋∈-infer x       []             = no λ()
𝕋∈-infer x       (K       𝕂∷ Γ) = Dec-map′ (×-map₂ (×-map (K 𝕂∷_) there𝕂)) (×-map₂ λ{ (_ 𝕂∷ Γ′ , there𝕂 x∈) → (Γ′ , x∈) }) (𝕋∈-infer x Γ)
𝕋∈-infer zero    ((T , u) 𝕋∷ Γ) = Dec-map′ (λ prf → T , (T , inc𝕌 u prf) 𝕋∷ Γ , here refl) (λ{ (_ , _ , here {prf = prf} _) → recompute (useable𝕌-dec u) prf }) (useable𝕌-dec u)
𝕋∈-infer (suc x) ((T , u) 𝕋∷ Γ) = Dec-map′ (×-map₂ (×-map ((T , u) 𝕋∷_) there𝕋)) (×-map₂ λ{ (_ 𝕋∷ Γ′ , there𝕋 x∈) → (Γ′ , x∈)}) (𝕋∈-infer x Γ)

context-form-check : ∀ Γ → Dec (ℂ⊢ Γ)
kind-infer : ∀ Γ T → Dec (∃ λ K → Γ 𝕋⊢ T ⦂ K)

context-form-check []             = yes []
context-form-check (_       𝕂∷ Γ) = Dec-map′ ⋆𝕂∷_ (λ{ (⋆𝕂∷ ⊢Γ) → ⊢Γ }) (context-form-check Γ)
context-form-check ((T , u) 𝕋∷ Γ) = Dec-map′ (λ{ ((Tyₗ , ⊢T) , ⊢Γ) → ⊢T 𝕋∷ ⊢Γ}) (λ{ (⊢T 𝕋∷ ⊢Γ) → (Tyₗ , ⊢T) , ⊢Γ }) ((kind-infer Γ T) ×-dec (context-form-check Γ))

kind-infer Γ (tvarₗ x)  = Dec-map′ (×-map₂ tvarₗ) (×-map₂ λ{ (tvarₗ x∈) → x∈ }) (𝕂∈-infer x Γ)
kind-infer Γ (T ⊸ₗ U)   = Dec-map′ (λ{ ((Tyₗ , ⊢T) , (Tyₗ , ⊢U)) → Tyₗ , ⊢T ⊸ₗ ⊢U }) (λ{ (Tyₗ , ⊢T ⊸ₗ ⊢U) → (Tyₗ , ⊢T) , (Tyₗ , ⊢U) }) ((kind-infer Γ T) ×-dec (kind-infer Γ U))
kind-infer Γ (!ₗ T)     = Dec-map′ (λ{ (Tyₗ , ⊢T) -> Tyₗ , !ₗ ⊢T }) (×-map₂ λ{ (!ₗ ⊢T) → ⊢T }) (kind-infer Γ T)
kind-infer Γ (∀ₗ K ∙ T) = Dec-map′ (λ{ (Tyₗ , ⊢T) -> Tyₗ , ∀ₗ⋆∙ ⊢T }) (×-map₂ λ{ (∀ₗ⋆∙ ⊢T) → ⊢T }) (kind-infer (K 𝕂∷ Γ) T)

type-infer : ∀ Γ M → Dec (∃₂ λ T Γ′ → Γ 𝕄⊢ M ⦂ T / Γ′)

type-infer Γ (varₗ x)            = Dec-map′ (×-map₂ (×-map₂ varₗ)) (×-map₂ (×-map₂ (λ{ (varₗ x∈) → x∈ }))) (𝕋∈-infer x Γ)
type-infer Γ (λₗ T ∘ M)
  with type-infer ((T , 0/1ₗ) 𝕋∷ Γ) M
...  | no ¬⊢M                    = no λ{ (_ ⊸ₗ U , Γ′ , λₗ x ∘ ⊢M) → ¬⊢M (U , (T , 1/1ₗ) 𝕋∷ Γ′ , ⊢M) }
...  | yes (U , Γ′ , ⊢M)
    with Γ′             | 𝕄⊢-preserves-extractℂ⁻ ⊢M
...    | (T′ , u) 𝕋∷ Γ′ | eq     = {!!}
type-infer Γ (M $ₗ∘ N)
  with type-infer Γ M
...  | no ¬⊢M = {!!}
...  | yes (U , Γ′ , ⊢M)
    with U
...    | tvarₗ x  = no λ{ (_ , fst , ⊢M $ₗ∘ _) → {!!} }
...    | !ₗ U     = {!!}
...    | ∀ₗ K ∙ U = {!!}
...    | U ⊸ₗ V   = {!!}
type-infer Γ (bangₗ M)           = {!!}
type-infer Γ (let-bangₗ M inₗ N) = {!!}
type-infer Γ (Λₗ K ∙ M)          = {!!}
type-infer Γ (M $$ₗ∙ T)          = {!!}
