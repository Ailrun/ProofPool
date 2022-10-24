module Calculus.PolyLinear.TypeCheck where

open import Calculus.PolyLinear.Util
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
open import Relation.Nullary.Decidable using (fromWitness) renaming (map′ to Dec-map′)
open import Relation.Nullary.Product

𝕂∈-infer : ∀ x Γ →
           -------------------------
           Dec (∃ λ K → x ⦂ K 𝕂∈ Γ)
𝕂∈-infer x       []       = no λ()
𝕂∈-infer x       (_ 𝕋∷ Γ) = Dec-map′ (×-map₂ there𝕋) (×-map₂ λ{ (there𝕋 x∈) → x∈ }) (𝕂∈-infer x Γ)
𝕂∈-infer zero    (K 𝕂∷ Γ) = yes (K , here refl)
𝕂∈-infer (suc x) (K 𝕂∷ Γ) = Dec-map′ (×-map₂ there𝕂) (×-map₂ λ{ (there𝕂 x∈) → x∈ }) (𝕂∈-infer x Γ)

𝕋∈-infer : ∀ x Γ →
           ----------------------------------
           Dec (∃₂ λ T Γ′ → x ⦂ T 𝕋∈ Γ / Γ′)
𝕋∈-infer x       []             = no λ()
𝕋∈-infer x       (K       𝕂∷ Γ) = Dec-map′ (×-map₂ (×-map (K 𝕂∷_) there𝕂)) (×-map₂ λ{ (_ 𝕂∷ Γ′ , there𝕂 x∈) → Γ′ , x∈ }) (𝕋∈-infer x Γ)
𝕋∈-infer zero    ((T , u) 𝕋∷ Γ) = Dec-map′ (λ prf → T , (T , inc𝕌 u prf) 𝕋∷ Γ , here refl) (λ{ (_ , _ , here {prf = prf} _) → recompute (useable𝕌-dec u) prf }) (useable𝕌-dec u)
𝕋∈-infer (suc x) ((T , u) 𝕋∷ Γ) = Dec-map′ (×-map₂ (×-map ((T , u) 𝕋∷_) there𝕋)) (×-map₂ λ{ (_ 𝕋∷ Γ′ , there𝕋 x∈) → Γ′ , x∈ }) (𝕋∈-infer x Γ)

context-form-check : ∀ Γ →
                     -----------
                     Dec (ℂ⊢ Γ)
kind-infer         : ∀ Γ T →
                     -------------------------
                     Dec (∃ λ K → Γ 𝕋⊢ T ⦂ K)

context-form-check []             = yes []
context-form-check (_       𝕂∷ Γ) = Dec-map′ ⋆𝕂∷_ (λ{ (⋆𝕂∷ ⊢Γ) → ⊢Γ }) (context-form-check Γ)
context-form-check ((T , u) 𝕋∷ Γ) = Dec-map′ (λ{ ((Tyₗ , ⊢T) , ⊢Γ) → ⊢T 𝕋∷ ⊢Γ }) (λ{ (⊢T 𝕋∷ ⊢Γ) → (Tyₗ , ⊢T) , ⊢Γ }) ((kind-infer Γ T) ×-dec (context-form-check Γ))

kind-infer Γ (tvarₗ x)  = Dec-map′ (×-map₂ tvarₗ) (×-map₂ λ{ (tvarₗ x∈) → x∈ }) (𝕂∈-infer x Γ)
kind-infer Γ (T ⊸ₗ U)   = Dec-map′ (λ{ ((Tyₗ , ⊢T) , (Tyₗ , ⊢U)) → Tyₗ , ⊢T ⊸ₗ ⊢U }) (λ{ (Tyₗ , ⊢T ⊸ₗ ⊢U) → (Tyₗ , ⊢T) , (Tyₗ , ⊢U) }) ((kind-infer Γ T) ×-dec (kind-infer Γ U))
kind-infer Γ (!ₗ T)     = Dec-map′ (λ{ (Tyₗ , ⊢T) -> Tyₗ , !ₗ ⊢T }) (×-map₂ λ{ (!ₗ ⊢T) → ⊢T }) (kind-infer Γ T)
kind-infer Γ (∀ₗ K ∙ T) = Dec-map′ (λ{ (Tyₗ , ⊢T) -> Tyₗ , ∀ₗ⋆∙ ⊢T }) (×-map₂ λ{ (∀ₗ⋆∙ ⊢T) → ⊢T }) (kind-infer (K 𝕂∷ Γ) T)

type-infer : ∀ Γ M →
             ----------------------------------
             Dec (∃₂ λ T Γ′ → Γ 𝕄⊢ M ⦂ T / Γ′)
type-infer Γ (varₗ x)            = Dec-map′
                                     (×-map₂ (×-map₂ varₗ))
                                     (×-map₂ (×-map₂ (λ{ (varₗ x∈) → x∈ })))
                                     (𝕋∈-infer x Γ)
type-infer Γ (λₗ T ∘ M)
  with type-infer ((T , 0/1ₗ) 𝕋∷ Γ) M
...  | no ¬⊢M                    = no λ{ (_ ⊸ₗ U , Γ′ , λₗ x ∘ ⊢M) → ¬⊢M (U , (T , 1/1ₗ) 𝕋∷ Γ′ , ⊢M) }
...  | yes (U , Γ′ , ⊢M)
    with ≤u 𝕋∷ _ ← 𝕄⊢⇒≤𝕌ℂ ⊢M
       | (T′ , u) 𝕋∷ Γ″ ← Γ′
       | eq ← 𝕄⊢-preserves-extractℂ⁻ ⊢M
      with refl ← ℂ⁻-𝕋∷-injectiveˡ eq
        with ≤u
...        | refl                = no λ{ (_ , _ , λₗ _ ∘ ⊢M′) → case (ℂ-𝕋∷-injectiveˡ₂ (𝕄⊢-det₂ ⊢M ⊢M′)) λ() }
...        | 0/1ₗ≤1/1ₗ           = Dec-map′
                                     (λ{ (Tyₗ , ⊢T) → _ , _ , λₗ ⊢T ∘ ⊢M })
                                     (λ{ (_ , _ , λₗ ⊢T ∘ _) → _ , ⊢T })
                                     (kind-infer Γ T)
type-infer Γ (M $ₗ∘ N)
  with type-infer Γ M
...  | no ¬⊢M                    = no λ{ (_ , _ , ⊢M $ₗ∘ _) → ¬⊢M (_ , _ , ⊢M) }
...  | yes (U⊸T , Γ′ , ⊢M)
    with U⊸T
...    | tvarₗ _                 = no λ{ (_ , _ , ⊢M′ $ₗ∘ _) → case (𝕄⊢-det₁ ⊢M ⊢M′) λ() }
...    | !ₗ _                    = no λ{ (_ , _ , ⊢M′ $ₗ∘ _) → case (𝕄⊢-det₁ ⊢M ⊢M′) λ() }
...    | ∀ₗ _ ∙ _                = no λ{ (_ , _ , ⊢M′ $ₗ∘ _) → case (𝕄⊢-det₁ ⊢M ⊢M′) λ() }
...    | U ⊸ₗ _
      with type-infer Γ′ N
...      | no ¬⊢N                = no λ{ (_ , _ , ⊢M′ $ₗ∘ ⊢N) → ¬⊢N (_ , _ , subst (_𝕄⊢ _ ⦂ _ / _) (𝕄⊢-det₂ ⊢M′ ⊢M) ⊢N) }
...      | yes (U′ , Γ″ , ⊢N)    = Dec-map′
                                     (λ{ refl → _ , _ , ⊢M $ₗ∘ ⊢N })
                                     (λ{ (_ , _ , ⊢M′ $ₗ∘ ⊢N′) →
                                       trans
                                         (𝕋-⊸ₗ-injectiveˡ (𝕄⊢-det₁ ⊢M ⊢M′))
                                         (𝕄⊢-det₁ ⊢N′ (subst (_𝕄⊢ _ ⦂ _ / _) (𝕄⊢-det₂ ⊢M ⊢M′) ⊢N))
                                       })
                                     (𝕋-≡-dec U U′)
type-infer Γ (bangₗ M)
  with type-infer Γ M
...  | no ¬⊢M                    = no λ{ (_ , _ , bangₗ ⊢M) → ¬⊢M (_ , _ , ⊢M) }
...  | yes (U , Γ′ , ⊢M)         = Dec-map′
                                     (λ{ refl → _ , _ , bangₗ ⊢M })
                                     (λ{ (_ , _ , bangₗ ⊢M′) → 𝕄⊢-det₂ ⊢M′ ⊢M })
                                     (ℂ-≡-dec Γ Γ′)
type-infer Γ (let-bangₗ M inₗ N)
  with type-infer Γ M
...  | no ¬⊢M                    = no λ{ (_ , _ , let-bangₗ ⊢M inₗ _) → ¬⊢M (_ , _ , ⊢M) }
...  | yes (!U , Γ′ , ⊢M)
    with !U
...    | tvarₗ _                 = no λ{ (_ , _ , let-bangₗ ⊢M′ inₗ _) → case (𝕄⊢-det₁ ⊢M ⊢M′) λ() }
...    | ∀ₗ _ ∙ _                = no λ{ (_ , _ , let-bangₗ ⊢M′ inₗ _) → case (𝕄⊢-det₁ ⊢M ⊢M′) λ() }
...    | _ ⊸ₗ _                  = no λ{ (_ , _ , let-bangₗ ⊢M′ inₗ _) → case (𝕄⊢-det₁ ⊢M ⊢M′) λ() }
...    | !ₗ U                    = Dec-map′ ⊢N⇒⊢let-bang-M-in-N ⊢let-bang-M-in-N⇒⊢N (type-infer ((U , ∞ₗ) 𝕋∷ Γ′) N)
  where
    ⊢N⇒⊢let-bang-M-in-N : (∃₂ λ T Γ″ → (U , ∞ₗ) 𝕋∷ Γ′ 𝕄⊢ N ⦂ T / Γ″) → (∃₂ λ T Γ″ → Γ 𝕄⊢ let-bangₗ M inₗ N ⦂ T / Γ″)
    ⊢N⇒⊢let-bang-M-in-N (_ , _ , ⊢N)
      with refl 𝕋∷ _ ← 𝕄⊢⇒≤𝕌ℂ ⊢N = _ , _ , let-bangₗ ⊢M inₗ ⊢N

    ⊢let-bang-M-in-N⇒⊢N : (∃₂ λ T Γ″ → Γ 𝕄⊢ let-bangₗ M inₗ N ⦂ T / Γ″) → (∃₂ λ T Γ″ → (U , ∞ₗ) 𝕋∷ Γ′ 𝕄⊢ N ⦂ T / Γ″)
    ⊢let-bang-M-in-N⇒⊢N (_ , _ , let-bangₗ ⊢M′ inₗ ⊢N)
      with refl , refl ← 𝕄⊢-det ⊢M′ ⊢M = _ , _ , ⊢N
type-infer Γ (Λₗ K ∙ M)          = Dec-map′ ⊢M⇒⊢ΛK∙M (λ{ (_ , _ , Λₗ⋆∙ ⊢M) → _ , _ , ⊢M }) (type-infer (K 𝕂∷ Γ) M)
  where
    ⊢M⇒⊢ΛK∙M : (∃₂ λ T Γ′ → K 𝕂∷ Γ 𝕄⊢ M ⦂ T / Γ′) → (∃₂ λ T Γ′ → Γ 𝕄⊢ Λₗ K ∙ M ⦂ T / Γ′)
    ⊢M⇒⊢ΛK∙M (_ , _ , ⊢M)
      with ⋆𝕂∷ _ ← 𝕄⊢⇒≤𝕌ℂ ⊢M = _ , _ , Λₗ⋆∙ ⊢M
type-infer Γ (M $$ₗ∙ T)
  with type-infer Γ M
...  | no ¬⊢M                    = no λ{ (_ , _ , ⊢M $$ₗ∙ _) → ¬⊢M (_ , _ , ⊢M) }
...  | yes (∀K∙T , Γ′ , ⊢M)
    with ∀K∙T
...    | tvarₗ _                 = no λ{ (_ , _ , ⊢M′ $$ₗ∙ _) → case (𝕄⊢-det₁ ⊢M ⊢M′) λ() }
...    | !ₗ _                    = no λ{ (_ , _ , ⊢M′ $$ₗ∙ _) → case (𝕄⊢-det₁ ⊢M ⊢M′) λ() }
...    | _ ⊸ₗ _                  = no λ{ (_ , _ , ⊢M′ $$ₗ∙ _) → case (𝕄⊢-det₁ ⊢M ⊢M′) λ() }
...    | ∀ₗ K ∙ _
      with kind-infer Γ′ T
...      | no ¬⊢T                = no λ{ (_ , _ , ⊢M′ $$ₗ∙ ⊢T) → ¬⊢T (_ , subst (_𝕋⊢ _ ⦂ _) (𝕄⊢-det₂ ⊢M′ ⊢M) ⊢T) }
...      | yes (K′ , ⊢T)         = Dec-map′
                                     (λ{ refl → _ , _ , ⊢M $$ₗ∙ ⊢T })
                                     (λ{ (_ , _ , ⊢M′ $$ₗ∙ ⊢T′) →
                                       trans
                                         (𝕋-∀ₗ∙-injectiveˡ (𝕄⊢-det₁ ⊢M ⊢M′))
                                         (𝕋⊢-det ⊢T′ (subst (_𝕋⊢ _ ⦂ _) (𝕄⊢-det₂ ⊢M ⊢M′) ⊢T))
                                       })
                                     (𝕂-≡-dec K K′)
