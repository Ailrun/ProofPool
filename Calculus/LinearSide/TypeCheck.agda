module Calculus.LinearSide.TypeCheck where

open import Data.Fin using (Fin; suc)
import Data.Fin.Properties as Fin
open import Data.Product using (∃; _,_; -,_; uncurry)
open import Data.Sum using ([_,_]; inj₁; inj₂)
open import Data.Vec using (_∷_)
import Data.Vec as Vec
open import Function using (case_of_)
open import Relation.Nullary using (Dec; yes; no)
import Relation.Nullary.Decidable as Dec
open import Relation.Binary.PropositionalEquality using (refl)
import Relation.Binary.PropositionalEquality as ≡

open import Calculus.LinearSide.Syntax
open import Calculus.LinearSide.Syntax.Properties
open import Calculus.LinearSide.Rules
open import Calculus.LinearSide.Rules.Properties

infix  4 _⊢ₗ_⦂?
infix  4 _unused-in?_
infix  4 _linear-in?_

_unused-in?_ : ∀ {n} (x : Fin n) (M : 𝕄 n) → Dec (x unused-in M)
x unused-in? varₗ y            = Dec.map′ varₗ (λ{ (varₗ neq) → neq }) (Dec.¬? (x Fin.≟ y))
x unused-in? λₗ T ∘ₗ M         = Dec.map′ λₗ*∘ₗ_ (λ{ (λₗ*∘ₗ M∅) → M∅ }) (suc x unused-in? M)
x unused-in? M $∘ₗ N           = Dec.map′ (uncurry _$∘ₗ_) (λ{ (M∅ $∘ₗ N∅) → M∅ , N∅ }) ((x unused-in? M) Dec.×-dec (x unused-in? N))
x unused-in? bangₗ M           = Dec.map′ bangₗ (λ{ (bangₗ M∅) → M∅ }) (x unused-in? M)
x unused-in? let-bangₗ M inₗ N = Dec.map′ (uncurry let-bangₗ_inₗ_) (λ{ (let-bangₗ M∅ inₗ N∅) → M∅ , N∅ }) (((x unused-in? M) Dec.×-dec (suc x unused-in? N)))

_linear-in?_ : ∀ {n} (x : Fin n) (M : 𝕄 n) → Dec (x linear-in M)
x linear-in? varₗ y            = Dec.map′ varₗ (λ{ (varₗ eq) → eq }) (x Fin.≟ y)
x linear-in? λₗ T ∘ₗ M         = Dec.map′ λₗ*∘ₗ_ (λ{ (λₗ*∘ₗ Mₗ) → Mₗ }) (suc x linear-in? M)
x linear-in? M $∘ₗ N           = Dec.map′
                                   [ uncurry _$∘ₗ∅_ , uncurry ∅_$∘ₗ_ ]
                                   (λ{ (Mₗ $∘ₗ∅ N∅) → inj₁ (Mₗ , N∅) ; (∅ M∅ $∘ₗ Nₗ) → inj₂ (M∅ , Nₗ) })
                                   (((x linear-in? M) Dec.×-dec (x unused-in? N)) Dec.⊎-dec (x unused-in? M) Dec.×-dec (x linear-in? N))
x linear-in? bangₗ M           = no λ ()
x linear-in? let-bangₗ M inₗ N = Dec.map′
                                   [ uncurry let-bangₗ_inₗ∅_ , uncurry let-bangₗ∅_inₗ_ ]
                                   (λ{ (let-bangₗ Mₗ inₗ∅ N∅) → inj₁ (Mₗ , N∅) ; (let-bangₗ∅ M∅ inₗ Nₗ) → inj₂ (M∅ , Nₗ) })
                                   (((x linear-in? M) Dec.×-dec (suc x unused-in? N)) Dec.⊎-dec (x unused-in? M) Dec.×-dec (suc x linear-in? N))

_⊢ₗ_⦂? : ∀ {n} (Γ : ℂ n) (M : 𝕄 n) → Dec (∃ λ T → Γ ⊢ₗ M ⦂ T)
Γ ⊢ₗ varₗ x            ⦂? = yes (Vec.lookup Γ x , varₗ refl)
Γ ⊢ₗ λₗ T ∘ₗ M         ⦂?
  with T ∷ Γ ⊢ₗ M ⦂?
...  | no ¬U,⊢M           = no λ{ (_ , λₗ*∘ₗ ⊢M ∣ₗ _) → ¬U,⊢M (-, ⊢M) }
...  | yes (U , ⊢M)
    with 0 linear-in? M
...    | no ¬Mₗ           = no λ{ (_ , λₗ*∘ₗ _ ∣ₗ Mₗ) → ¬Mₗ Mₗ }
...    | yes Mₗ           = yes (T ⊸ₗ U , λₗ*∘ₗ ⊢M ∣ₗ Mₗ)
Γ ⊢ₗ M $∘ₗ N           ⦂?
  with Γ ⊢ₗ M ⦂?
...  | no ¬T⊸ₗU,⊢M        = no λ{ (_ , ⊢M $∘ₗ _) → ¬T⊸ₗU,⊢M (-, ⊢M) }
...  | yes (T⊸ₗU , ⊢M)
    with T⊸ₗU
...    | baseₗ            = no λ{ (_ , ⊢M′ $∘ₗ _) → case ⊢ₗ-deterministic ⊢M ⊢M′ of λ () }
...    | !ₗ T             = no λ{ (_ , ⊢M′ $∘ₗ _) → case ⊢ₗ-deterministic ⊢M ⊢M′ of λ () }
...    | T ⊸ₗ U
      with Γ ⊢ₗ N ⦂?
...      | no ¬T′,⊢N      = no λ{ (_ , _ $∘ₗ ⊢N) → ¬T′,⊢N (-, ⊢N) }
...      | yes (T′ , ⊢N)
        with T 𝕋≟ T′
...        | no  T≢T′     = no λ{ (_ , ⊢M′ $∘ₗ ⊢N′) → T≢T′ (≡.trans (⊸ₗ-injectiveˡ (⊢ₗ-deterministic ⊢M ⊢M′)) (⊢ₗ-deterministic ⊢N′ ⊢N)) }
...        | yes refl     = yes (U , (⊢M $∘ₗ ⊢N))
Γ ⊢ₗ bangₗ M           ⦂? = Dec.map′ (λ{ (_ , ⊢M) → -, bangₗ ⊢M }) (λ{ (_ , bangₗ ⊢M) → -, ⊢M }) (Γ ⊢ₗ M ⦂?)
Γ ⊢ₗ let-bangₗ M inₗ N ⦂?
  with Γ ⊢ₗ M ⦂?
...  | no ¬!ₗT,⊢M         = no λ{ (_ , let-bangₗ ⊢M inₗ _) → ¬!ₗT,⊢M (-, ⊢M) }
...  | yes (!ₗT , ⊢M)
    with !ₗT
...    | baseₗ            = no λ{ (_ , let-bangₗ ⊢M′ inₗ _) → case ⊢ₗ-deterministic ⊢M ⊢M′ of λ () }
...    | T ⊸ₗ U           = no λ{ (_ , let-bangₗ ⊢M′ inₗ _) → case ⊢ₗ-deterministic ⊢M ⊢M′ of λ () }
...    | !ₗ T
      with T ∷ Γ ⊢ₗ N ⦂?
...      | no ¬U,⊢N       = no λ{ (_ , let-bangₗ ⊢M′ inₗ ⊢N) → ¬U,⊢N (-, ≡.subst (λ T′ → T′ ∷ Γ ⊢ₗ N ⦂ _) (!ₗ-injective (⊢ₗ-deterministic ⊢M′ ⊢M)) ⊢N) }
...      | yes (U , ⊢N)   = yes (U , let-bangₗ ⊢M inₗ ⊢N)
