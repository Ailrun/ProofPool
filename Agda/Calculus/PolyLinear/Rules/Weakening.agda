{-# OPTIONS --allow-unsolved-metas #-}
module Calculus.PolyLinear.Rules.Weakening where

open import Calculus.PolyLinear.Syntax
open import Calculus.PolyLinear.Syntax.Properties
open import Calculus.PolyLinear.Rules
open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable

𝕂∈⇒len+𝕂∈++ : x ⦂ K 𝕂∈ Γ′ → len Δ + x ⦂ wk∣ len Δ ↑ 0 ∣ K 𝕂∈ Δ ++ Γ′
𝕂∈⇒len+𝕂∈++ {K = K} {Δ = []}    x∈
  rewrite wk𝕂∣0↑x∣≡id K 0          = x∈
𝕂∈⇒len+𝕂∈++ {K = K} {Δ = _ ∷ _} x∈ = there (𝕂∈⇒len+𝕂∈++ x∈)

𝕋∈⇒len+𝕋∈++ : x ⦂ T 𝕋∈ Γ′ / Γ″ → len Δ + x ⦂ wk∣ len Δ ↑ 0 ∣ T 𝕋∈ Δ ++ Γ′ / Δ ++ Γ″
𝕋∈⇒len+𝕋∈++ {T = T} {Δ = []}     x∈
  rewrite wk𝕋∣0↑x∣≡id T 0                                          = x∈
𝕋∈⇒len+𝕋∈++ {T = T} {Δ = _ ∷ Δ′} x∈
  rewrite sym (≤≤⇒wk𝕋wk𝕋-compose T 1 ≤-refl (z≤n {len Δ′ + 0})) = there (𝕋∈⇒len+𝕋∈++ x∈)

≥len⇒𝕂∈++⇒len+𝕂∈++-++ : ∀ Γ → x ≥ len Γ → x ⦂ K 𝕂∈ Γ ++ Γ′ → len Δ + x ⦂ wk∣ len Δ ↑ 0 ∣ K 𝕂∈ wk∣ len Δ ↑ len Γ ∣ Γ ++ Δ ++ Γ′
≥len⇒𝕂∈++⇒len+𝕂∈++-++                     []      z≤n      x∈         = 𝕂∈⇒len+𝕂∈++ x∈
≥len⇒𝕂∈++⇒len+𝕂∈++-++ {x = suc x} {Δ = Δ} (_ ∷ Γ) (s≤s x≥) (there x∈)
  rewrite +-suc (len Δ) x                                             = there (≥len⇒𝕂∈++⇒len+𝕂∈++-++ Γ x≥ x∈)

≥len⇒𝕋∈++⇒≡++ : ∀ Γ → x ≥ len Γ → x ⦂ T 𝕋∈ Γ ++ Γ′ / Γ″ → ∃ λ Γ‴ → Γ″ ≡ Γ ++ Γ‴
≥len⇒𝕋∈++⇒≡++ []      z≤n      x∈         = _ , refl
≥len⇒𝕋∈++⇒≡++ (x ∷ Γ) (s≤s x≥) (there x∈)
  with _ , refl ← ≥len⇒𝕋∈++⇒≡++ Γ x≥ x∈   = _ , refl

≥len⇒𝕋∈++⇒len+𝕋∈++-++ : ∀ Γ → x ≥ len Γ → x ⦂ T 𝕋∈ Γ ++ Γ′ / Γ ++ Γ″ → len Δ + x ⦂ wk∣ len Δ ↑ 0 ∣ T 𝕋∈ wk∣ len Δ ↑ len Γ ∣ Γ ++ Δ ++ Γ′ / wk∣ len Δ ↑ len Γ ∣ Γ ++ Δ ++ Γ″
≥len⇒𝕋∈++⇒len+𝕋∈++-++                     []      z≤n      x∈                 = 𝕋∈⇒len+𝕋∈++ x∈
≥len⇒𝕋∈++⇒len+𝕋∈++-++ {x = suc x} {Δ = Δ} (_ ∷ Γ) (s≤s x≥) (there {T = T} x∈)
  rewrite +-suc (len Δ) x
        | ≤≤⇒wk𝕋wk𝕋-compose T (len Δ) ≤-refl (z≤n {1 + 0})
        | +-comm (len Δ) 1
        | sym (≤≤⇒wk𝕋wk𝕋-compose T 1 ≤-refl (z≤n {len Δ + 0}))                = there (≥len⇒𝕋∈++⇒len+𝕋∈++-++ Γ x≥ x∈)

<len⇒𝕂∈++⇒len+𝕂∈++-++ : ∀ Γ → x < len Γ → x ⦂ K 𝕂∈ Γ ++ Γ′ → x ⦂ wk∣ len Δ ↑ len Γ ∣ K 𝕂∈ wk∣ len Δ ↑ len Γ ∣ Γ ++ Δ ++ Γ′
<len⇒𝕂∈++⇒len+𝕂∈++-++ (_ ∷ Γ) x<       (here refl) = here refl
<len⇒𝕂∈++⇒len+𝕂∈++-++ (_ ∷ Γ) (s≤s x<) (there x∈)  = there (<len⇒𝕂∈++⇒len+𝕂∈++-++ Γ x< x∈)

-- <len⇒𝕂∈++⇒len+𝕂∈++-++ : ∀ Γ → x < len Γ → x ⦂ K 𝕂∈ Γ ++ Γ′ → x ⦂ wk∣ len Δ ↑ len Γ ∣ K 𝕂∈ wk∣ len Δ ↑ len Γ ∣ Γ ++ Δ ++ Γ′
-- <len⇒𝕂∈++⇒len+𝕂∈++-++ (_ ∷ Γ) x<       (here refl) = here refl
-- <len⇒𝕂∈++⇒len+𝕂∈++-++ (_ ∷ Γ) (s≤s x<) (there x∈)  = there (<len⇒𝕂∈++⇒len+𝕂∈++-++ Γ x< x∈)

wk∣↑∣𝕂∈ : ∀ Γ →
          x ⦂ K 𝕂∈ Γ ++ Γ′ →
          --------------------------------------------
          wk∣ len Δ ↑ len Γ ∣ x ⦂ wk∣ len Δ ↑ len Γ ∣ K 𝕂∈ wk∣ len Δ ↑ len Γ ∣ Γ ++ Δ ++ Γ′
wk∣↑∣𝕂∈ {x} []               x∈
  rewrite proj₂ (dec-yes (x ≥? 0) z≤n) = 𝕂∈⇒len+𝕂∈++ x∈
wk∣↑∣𝕂∈ {x} (K       /𝕂 ∷ Γ) x∈
  with x ≥? suc (len Γ)
...  | yes x≥                          = ≥len⇒𝕂∈++⇒len+𝕂∈++-++ (_ ∷ Γ) x≥ x∈
...  | no  x≱                          = <len⇒𝕂∈++⇒len+𝕂∈++-++ (_ ∷ Γ) (≰⇒> x≱) x∈
wk∣↑∣𝕂∈ {x} ((T , u) /𝕋 ∷ Γ) x∈
  with x ≥? suc (len Γ)
...  | yes x≥                          = ≥len⇒𝕂∈++⇒len+𝕂∈++-++ (_ ∷ Γ) x≥ x∈
...  | no  x≱                          = <len⇒𝕂∈++⇒len+𝕂∈++-++ (_ ∷ Γ) (≰⇒> x≱) x∈

wk∣↑∣𝕋∈ : ∀ Γ →
          x ⦂ T 𝕋∈ Γ ++ Γ′ / Γ₀ →
          --------------------------------------------
          let Γ″ , Γ‴ = splitAt (len Γ) Γ₀ in
          wk∣ len Δ ↑ len Γ ∣ x ⦂ wk∣ len Δ ↑ len Γ ∣ T 𝕋∈ wk∣ len Δ ↑ len Γ ∣ Γ ++ Δ ++ Γ′ / wk∣ len Δ ↑ len Γ ∣ Γ″ ++ Δ ++ Γ‴
wk∣↑∣𝕋∈ {x} []               x∈
  rewrite proj₂ (dec-yes (x ≥? 0) z≤n) = 𝕋∈⇒len+𝕋∈++ x∈
wk∣↑∣𝕋∈ {x} (K       /𝕂 ∷ Γ) x∈
  with x ≥? suc (len Γ)
...  | yes x≥
    with _ , refl ← ≥len⇒𝕋∈++⇒≡++ (K /𝕂 ∷ Γ) x≥ x∈ = {!!} -- ≥len⇒𝕂∈++⇒len+𝕂∈++-++ (_ ∷ Γ) x≥ x∈
...  | no  x≱                          = {!!} -- <len⇒𝕂∈++⇒len+𝕂∈++-++ (_ ∷ Γ) (≰⇒> x≱) x∈
wk∣↑∣𝕋∈ {x} ((T , u) /𝕋 ∷ Γ) x∈
  with x ≥? suc (len Γ)
...  | yes x≥                          = {!!} -- ≥len⇒𝕂∈++⇒len+𝕂∈++-++ (_ ∷ Γ) x≥ x∈
...  | no  x≱                          = {!!} -- <len⇒𝕂∈++⇒len+𝕂∈++-++ (_ ∷ Γ) (≰⇒> x≱) x∈

𝕋⊢wk∣↑∣ : ∀ Γ →
          ℂ⊢ Δ ++ Γ′ →
          Γ ++ Γ′ 𝕋⊢ T ⦂ K →
          --------------------------------------------
          wk∣ len Δ ↑ len Γ ∣ Γ ++ Δ ++ Γ′ 𝕋⊢ wk∣ len Δ ↑ len Γ ∣ T ⦂ wk∣ len Δ ↑ len Γ ∣ K
ℂ⊢wk∣↑∣ : ∀ Γ →
          ℂ⊢ Δ ++ Γ′ →
          ℂ⊢ Γ ++ Γ′ →
          ---------------
          ℂ⊢ wk∣ len Δ ↑ len Γ ∣ Γ ++ Δ ++ Γ′

𝕋⊢wk∣↑∣ Γ ⊢ΔΓ′ (tvarₗ ⊢ΓΓ′ x∈) = tvarₗ (ℂ⊢wk∣↑∣ Γ ⊢ΔΓ′ ⊢ΓΓ′) (wk∣↑∣𝕂∈ Γ x∈)
𝕋⊢wk∣↑∣ Γ ⊢ΔΓ′ (⊢T ⊸ₗ ⊢U)      = 𝕋⊢wk∣↑∣ Γ ⊢ΔΓ′ ⊢T ⊸ₗ 𝕋⊢wk∣↑∣ Γ ⊢ΔΓ′ ⊢U
𝕋⊢wk∣↑∣ Γ ⊢ΔΓ′ (!ₗ ⊢T)         = !ₗ (𝕋⊢wk∣↑∣ Γ ⊢ΔΓ′ ⊢T)
𝕋⊢wk∣↑∣ Γ ⊢ΔΓ′ (∀ₗ⋆∙ ⊢T)       = ∀ₗ⋆∙ (𝕋⊢wk∣↑∣ (_ ∷ Γ) ⊢ΔΓ′ ⊢T)

ℂ⊢wk∣↑∣ []               ⊢ΔΓ′ ⊢ΓΓ′           = ⊢ΔΓ′
ℂ⊢wk∣↑∣ (K       /𝕂 ∷ Γ) ⊢ΔΓ′ (⋆/𝕂   ∷ ⊢ΓΓ′) = ⋆/𝕂 ∷ ℂ⊢wk∣↑∣ Γ ⊢ΔΓ′ ⊢ΓΓ′
ℂ⊢wk∣↑∣ ((T , u) /𝕋 ∷ Γ) ⊢ΔΓ′ (⊢T /𝕋 ∷ ⊢ΓΓ′) = 𝕋⊢wk∣↑∣ Γ ⊢ΔΓ′ ⊢T /𝕋 ∷ ℂ⊢wk∣↑∣ Γ ⊢ΔΓ′ ⊢ΓΓ′

𝕄⊢wk∣↑∣ : ∀ Γ →
          ℂ⊢ Δ ++ Γ′ →
          Γ ++ Γ′ 𝕄⊢ M ⦂ T / Γ₀ →
          --------------------------------------------
          let Γ″ , Γ‴ = splitAt (len Γ) Γ₀ in
          wk∣ len Δ ↑ len Γ ∣ Γ ++ Δ ++ Γ′ 𝕄⊢ wk∣ len Δ ↑ len Γ ∣ M ⦂ wk∣ len Δ ↑ len Γ ∣ T / wk∣ len Δ ↑ len Γ ∣ Γ″ ++ Δ ++ Γ‴
𝕄⊢wk∣↑∣ Γ ⊢ΔΓ′ (varₗ x) = varₗ {!!}
𝕄⊢wk∣↑∣ Γ ⊢ΔΓ′ (λₗ ⊢T ∘ ⊢M) = λₗ 𝕋⊢wk∣↑∣ Γ ⊢ΔΓ′ ⊢T ∘ {!𝕄⊢wk∣↑∣ (_ ∷ Γ) ⊢ΔΓ′ ⊢M!} -- requires weakening exchange
𝕄⊢wk∣↑∣ Γ ⊢ΔΓ′ (⊢M $ₗ∘ ⊢N) = 𝕄⊢wk∣↑∣ Γ ⊢ΔΓ′ ⊢M $ₗ∘ {!𝕄⊢wk∣↑∣ Γ ⊢ΔΓ′ ⊢N!}
𝕄⊢wk∣↑∣ Γ ⊢ΔΓ′ (bangₗ ⊢M) = {!!}
𝕄⊢wk∣↑∣ Γ ⊢ΔΓ′ (let-bangₗ ⊢M inₗ ⊢N) = let-bangₗ 𝕄⊢wk∣↑∣ Γ ⊢ΔΓ′ ⊢M inₗ {!!}
𝕄⊢wk∣↑∣ Γ ⊢ΔΓ′ (Λₗ⋆∙ ⊢M) = Λₗ⋆∙ 𝕄⊢wk∣↑∣ (_ ∷ Γ) ⊢ΔΓ′ ⊢M
𝕄⊢wk∣↑∣ Γ ⊢ΔΓ′ (⊢M $$ₗ∙ ⊢T) = {!!} -- requires weakening over substitution
