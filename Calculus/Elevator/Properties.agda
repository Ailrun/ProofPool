open import Calculus.Elevator.ModeSpec

module Calculus.Elevator.Properties ℓ₁ ℓ₂ (ℳ : ModeSpec ℓ₁ ℓ₂) where
module ℳ = ModeSpec ℳ
open ℳ

open import Agda.Primitive
open import Data.Bool as Bool using (Bool; true; false)
import Data.Bool.Properties as Bool
open import Data.Empty as ⊥ using (⊥)
open import Data.List as List using (List; []; _∷_; _++_)
import Data.List.Properties as List
open import Data.List.Relation.Unary.All as All using (All)
open import Data.Nat as ℕ using (ℕ; suc; _+_)
open import Data.Product as × using (_×_; _,_; proj₁; proj₂; ∃₂)
open import Data.Unit as ⊤ using (⊤)
import Function.Equivalence as FE
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst₂; _≢_; ≢-sym)

import Calculus.Elevator.Syntax as S
import Calculus.Elevator.Typing as T
import Calculus.Elevator.OpSem as O
open S ℓ₁ ℓ₂ ℳ
open T ℓ₁ ℓ₂ ℳ
open O ℓ₁ ℓ₂ ℳ

⊢∧<ₘ⇒⊢ : ⊢[ m ] Γ →
         m₀ <ₘ m →
         ----------------
         ⊢[ m₀ ] Γ
⊢∧<ₘ⇒⊢ []              <m = []
⊢∧<ₘ⇒⊢ (⊢S [ m≤ ]∷ ⊢Γ) <m = ⊢S [ ℳ.≤-trans (ℳ.<⇒≤ <m) m≤ ]∷ (⊢∧<ₘ⇒⊢ ⊢Γ <m)
⊢∧<ₘ⇒⊢ (⊢S [?]∷ ⊢Γ)    <m = ⊢S [?]∷ ⊢∧<ₘ⇒⊢ ⊢Γ <m

⊢∧-~-⊞-⇒⊢ : ⊢[ m ] Γ →
            Γ ~ Γ₀ ⊞ Γ₁ →
            ----------------
            ⊢[ m ] Γ₀ × ⊢[ m ] Γ₁
⊢∧-~-⊞-⇒⊢ []              []       = [] , []
⊢∧-~-⊞-⇒⊢ (⊢S [ m≤ ]∷ ⊢Γ) (_∷[_]_ {dS₀ = dS₀} {dS₁ = dS₁} {m = m} cS c Γ~)
  with ⊢Γ₀ , ⊢Γ₁ ← ⊢∧-~-⊞-⇒⊢ ⊢Γ Γ~
    with stₘ m ``Co | dS₀ | dS₁
...    | false | false | true      = ⊢S [?]∷ ⊢Γ₀ , ⊢S [ m≤ ]∷ ⊢Γ₁
...    | false | true  | false     = ⊢S [ m≤ ]∷ ⊢Γ₀ , ⊢S [?]∷ ⊢Γ₁
...    | true  | false | true      = ⊢S [?]∷ ⊢Γ₀ , ⊢S [ m≤ ]∷ ⊢Γ₁
...    | true  | true  | false     = ⊢S [ m≤ ]∷ ⊢Γ₀ , ⊢S [?]∷ ⊢Γ₁
...    | true  | true  | true      = ⊢S [ m≤ ]∷ ⊢Γ₀ , ⊢S [ m≤ ]∷ ⊢Γ₁
⊢∧-~-⊞-⇒⊢ (⊢S [?]∷ ⊢Γ)    (_∷[_]_ {dS₀ = false} {dS₁ = false} cS c Γ~) 
  with ⊢Γ₀ , ⊢Γ₁ ← ⊢∧-~-⊞-⇒⊢ ⊢Γ Γ~ = ⊢S [?]∷ ⊢Γ₀ , ⊢S [?]∷ ⊢Γ₁

⊢∧-~-⊞-⇒⊢₀ : ⊢[ m ] Γ →
             Γ ~ Γ₀ ⊞ Γ₁ →
             ----------------
             ⊢[ m ] Γ₀
⊢∧-~-⊞-⇒⊢₀ ⊢Γ Γ~ = proj₁ (⊢∧-~-⊞-⇒⊢ ⊢Γ Γ~)

⊢∧-~-⊞-⇒⊢₁ : ⊢[ m ] Γ →
             Γ ~ Γ₀ ⊞ Γ₁ →
             ----------------
             ⊢[ m ] Γ₁
⊢∧-~-⊞-⇒⊢₁ ⊢Γ Γ~ = proj₂ (⊢∧-~-⊞-⇒⊢ ⊢Γ Γ~)

⊢∧∤[-]⇒⊢ : ⊢[ m ] Γ →
           Γ ∤[ m₀ ] Γ′ →
           ----------------
           ⊢[ m₀ ] Γ′
⊢∧∤[-]⇒⊢ []              []                 = []
⊢∧∤[-]⇒⊢ (⊢S [ m≤ ]∷ ⊢Γ) (Wk∈ ∷≰[ ≰m₁ ] Γ∤) = ⊢S [?]∷ ⊢∧∤[-]⇒⊢ ⊢Γ Γ∤
⊢∧∤[-]⇒⊢ (⊢S [ m≤ ]∷ ⊢Γ) (   ∤∷≤[ ≤m₁ ] Γ∤) = ⊢S [ ≤m₁ ]∷ ⊢∧∤[-]⇒⊢ ⊢Γ Γ∤
⊢∧∤[-]⇒⊢ (⊢S [?]∷    ⊢Γ) (_   ∷≰[ ≰m₁ ] Γ∤) = ⊢S [?]∷ ⊢∧∤[-]⇒⊢ ⊢Γ Γ∤
⊢∧∤[-]⇒⊢ (⊢S [?]∷    ⊢Γ) (   ∤∷≤[ ≤m₁ ] Γ∤) = ⊢S [?]∷ ⊢∧∤[-]⇒⊢ ⊢Γ Γ∤

++-~⊞ : ∀ Γ₀ →
        Γ₀ ++ Γ₁ ~ Γ₂ ⊞ Γ₃ →
        ∃₂ (λ Γ₂₀ Γ₂₁ → (Γ₂ ≡ Γ₂₀ ++ Γ₂₁) ×
          ∃₂ (λ Γ₃₀ Γ₃₁ → (Γ₃ ≡ Γ₃₀ ++ Γ₃₁) ×
            Γ₀ ~ Γ₂₀ ⊞ Γ₃₀ × Γ₁ ~ Γ₂₁ ⊞ Γ₃₁))
++-~⊞ []                  Γ₁~ = [] , _ , refl , [] , _ , refl , [] , Γ₁~
++-~⊞ (.(_ , _ , _) ∷ Γ₀) (cS T.∷[ c ] Γ₀Γ₁~)
  with Γ₂₀ , _ , eq₂ , Γ₃₀ , _ , eq₃ , Γ₀~ , Γ₁~ ← ++-~⊞ Γ₀ Γ₀Γ₁~ = _ ∷ Γ₂₀ , _ , cong (_ ∷_) eq₂ , _ ∷ Γ₃₀ , _ , cong (_ ∷_) eq₃ , cS T.∷[ c ] Γ₀~ , Γ₁~

~⊞-respects-++ : Γ ~ Γ₀ ⊞ Γ₁ →
                 Δ ~ Δ₀ ⊞ Δ₁ →
                 Γ ++ Δ ~ Γ₀ ++ Δ₀ ⊞ Γ₁ ++ Δ₁
~⊞-respects-++ []             Δ~ = Δ~
~⊞-respects-++ (cS ∷[ c ] Γ~) Δ~ = cS ∷[ c ] (~⊞-respects-++ Γ~ Δ~)

~⊞-∤⁻¹ : Γ ~ Γ₀ ⊞ Γ₁ →
         Γ′ ∤[ m ] Γ → 
         ∃₂ (λ Γ′₀ Γ′₁ → Γ′ ~ Γ′₀ ⊞ Γ′₁ × Γ′₀ ∤[ m ] Γ₀ × Γ′₁ ∤[ m ] Γ₁)
~⊞-∤⁻¹ [] [] = _ , _ , [] , [] , []
~⊞-∤⁻¹ (cS ∷[ c ] Γ~) (Wk∈ ∷≰[ ≰m ] ∤Γ)
  with _ , _ , Γ′~ , ∤Γ₀ , ∤Γ₁ ← ~⊞-∤⁻¹ Γ~ ∤Γ = {!!} , {!!} , {!!} , {!!} , {!!}
~⊞-∤⁻¹ (cS ∷[ c ] Γ~) (   ∤∷≤[ ≤m ] ∤Γ) = {!!} , {!!} , {!!} , {!!} , {!!}

∤-backward-preserve-⊢ : Γ₀ ++ Γ′ ⊢[ m ] L ⦂ S →
                        Γ ∤[ m₀ ] Γ′ →
                        Γ₀ ++ Γ ⊢[ m ] L ⦂ S
∤-backward-preserve-⊢ `unit Γ∤ = `unit
∤-backward-preserve-⊢ (`λ⦂-∘ ⊢L) Γ∤ = `λ⦂-∘ (∤-backward-preserve-⊢ ⊢L Γ∤)
∤-backward-preserve-⊢ (Γ′~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M) Γ∤ = {!!} ⊢ ∤-backward-preserve-⊢ ⊢L {!!} ⦂ ⊢⊸ `$ ∤-backward-preserve-⊢ ⊢M {!!}
∤-backward-preserve-⊢ (`lift[-⇒-] ⊢L) Γ∤ = `lift[-⇒-] ∤-backward-preserve-⊢ ⊢L Γ∤
∤-backward-preserve-⊢ (Γ′∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑) Γ∤ = {!!} ⊢`unlift[-⇒-] {!!} ⦂ ⊢↑
∤-backward-preserve-⊢ (Γ′∤ ⊢`return[-⇒-] ⊢L) Γ∤ = {!!} ⊢`return[-⇒-] {!!}
∤-backward-preserve-⊢ (Γ′∼ ⊢`let-return[-⇒-] ⊢L ⦂ ⊢↓ `in ⊢M) Γ∤ = {!!}
∤-backward-preserve-⊢ (`# x) Γ∤ = {!!}

preservation    : ⊢[ m ] Γ →
                  ⊢[ m ] S ⦂⋆ →
                  Γ ⊢[ m ] L ⦂ S →
                  L ⟶ L′ →
                  -----------------
                  Γ ⊢[ m ] L′ ⦂ S
preservation[≤] : ⊢[ m ] Γ →
                  ⊢[ m ] S ⦂⋆ →
                  Γ ⊢[ m ] L ⦂ S →
                  ¬ (m₀ ≤ₘ m) →
                  L ⟶[ m₀ ≤] L′ →
                  -----------------
                  Γ ⊢[ m ] L′ ⦂ S

preservation ⊢Γ ⊢S                     (Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)                  ξ- L⟶ `$?                  = Γ~ ⊢ preservation (⊢∧-~-⊞-⇒⊢₀ ⊢Γ Γ~) ⊢⊸ ⊢L L⟶ ⦂ ⊢⊸ `$ ⊢M
preservation ⊢Γ ⊢S                     (Γ~ ⊢ ⊢L ⦂ ⊢T `⊸[ m ] ⊢S′ `$ ⊢M)      (ξ-! VL `$ M⟶)             = Γ~ ⊢ ⊢L ⦂ ⊢T `⊸[ m ] ⊢S′ `$ preservation (⊢∧-~-⊞-⇒⊢₁ ⊢Γ Γ~) ⊢T ⊢M M⟶
preservation ⊢Γ ⊢S                     (Γ~ ⊢ `λ⦂-∘ ⊢L ⦂ ⊢⊸ `$ ⊢M)            β-⊸                        = {!!}
preservation ⊢Γ (`↑[-⇒ <m ][ ↑∈m ] ⊢S) (`lift[-⇒-] ⊢L)                       (ξ-`lift[-⇒-] L⟶[≤])       = `lift[-⇒-] preservation[≤] (⊢∧<ₘ⇒⊢ ⊢Γ <m) ⊢S ⊢L (ℳ.<⇒≱ <m) L⟶[≤]
preservation ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)            (ξ-`unlift[-⇒-] L⟶)        = Γ∤ ⊢`unlift[-⇒-] preservation (⊢∧∤[-]⇒⊢ ⊢Γ Γ∤) ⊢↑ ⊢L L⟶ ⦂ ⊢↑
preservation ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] `lift[-⇒-] ⊢L ⦂ ⊢↑) (β-↑ WL)                   = {!!}
preservation ⊢Γ (`↓[-⇒ m< ][ ↓∈m ] ⊢S) (Γ∤ ⊢`return[-⇒-] ⊢L)                 (ξ-`return[-⇒-] L⟶)        = Γ∤ ⊢`return[-⇒-] preservation (⊢∧∤[-]⇒⊢ ⊢Γ Γ∤) ⊢S ⊢L L⟶
preservation ⊢Γ ⊢S                     (Γ~ ⊢`let-return[-⇒-] ⊢L ⦂ ⊢↓ `in ⊢M) ξ-`let-return[-⇒-] L⟶ `in- = Γ~ ⊢`let-return[-⇒-] preservation (⊢∧-~-⊞-⇒⊢₀ ⊢Γ Γ~) ⊢↓ ⊢L L⟶ ⦂ ⊢↓ `in ⊢M
preservation ⊢Γ ⊢S                     (Γ~ ⊢`let-return[-⇒-] ⊢L ⦂ ⊢↓ `in ⊢M) (β-↓ VL)                   = {!!}


preservation[≤] ⊢Γ ⊢S (Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M) ≮m ξ- L⟶[≤] `$? = Γ~ ⊢ preservation[≤] (⊢∧-~-⊞-⇒⊢₀ ⊢Γ Γ~) ⊢⊸ ⊢L ≮m L⟶[≤] ⦂ ⊢⊸ `$ ⊢M
preservation[≤] ⊢Γ ⊢S (Γ~ ⊢ ⊢L ⦂ ⊢T `⊸[ m ] ⊢S′ `$ ⊢M) ≮m (ξ-! WL `$ M⟶[≤]) = Γ~ ⊢ ⊢L ⦂ ⊢T `⊸[ m ] ⊢S′ `$ preservation[≤] (⊢∧-~-⊞-⇒⊢₁ ⊢Γ Γ~) ⊢T ⊢M ≮m M⟶[≤]
preservation[≤] ⊢Γ (`↑[-⇒ <m ][ ↑∈m ] ⊢S) (`lift[-⇒-] ⊢L) ≮m (ξ-`lift[-⇒-] L⟶[≤]) = `lift[-⇒-] preservation[≤] (⊢∧<ₘ⇒⊢ ⊢Γ <m) ⊢S ⊢L (λ m₁≤ → ≮m (ℳ.≤-trans m₁≤ (ℳ.<⇒≤ <m))) L⟶[≤] 
preservation[≤] ⊢Γ ⊢S (Γ∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑) ≮m (ξ-`unlift[≰ ≰m₀ ⇒-] L⟶[≤]) = Γ∤ ⊢`unlift[-⇒-] preservation[≤] (⊢∧∤[-]⇒⊢ ⊢Γ Γ∤) ⊢↑ ⊢L ≰m₀ L⟶[≤] ⦂ ⊢↑
preservation[≤] ⊢Γ ⊢S (Γ∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑) ≮m (ξ-`unlift[≤ ≤m₀ ⇒-] L⟶) = Γ∤ ⊢`unlift[-⇒-] preservation (⊢∧∤[-]⇒⊢ ⊢Γ Γ∤) ⊢↑ ⊢L L⟶ ⦂ ⊢↑
preservation[≤] ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] `lift[-⇒-] ⊢L ⦂ ⊢↑) ≮m (β-↑ m₀≤ WL) = {!!}
preservation[≤] ⊢Γ (`↓[-⇒ m< ][ ↓∈m ] ⊢S) (Γ∤ ⊢`return[-⇒-] ⊢L) ≮m (ξ-`return[≰ ≰m₀ ⇒-] L⟶[≤]) = Γ∤ ⊢`return[-⇒-] preservation[≤] (⊢∧∤[-]⇒⊢ ⊢Γ Γ∤) ⊢S ⊢L ≰m₀ L⟶[≤]
preservation[≤] ⊢Γ (`↓[-⇒ m< ][ ↓∈m ] ⊢S) (Γ∤ ⊢`return[-⇒-] ⊢L) ≮m (ξ-`return[≤ ≤m₀ ⇒-] L⟶) = Γ∤ ⊢`return[-⇒-] preservation (⊢∧∤[-]⇒⊢ ⊢Γ Γ∤) ⊢S ⊢L L⟶
preservation[≤] ⊢Γ ⊢S                     (Γ~ ⊢`let-return[-⇒-] ⊢L ⦂ ⊢↓ `in ⊢M) ≮m ξ-`let-return[-⇒-] L⟶[≤] `in? = Γ~ ⊢`let-return[-⇒-] preservation[≤] (⊢∧-~-⊞-⇒⊢₀ ⊢Γ Γ~) ⊢↓ ⊢L ≮m L⟶[≤] ⦂ ⊢↓ `in ⊢M
preservation[≤] ⊢Γ ⊢S                     (Γ~ ⊢`let-return[-⇒-] ⊢L ⦂ `↓[-⇒ m< ][ ↓∈m ] ⊢T `in ⊢M) ≮m (ξ-`let-return[-⇒-]! WL `in M⟶[≤]) = Γ~ ⊢`let-return[-⇒-] ⊢L ⦂ (`↓[-⇒ m< ][ ↓∈m ] ⊢T) `in preservation[≤] (⊢T [ ℳ.<⇒≤ m< ]∷ ⊢∧-~-⊞-⇒⊢₁ ⊢Γ Γ~) ⊢S ⊢M ≮m M⟶[≤]
preservation[≤] ⊢Γ (⊢S `⊸[ ⊸∈m ] ⊢T)      (`λ⦂-∘ ⊢L) ≮m (ξ-`λ⦂[-]-∘ L⟶[≤]) = `λ⦂-∘ preservation[≤] (⊢S [ ℳ.≤-refl ]∷ ⊢Γ) ⊢T ⊢L ≮m L⟶[≤]
-- Γ~ ⊢ ⊢L ⦂ ⊢T `⊸[ m ] ⊢S′ `$ preservation[≤] (⊢∧-~-⊞-⇒⊢₁ ⊢Γ Γ~) ⊢T ⊢M ? M⟶
