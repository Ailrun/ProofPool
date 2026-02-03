module Calculus.SystemF.Properties where

open import Data.List using ([]; _∷_; _++_; length)
open import Data.Nat using (_≟_; _≥?_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes; no)

open import Calculus.SystemF.Syntax
open import Calculus.SystemF.Typing

-- Remove once non-trivial cases are done
postulate
  trivialWith : {A B : Set} → A → B

trivial : {A : Set} → A
trivial = trivialWith 0

⊢wkTy[-↑-]⦂Ty : ∀ Γ₀ →
                ⊢ Γ₀ ++ Γ₁ wf →
                ⊢ Γ ++ Γ₁ wf →
                Γ₀ ++ Γ₁ ⊢ Q ⦂Ty →
                wkCtx[ length Γ ] Γ₀ ++ Γ ++ Γ₁ ⊢ wkTy[ length Γ ↑ length Γ₀ ] Q ⦂Ty
⊢wkTy[-↑-]⦂Ty = {!!}

⊢wkCtx[-↑-]wf : ∀ Γ₀ →
                ⊢ Γ₀ ++ Γ₁ wf →
                ⊢ Γ ++ Γ₁ wf →
                ⊢ wkCtx[ length Γ ] Γ₀ ++ Γ ++ Γ₁ wf
⊢wkCtx[-↑-]wf = {!!}

⊢Ty[-/-]⦂Ty : ∀ Γ₀ →
              ⊢ Γ₀ ++ Γ₁ wf →
              Γ₁ ⊢ Q ⦂Ty →
              Γ₀ ++ kindTy ∷ Γ₁ ⊢ R ⦂Ty →
              Ctx[ Q ] Γ₀ ++ Γ₁ ⊢ Ty[ wkTy[ length Γ₀ ↑ 0 ] Q / length Γ₀ ] R ⦂Ty
⊢Ty[-/-]⦂Ty Γ₀ ⊢Γ₀Γ₁ ⊢Q bot = bot
⊢Ty[-/-]⦂Ty Γ₀ ⊢Γ₀Γ₁ ⊢Q (⊢R ⇒ ⊢S) = (⊢Ty[-/-]⦂Ty Γ₀ ⊢Γ₀Γ₁ ⊢Q ⊢R) ⇒ (⊢Ty[-/-]⦂Ty Γ₀ ⊢Γ₀Γ₁ ⊢Q ⊢S)
⊢Ty[-/-]⦂Ty Γ₀ ⊢Γ₀Γ₁ ⊢Q (‼ ⊢R) = ‼ {!!}
⊢Ty[-/-]⦂Ty Γ₀ ⊢Γ₀Γ₁ ⊢Q (#_ {a = a} a∈)
  with a ≥? length Γ₀
...  | no  a≱Γ₀ = # trivialWith (a≱Γ₀ , a∈)
...  | yes a≥Γ₀
    with a ≟ length Γ₀
...    | no  a≢Γ₀ = # trivialWith (a≢Γ₀ , a∈)
...    | yes refl = {!!}
