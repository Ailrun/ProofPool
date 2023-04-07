module Calculus.Elevator.Embedding.LambdaBox where

open import Agda.Primitive
open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_; length)
open import Data.Nat as ℕ using (ℕ; suc; s≤s)
import Data.Nat.Properties as ℕ
import Data.Nat.Induction as ℕ
open import Data.Product using (_×_; _,_; ∃; -,_)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary using (Rel; Antisymmetric; IsPartialOrder; IsDecPartialOrder)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)

open import Calculus.Elevator.Embedding.LambdaBox.ModeSpec
import Calculus.Elevator.Syntax as S
import Calculus.Elevator.Typing as T
import Calculus.Elevator.OpSem as O
open S ℳ²
open T ℳ²
open O ℳ²
import Calculus.LambdaBox.Syntax as DP
import Calculus.LambdaBox.OpSem as DP
import Calculus.LambdaBox.Typing as DP

infix 4 _~ᵀ_
infix 4 _⍮_~ᵍ_
infix 4 _⊢_~ᴹ_

pattern `↓ S = `↓[ cMode ⇒ pMode ] S
pattern `↑ S = `↑[ pMode ⇒ cMode ] S

pattern `lift M = `lift[ pMode ⇒ cMode ] M
pattern `unlift M = `unlift[ cMode ⇒ pMode ] M

pattern `return M = `return[ cMode ⇒ pMode ] M
pattern `let-return_`in_ M N = `let-return[ pMode ⇒ cMode ] M `in N

pattern `λ⦂ᵖ_∘_ S M = `λ⦂[ pMode ] S ∘ M

data _~ᵀ_ : DP.Type → Type → Set where
  `⊤   : ---------------------
         DP.`⊤ ~ᵀ `⊤

  `□   : DP.S ~ᵀ S →
         ------------------------
         DP.`□ DP.S ~ᵀ `↓ (`↑ S)

  _`→_ : DP.S ~ᵀ S →
         DP.T ~ᵀ T →
         --------------------------
         DP.S DP.`→ DP.T ~ᵀ S `⊸ T

data _⍮_~ᵍ_ : DP.Context → DP.Context → Context → Set where
  []   : --------------
         [] ⍮ [] ~ᵍ []

  _∷ᶜ_ : DP.S ~ᵀ S →
         DP.Δ ⍮ DP.Γ ~ᵍ Γ →
         ------------------------------------------------
         DP.S ∷ DP.Δ ⍮ DP.Γ ~ᵍ (`↑ S , cMode , true) ∷ Γ

  _∷ᵖ_ : DP.S ~ᵀ S →
         DP.Δ ⍮ DP.Γ ~ᵍ Γ →
         ---------------------------------------------
         DP.Δ ⍮ DP.S ∷ DP.Γ ~ᵍ (S , pMode , true) ∷ Γ

data _⍮_~ᵍ⁻- : ℕ → ℕ → Set where
  []   : ------------
         0 ⍮ 0 ~ᵍ⁻-

  ?∷ᶜ_ : k ⍮ k′ ~ᵍ⁻- →
         ------------------
         suc k ⍮ k′ ~ᵍ⁻-

  ?∷ᵖ_ : k ⍮ k′ ~ᵍ⁻- →
         ------------------
         k ⍮ suc k′ ~ᵍ⁻-

variable
  kk′~ᵍ⁻- : k ⍮ k′ ~ᵍ⁻-

-⍮-~ᵍ⁻-extractᶜ : k ⍮ k′ ~ᵍ⁻- →
                  k ⍮ 0 ~ᵍ⁻-
-⍮-~ᵍ⁻-extractᶜ []           = []
-⍮-~ᵍ⁻-extractᶜ (?∷ᶜ kk′~ᵍ⁻-) = ?∷ᶜ -⍮-~ᵍ⁻-extractᶜ kk′~ᵍ⁻-
-⍮-~ᵍ⁻-extractᶜ (?∷ᵖ kk′~ᵍ⁻-) = -⍮-~ᵍ⁻-extractᶜ kk′~ᵍ⁻-

-⍮-~ᵍ⁻-idxᶜ : {u : ℕ} → k ⍮ k′ ~ᵍ⁻- → u ℕ.< k → ℕ
-⍮-~ᵍ⁻-idxᶜ (?∷ᶜ kk′~ᵍ⁻-) (ℕ.s≤s ℕ.z≤n)         = 0
-⍮-~ᵍ⁻-idxᶜ (?∷ᶜ kk′~ᵍ⁻-) (ℕ.s≤s u<@(ℕ.s≤s u≤)) = suc (-⍮-~ᵍ⁻-idxᶜ kk′~ᵍ⁻- u<)
-⍮-~ᵍ⁻-idxᶜ (?∷ᵖ kk′~ᵍ⁻-) u<                    = suc (-⍮-~ᵍ⁻-idxᶜ kk′~ᵍ⁻- u<)

-⍮-~ᵍ⁻-idxᵖ : {x : ℕ} → k ⍮ k′ ~ᵍ⁻- → x ℕ.< k′ → ℕ
-⍮-~ᵍ⁻-idxᵖ (?∷ᶜ kk′~ᵍ⁻-)  x<                   = suc (-⍮-~ᵍ⁻-idxᵖ kk′~ᵍ⁻- x<)
-⍮-~ᵍ⁻-idxᵖ (?∷ᵖ kk′~ᵍ⁻-) (ℕ.s≤s ℕ.z≤n)         = 0
-⍮-~ᵍ⁻-idxᵖ (?∷ᵖ kk′~ᵍ⁻-) (ℕ.s≤s x<@(ℕ.s≤s x≤)) = suc (-⍮-~ᵍ⁻-idxᵖ kk′~ᵍ⁻- x<)

data _⊢_~ᴹ_ : k ⍮ k′ ~ᵍ⁻- → DP.Term → Term → Set where
  `unit         : --------------------------------------------
                  kk′~ᵍ⁻- ⊢ DP.`unit ~ᴹ `unit

  `box          : -⍮-~ᵍ⁻-extractᶜ kk′~ᵍ⁻- ⊢ DP.L ~ᴹ L →
                  --------------------------------------------
                  kk′~ᵍ⁻- ⊢ DP.`box DP.L ~ᴹ `return (`lift L)

  `let-box_`in_ : kk′~ᵍ⁻- ⊢ DP.L ~ᴹ L →
                  ?∷ᶜ kk′~ᵍ⁻- ⊢ DP.N ~ᴹ N →
                  -----------------------------------------------------------
                  kk′~ᵍ⁻- ⊢ DP.`let-box DP.L `in DP.N ~ᴹ `let-return L `in N

  `#¹_          : (u< : DP.u ℕ.< k) →
                  ---------------------------------------------------------------
                  kk′~ᵍ⁻- ⊢ DP.`#¹ DP.u ~ᴹ `unlift (`# (-⍮-~ᵍ⁻-idxᶜ kk′~ᵍ⁻- u<))

  `λ⦂_∙_        : DP.S ~ᵀ S →
                  ?∷ᵖ kk′~ᵍ⁻- ⊢ DP.L ~ᴹ L →
                  -------------------------------------------
                  kk′~ᵍ⁻- ⊢ DP.`λ⦂ DP.S ∙ DP.L ~ᴹ `λ⦂ᵖ S ∘ L

  _`$_          : kk′~ᵍ⁻- ⊢ DP.L ~ᴹ L →
                  kk′~ᵍ⁻- ⊢ DP.N ~ᴹ N →
                  ------------------------------------
                  kk′~ᵍ⁻- ⊢ DP.L DP.`$ DP.N ~ᴹ L `$ N

  `#⁰_          : (x< : DP.x ℕ.< k′) →
                  -----------------------------------------------------
                  kk′~ᵍ⁻- ⊢ DP.`#⁰ DP.x ~ᴹ `# (-⍮-~ᵍ⁻-idxᵖ kk′~ᵍ⁻- x<)

  `unlift-`lift : -⍮-~ᵍ⁻-extractᶜ kk′~ᵍ⁻- ⊢ DP.L ~ᴹ L →
                  --------------------------------------
                  kk′~ᵍ⁻- ⊢ DP.L ~ᴹ `unlift (`lift L)

depth~ᴹ : kk′~ᵍ⁻- ⊢ DP.M ~ᴹ M → ℕ
depth~ᴹ `unit                = 0
depth~ᴹ (`box ~M)            = suc (depth~ᴹ ~M)
depth~ᴹ (`let-box ~M `in ~N) = suc (depth~ᴹ ~M ℕ.⊔ depth~ᴹ ~N)
depth~ᴹ (`#¹ u)              = 0
depth~ᴹ (`λ⦂ ~S ∙ ~M)        = suc (depth~ᴹ ~M)
depth~ᴹ (~M `$ ~N)           = suc (depth~ᴹ ~M ℕ.⊔ depth~ᴹ ~N)
depth~ᴹ (`#⁰ x)              = 0
depth~ᴹ (`unlift-`lift ~M)   = suc (depth~ᴹ ~M)

~ᴹ-simulation-helper : DP.M DP.⟶ DP.M′ →
                       (DPM~ : [] ⊢ DP.M ~ᴹ M) →
                       Acc ℕ._<_ (depth~ᴹ DPM~) →
                       ∃ λ M′ → M ⟶* M′ × [] ⊢ DP.M′ ~ᴹ M′
~ᴹ-simulation-helper DP.ξ-`let-box DPL⟶ `in- (`let-box ~L `in ~M) (acc r)
  with _ , ⟶*L′ , ~L′ ← ~ᴹ-simulation-helper DPL⟶ ~L (r _ (s≤s (ℕ.m≤m⊔n _ _))) = -, ξ-of-⟶* (`let-return_`in _) ξ-`let-return[-⇒-]_`in- ⟶*L′ , `let-box ~L′ `in ~M
~ᴹ-simulation-helper DP.β-`□ (`let-box ~L `in ~M) r = {!!}
~ᴹ-simulation-helper DP.ξ- DPL⟶ `$? (~L `$ ~M) r = {!!}
~ᴹ-simulation-helper (DP.ξ-! x `$ DPL⟶) (~L `$ ~M) r = {!!}
~ᴹ-simulation-helper (DP.β-`→ x) (~L `$ ~M) r = {!!}
~ᴹ-simulation-helper DPL⟶ (`unlift-`lift ~L) r = {!!}

~ᴹ-simulation : DP.L DP.⟶ DP.L′ →
                [] ⊢ DP.L ~ᴹ L →
                ∃ λ L′ → L ⟶* L′ × [] ⊢ DP.L′ ~ᴹ L′
~ᴹ-simulation DPL⟶ ~L = ~ᴹ-simulation-helper DPL⟶ ~L (ℕ.<-wellFounded _)

~ᴹ⁻¹-simulation : L ⟶ L′ →
                  [] ⊢ DP.L ~ᴹ L →
                  ∃ λ DPL′ → DP.L DP.⟶* DPL′ × [] ⊢ DPL′ ~ᴹ L′
~ᴹ⁻¹-simulation (ξ-`unlift[-⇒-] (ξ-`lift[-⇒-] L⟶[≤])) (`unlift-`lift ~L) = -, ε , `unlift-`lift {!!}
-- lemma-preserve~ : [] ⊢ DP.L ~ᴹ L → L ⟶[ cMode ≤] L′ → [] ⊢ DP.L ~ᴹ L′
~ᴹ⁻¹-simulation (β-`↑ WL′) (`unlift-`lift ~L) = -, ε , ~L
~ᴹ⁻¹-simulation (ξ-`return[-⇒-] (ξ-`lift[-⇒-] L⟶[≤])) (`box ~L) = -, ε , `box {!!}
-- lemma-preserve~
~ᴹ⁻¹-simulation ξ-`let-return[-⇒-] L⟶ `in- (`let-box ~L `in ~M)
  with _ , DPL⟶* , ~L′ ← ~ᴹ⁻¹-simulation L⟶ ~L = -, DP.ξ-of-⟶* (DP.`let-box_`in _) DP.ξ-`let-box_`in- DPL⟶* , `let-box ~L′ `in ~M
~ᴹ⁻¹-simulation (β-`↓ (`lift WL)) (`let-box `box ~L `in ~M) = -, DP.β-`□ ◅ ε , {!!}
-- lemma : [] ⊢ DP.L ~ᴹ L → (?∷ᶜ []) ⊢ DP.M ~ᴹ M →
--         [] ⊢ DP.[ DP.L /¹ 0 ] DP.M ~ᴹ [ `lift L /[ cMode ] 0 ] M
~ᴹ⁻¹-simulation (β-`↓ (`neut x)) (`let-box ~L `in ~M) = {!!} -- impossible
~ᴹ⁻¹-simulation ξ- L⟶ `$? (~L `$ ~M)
  with _ , DPL⟶* , ~L′ ← ~ᴹ⁻¹-simulation L⟶ ~L = -, DP.ξ-of-⟶* (DP._`$ _) DP.ξ-_`$? DPL⟶* , ~L′ `$ ~M
~ᴹ⁻¹-simulation (ξ-! VL′ `$ M⟶) (~L `$ ~M)
  with _ , DPM⟶* , ~M′ ← ~ᴹ⁻¹-simulation M⟶ ~M = -, DP.ξ-of-⟶* (_ DP.`$_) (DP.ξ-! {!!} `$_) DPM⟶* , ~L `$ ~M′
-- lemma-value⁻¹ : [] ⊢ DPL ~ᴹ L → WeakNorm L → DP.Value DPL
~ᴹ⁻¹-simulation (β-`⊸ VM) ((`λ⦂ ~S ∙ ~L) `$ ~M) = -, DP.β-`→ {!!} ◅ ε , {!!}
-- lemma-value⁻¹
-- lemma : [] ⊢ DP.L ~ᴹ L → (?∷ᵖ []) ⊢ DP.M ~ᴹ M →
--         [] ⊢ DP.[ DP.L /⁰ 0 ] DP.M ~ᴹ [ `lift L /[ pMode ] 0 ] M
