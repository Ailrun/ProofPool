module Calculus.LinearSide.Syntax.Properties where

open import Data.Nat hiding (_/_)
open import Data.Fin using (Fin)
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Unit hiding (_≟_)
open import Data.Vec using (Vec)
import Data.Vec as Vec
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.PropositionalEquality

open import Calculus.LinearSide.Syntax

module 𝕄App {ℓ} {T : ℕ → Set ℓ} (l : Lift T 𝕄) where
  open Lift l hiding (var) public

  infixl 8 _/_

  _/_ : 𝕄 m → Sub T m n → 𝕄 n
  varₗ x            / σ = lift (Vec.lookup σ x)
  λₗ T ∘ₗ M         / σ = λₗ T ∘ₗ (M / σ ↑)
  M $∘ₗ N           / σ = (M / σ) $∘ₗ (N / σ)
  bangₗ M           / σ = bangₗ (M / σ)
  let-bangₗ M inₗ N / σ = let-bangₗ (M / σ) inₗ (N / σ ↑)

  open Application (record { _/_ = _/_ }) using (_/✶_) public

  λₗ∘ₗ-/✶-↑✶ : ∀ k {m n U M} (σs : Subs T m n) →
               λₗ U ∘ₗ M /✶ σs ↑✶ k ≡ λₗ U ∘ₗ (M /✶ σs ↑✶ suc k)
  λₗ∘ₗ-/✶-↑✶ k ε        = refl
  λₗ∘ₗ-/✶-↑✶ k (σ ◅ σs) = cong₂ _/_ (λₗ∘ₗ-/✶-↑✶ k σs) refl

  $∘ₗ-/✶-↑✶ : ∀ k {m n M N} (σs : Subs T m n) →
              M $∘ₗ N /✶ σs ↑✶ k ≡ (M /✶ σs ↑✶ k) $∘ₗ (N /✶ σs ↑✶ k)
  $∘ₗ-/✶-↑✶ k ε        = refl
  $∘ₗ-/✶-↑✶ k (σ ◅ σs) = cong₂ _/_ ($∘ₗ-/✶-↑✶ k σs) refl

  bangₗ-/✶-↑✶ : ∀ k {m n M} (σs : Subs T m n) →
               bangₗ M /✶ σs ↑✶ k ≡ bangₗ (M /✶ σs ↑✶ k)
  bangₗ-/✶-↑✶ k ε        = refl
  bangₗ-/✶-↑✶ k (σ ◅ σs) = cong₂ _/_ (bangₗ-/✶-↑✶ k σs) refl

  let-bangₗ-inₗ-/✶-↑✶ : ∀ k {m n M N} (σs : Subs T m n) →
                        let-bangₗ M inₗ N /✶ σs ↑✶ k ≡ let-bangₗ (M /✶ σs ↑✶ k) inₗ (N /✶ σs ↑✶ suc k)
  let-bangₗ-inₗ-/✶-↑✶ k ε        = refl
  let-bangₗ-inₗ-/✶-↑✶ k (σ ◅ σs) = cong₂ _/_ (let-bangₗ-inₗ-/✶-↑✶ k σs) refl

𝕄Subst : TermSubst 𝕄
𝕄Subst = record { var = varₗ; app = 𝕄App._/_ }

open TermSubst 𝕄Subst using (_/Var_) public

module 𝕄Lemma {T₁ T₂} {l₁ : Lift T₁ 𝕄} {l₂ : Lift T₂ 𝕄} where
  open TermSubst 𝕄Subst
  open Lifted l₁ using () renaming (_↑✶_ to _↑✶₁_; _/✶_ to _/✶₁_)
  open Lifted l₂ using () renaming (_↑✶_ to _↑✶₂_; _/✶_ to _/✶₂_)
  open ≡-Reasoning

  /✶-↑✶ : ∀ {m n} (σs₁ : Subs T₁ m n) (σs₂ : Subs T₂ m n) →
          (∀ k x → varₗ x /✶₁ σs₁ ↑✶₁ k ≡ varₗ x /✶₂ σs₂ ↑✶₂ k) →
          --------------------------------------------------------
          ∀ k M → M /✶₁ σs₁ ↑✶₁ k ≡ M /✶₂ σs₂ ↑✶₂ k
  /✶-↑✶ σs₁ σs₂ hyp k (varₗ x)                            = hyp k x
  /✶-↑✶ σs₁ σs₂ hyp k (λₗ T ∘ₗ M)                         = begin
    λₗ T ∘ₗ M /✶₁ σs₁ ↑✶₁ k                                 ≡⟨ 𝕄App.λₗ∘ₗ-/✶-↑✶ _ k σs₁ ⟩
    λₗ T ∘ₗ (M /✶₁ σs₁ ↑✶₁ suc k)                           ≡⟨ cong λₗ _ ∘ₗ_ (/✶-↑✶ σs₁ σs₂ hyp (suc k) M) ⟩
    λₗ T ∘ₗ (M /✶₂ σs₂ ↑✶₂ suc k)                           ≡⟨ sym (𝕄App.λₗ∘ₗ-/✶-↑✶ _ k σs₂) ⟩
    λₗ T ∘ₗ M /✶₂ σs₂ ↑✶₂ k                                 ∎
  /✶-↑✶ σs₁ σs₂ hyp k (M $∘ₗ N)                           = begin
    M $∘ₗ N /✶₁ σs₁ ↑✶₁ k                                   ≡⟨ 𝕄App.$∘ₗ-/✶-↑✶ _ k σs₁ ⟩
    (M /✶₁ σs₁ ↑✶₁ k) $∘ₗ (N /✶₁ σs₁ ↑✶₁ k)                 ≡⟨ cong₂ _$∘ₗ_ (/✶-↑✶ σs₁ σs₂ hyp k M)
                                                                           (/✶-↑✶ σs₁ σs₂ hyp k N) ⟩
    (M /✶₂ σs₂ ↑✶₂ k) $∘ₗ (N /✶₂ σs₂ ↑✶₂ k)                 ≡˘⟨ 𝕄App.$∘ₗ-/✶-↑✶ _ k σs₂ ⟩
    M $∘ₗ N /✶₂ σs₂ ↑✶₂ k                                   ∎
  /✶-↑✶ σs₁ σs₂ hyp k (bangₗ M)                           = begin
    bangₗ M /✶₁ σs₁ ↑✶₁ k                                   ≡⟨ 𝕄App.bangₗ-/✶-↑✶ _ k σs₁ ⟩
    bangₗ (M /✶₁ σs₁ ↑✶₁ k)                                 ≡⟨ cong bangₗ (/✶-↑✶ σs₁ σs₂ hyp k M) ⟩
    bangₗ (M /✶₂ σs₂ ↑✶₂ k)                                 ≡˘⟨ 𝕄App.bangₗ-/✶-↑✶ _ k σs₂ ⟩
    bangₗ M /✶₂ σs₂ ↑✶₂ k                                   ∎
  /✶-↑✶ σs₁ σs₂ hyp k (let-bangₗ M inₗ N)                 = begin
    let-bangₗ M inₗ N /✶₁ σs₁ ↑✶₁ k                         ≡⟨ 𝕄App.let-bangₗ-inₗ-/✶-↑✶ _ k σs₁ ⟩
    let-bangₗ (M /✶₁ σs₁ ↑✶₁ k) inₗ (N /✶₁ σs₁ ↑✶₁ suc k)   ≡⟨ cong₂ let-bangₗ_inₗ_ (/✶-↑✶ σs₁ σs₂ hyp k M)
                                                                                    (/✶-↑✶ σs₁ σs₂ hyp (suc k) N) ⟩
    let-bangₗ (M /✶₂ σs₂ ↑✶₂ k) inₗ (N /✶₂ σs₂ ↑✶₂ suc k)   ≡˘⟨ 𝕄App.let-bangₗ-inₗ-/✶-↑✶ _ k σs₂ ⟩
    (let-bangₗ M inₗ N) /✶₂ σs₂ ↑✶₂ k                       ∎

𝕄Lemmas : TermLemmas 𝕄
𝕄Lemmas = record
  { termSubst = 𝕄Subst
  ; app-var   = refl
  ; /✶-↑✶     = 𝕄Lemma./✶-↑✶
  }

open TermLemmas 𝕄Lemmas public hiding (var)

infixr 9 _→ₗ_
infixr 9 λₗ_∙ₗ_

_→ₗ_ : 𝕋 → 𝕋 → 𝕋
T →ₗ U = !ₗ T ⊸ₗ U

λₗ_∙ₗ_ : 𝕋 → 𝕄 (suc n) → 𝕄 n
λₗ T ∙ₗ M = λₗ !ₗ T ∘ₗ let-bangₗ (varₗ 0) inₗ (weaken M)
