{-# OPTIONS --without-K --safe #-}
module TypeTheory.AMLTT.ModeSpec where

open import Agda.Primitive public
open import Data.Bool as Bool using (Bool)
open import Data.Product using (_×_; proj₁)
open import Relation.Binary
import Relation.Binary.Construct.NonStrictToStrict as Strict
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Relation.Nullary
open import Relation.Nullary.Decidable using (_×-dec_; ¬?)

-- Might add universe cumulativity? How about predicativity?
data ModeSpecSt : Set where
  Wkₘ Coₘ : ModeSpecSt

data ModeSpecOp : Set where
  Natₘ Πₘ ↑ₘ ↓ₘ : ModeSpecOp

record ModeSpec ℓ₁ ℓ₂ : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    `Mode : Set ℓ₁
    _≤ₘ_ : Rel `Mode ℓ₂
    isPreorderₘ : IsPreorder _≡_ _≤ₘ_
    _≟ₘ_ : Decidable (_≡_ {A = `Mode})
    _≤?ₘ_ : Decidable _≤ₘ_
    stₘ : `Mode → ModeSpecSt → Bool
    opₘ : `Mode → ModeSpecOp → Bool
    isWellStructuredₘ : ∀ m₁ m₂ s → m₁ ≤ₘ m₂ → Bool.T (stₘ m₁ s) → Bool.T (stₘ m₂ s)

  preorderₘ : Preorder ℓ₁ ℓ₁ ℓ₂
  preorderₘ = record
    { Carrier = `Mode
    ; _≈_ = _≡_
    ; _∼_ = _≤ₘ_
    ; isPreorder = isPreorderₘ
    }

  _<ₘ_ = Strict._<_ _≡_ _≤ₘ_
  <ₘ⇒≤ₘ = proj₁

  _<?ₘ_ : Decidable _<ₘ_
  m₁ <?ₘ m₂ = m₁ ≤?ₘ m₂ ×-dec ¬? (m₁ ≟ₘ m₂)

  _≰ₘ_ : Rel `Mode ℓ₂
  x ≰ₘ y = ¬ (x ≤ₘ y)

  open Preorder preorderₘ using () renaming (refl to ≤ₘ-refl; trans to ≤ₘ-trans) public
