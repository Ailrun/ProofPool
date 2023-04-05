{-# OPTIONS --safe #-}
module Calculus.Elevator.ModeSpec where

open import Agda.Primitive
open import Data.Bool as Bool using (Bool)
open import Data.Product using (_×_; proj₁)
open import Relation.Nullary
open import Relation.Binary
import Relation.Binary.Construct.NonStrictToStrict as Strict
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

data ModeSpecSt : Set where
  ``Wk ``Co : ModeSpecSt

data ModeSpecOp : Set where
  ``⊤ ``⊸ ``↑ ``↓ : ModeSpecOp

record ModeSpec ℓ₁ ℓ₂ : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    Mode : Set ℓ₁
    _≤ₘ_ : Rel Mode (ℓ₁ ⊔ ℓ₂)
    isDecPartialOrderₘ : IsDecPartialOrder _≡_ _≤ₘ_
    stₘ : Mode → ModeSpecSt → Bool
    opₘ : Mode → ModeSpecOp → Bool
    isWellStructuredₘ : ∀ m₁ m₂ s → m₁ ≤ₘ m₂ → Bool.T (stₘ m₁ s) → Bool.T (stₘ m₂ s)

  _<ₘ_ = Strict._<_ _≡_ _≤ₘ_
  <ₘ⇒≤ₘ = proj₁

  decPosetₘ : DecPoset ℓ₁ ℓ₁ (ℓ₁ ⊔ ℓ₂)
  decPosetₘ = record
    { Carrier = Mode
    ; _≈_ = _≡_
    ; _≤_ = _≤ₘ_
    ; isDecPartialOrder = isDecPartialOrderₘ
    }

  open DecPoset decPosetₘ using () renaming (refl to ≤ₘ-refl; trans to ≤ₘ-trans; _≟_ to _≟ₘ_; _≤?_ to _≤?ₘ_) public
