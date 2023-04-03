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
    isDecPartialOrder : IsDecPartialOrder _≡_ _≤ₘ_
    stₘ : Mode → ModeSpecSt → Bool
    opₘ : Mode → ModeSpecOp → Bool
    isWellStructured : ∀ m₁ m₂ s → m₁ ≤ₘ m₂ → Bool.T (stₘ m₁ s) → Bool.T (stₘ m₂ s)

  _≤?ₘ_ = isDecPartialOrder .IsDecPartialOrder._≤?_
  _<ₘ_ = Strict._<_ _≡_ _≤ₘ_
  <⇒≤ = proj₁

  decPoset : DecPoset ℓ₁ ℓ₁ (ℓ₁ ⊔ ℓ₂)
  decPoset = record
    { Carrier = Mode
    ; _≈_ = _≡_
    ; _≤_ = _≤ₘ_
    ; isDecPartialOrder = isDecPartialOrder
    }

  open DecPoset decPoset hiding (_≟_; _≤?_) renaming (refl to ≤-refl; trans to ≤-trans) public
  open import Relation.Binary.Properties.Poset poset public
