module Calculus.Elevator.ModeSpec where

open import Agda.Primitive
open import Data.Bool as Bool using (Bool)
open import Data.Product using (_×_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

data ModeSpecSt : Set where
  ``Wk ``Co : ModeSpecSt

data ModeSpecOp : Set where
  ``⊤ ``⊸ ``↑ ``↓ : ModeSpecOp

record ModeSpec ℓ₁ ℓ₂ : Set (lsuc (ℓ₁ ⊔ ℓ₂)) where
  field
    Mode : Set ℓ₁
    _≤ₘ_ : Rel Mode (ℓ₁ ⊔ ℓ₂)
    isPartialOrder : IsPartialOrder _≡_ _≤ₘ_
    stₘ : Mode → ModeSpecSt → Bool
    opₘ : Mode → ModeSpecOp → Bool
    isWellStructured : ∀ m₁ m₂ s → m₁ ≤ₘ m₂ → stₘ m₁ s Bool.≤ stₘ m₂ s

  _<ₘ_ : Rel Mode (ℓ₁ ⊔ ℓ₂)
  m₁ <ₘ m₂ = m₁ ≤ₘ m₂ × m₁ ≢ m₂
