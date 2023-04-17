------------------------------------------------------------
-- An Instance of Mode Specification for λ↑↓₂
------------------------------------------------------------

module Calculus.Elevator.Embedding.LambdaBox.ModeSpec where

open import Agda.Primitive
open import Data.Bool using (Bool; true; false)
open import Relation.Binary using (Rel; _⇒_; Transitive; Antisymmetric; IsPreorder; IsPartialOrder; IsDecPartialOrder)
open import Relation.Binary.PropositionalEquality as ≡ using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)

open import Calculus.Elevator.ModeSpec

data Mode² : Set where
  cMode pMode : Mode²

data _≤ₘ²_ : Rel Mode² lzero where
  refl : ∀ {m} →
         --------
         m ≤ₘ² m

  p≤c  : ----------------
         pMode ≤ₘ² cMode

≤ₘ²-reflexive : _≡_ ⇒ _≤ₘ²_
≤ₘ²-reflexive refl = refl

≤ₘ²-trans : Transitive _≤ₘ²_
≤ₘ²-trans refl m′≤m″ = m′≤m″
≤ₘ²-trans p≤c  refl  = p≤c

isPreorderₘ² : IsPreorder _≡_ _≤ₘ²_
isPreorderₘ² = record
               { isEquivalence = ≡.isEquivalence
               ; reflexive = ≤ₘ²-reflexive
               ; trans = ≤ₘ²-trans
               }

≤ₘ²-antisym : Antisymmetric _≡_ _≤ₘ²_
≤ₘ²-antisym refl refl = refl

isPartialOrderₘ² : IsPartialOrder _≡_ _≤ₘ²_
isPartialOrderₘ² = record
                   { isPreorder = isPreorderₘ²
                   ; antisym = ≤ₘ²-antisym
                   }

_≟ₘ²_ : ∀ (m m′ : Mode²) → Dec (m ≡ m′)
cMode ≟ₘ² cMode = yes refl
cMode ≟ₘ² pMode = no λ ()
pMode ≟ₘ² cMode = no λ ()
pMode ≟ₘ² pMode = yes refl

_≤?ₘ²_ : ∀ m m′ → Dec (m ≤ₘ² m′)
cMode ≤?ₘ² cMode = yes refl
cMode ≤?ₘ² pMode = no λ ()
pMode ≤?ₘ² cMode = yes p≤c
pMode ≤?ₘ² pMode = yes refl

isDecPartialOrderₘ² : IsDecPartialOrder _≡_ _≤ₘ²_
isDecPartialOrderₘ² = record
                      { isPartialOrder = isPartialOrderₘ²
                      ; _≟_ = _≟ₘ²_
                      ; _≤?_ = _≤?ₘ²_
                      }

stₘ² : Mode² → ModeSpecSt → Bool
stₘ² m st = true

opₘ² : Mode² → ModeSpecOp → Bool
opₘ² cMode ``⊤ = true
opₘ² cMode ``⊸ = true
opₘ² cMode ``↑ = true
opₘ² cMode ``↓ = false
opₘ² pMode ``⊤ = true
opₘ² pMode ``⊸ = true
opₘ² pMode ``↑ = false
opₘ² pMode ``↓ = true

ℳ² : ModeSpec _ _
ℳ² = record
     { Mode = Mode²
     ; _≤ₘ_ = _≤ₘ²_
     ; isDecPartialOrderₘ = isDecPartialOrderₘ²
     ; stₘ = stₘ²
     ; opₘ = opₘ²
     ; isWellStructuredₘ = λ _ _ _ _ t → t
     }
