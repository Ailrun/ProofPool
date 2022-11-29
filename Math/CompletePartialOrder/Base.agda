open import Relation.Binary.Core

module Math.CompletePartialOrder.Base
  {a ℓ ℓ′} {A : Set a}
  (_≈_ : Rel A ℓ)
  (_≤_ : Rel A ℓ′)
  where

open import Agda.Primitive
open import Data.Product
open import Relation.Binary.Definitions
open import Relation.Binary.Structures _≈_
open import Relation.Unary

private
  variable
    ℓ″ : Level

record IsSubset (P : Pred A ℓ″) : Set (a ⊔ ℓ ⊔ ℓ″) where
  field
    P-resp-≈ : P Respects _≈_

record IsDirected (P : Pred A ℓ″) : Set (a ⊔ ℓ ⊔ ℓ′ ⊔ ℓ″) where
  field
    isSubset : IsSubset P
    satisfiable : Satisfiable P
    isPartialOrder : IsPartialOrder _≤_
    directed : ∀ {x y} → P x → P y → ∃ λ z → x ≤ z × y ≤ z × P z

  open IsSubset isSubset public
  module Partial = IsPartialOrder isPartialOrder

record IsUB (P : Pred A ℓ″) (ub : A) : Set (a ⊔ ℓ ⊔ ℓ′ ⊔ ℓ″) where
  field
    isSubset : IsSubset P
    isPartialOrder : IsPartialOrder _≤_
    upperbound : ∀ {x} → P x → x ≤ ub

  module Subset = IsSubset isSubset
  open IsPartialOrder isPartialOrder public

record IsLUB (P : Pred A ℓ″) (⊔P : A) : Set (a ⊔ ℓ ⊔ ℓ′ ⊔ ℓ″) where
  pattern
  field
    isUB : IsUB P ⊔P
    least : ∀ {ub} → IsUB P ub → ⊔P ≤ ub

  open IsUB isUB public

  unique : ∀ {⊔P′} → IsLUB P ⊔P′ → ⊔P ≈ ⊔P′
  unique record{ isUB = isUB′; least = least′ } = antisym (least isUB′) (least′ isUB)

record IsCPO {ℓ″} : Set (lsuc (a ⊔ ℓ ⊔ ℓ′ ⊔ ℓ″)) where
  field
    ⊥ : A
    isPartialOrder : IsPartialOrder _≤_
    isLeast : Minimum _≤_ ⊥
    complete : ∀ {P : Pred A ℓ″} → IsDirected P → ∃ (IsLUB P)

  open IsPartialOrder isPartialOrder public
