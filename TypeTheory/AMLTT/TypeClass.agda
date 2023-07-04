{-# OPTIONS --without-K --safe #-}
module TypeTheory.AMLTT.TypeClass where

open import Agda.Primitive

record HasSubst {ℓ ℓ′} (A : Set ℓ) (B : Set ℓ′) : Set (ℓ ⊔ ℓ′) where
  infixl 4.5 _`⟦_⟧
  field
    _`⟦_⟧ : A → B → A

open HasSubst {{...}} public
