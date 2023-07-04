{-# OPTIONS --without-K --safe #-}
open import TypeTheory.AMLTT.ModeSpec

module TypeTheory.AMLTT.Typing {ℓ₁ ℓ₂} (ℳ : `ModeSpec ℓ₁ ℓ₂) where

open import Data.Product
open import Relation.Binary.PropositionalEquality

-- How should we deal with
-- (l , true , `Nat) ∷ (l , true , `Fin # 0) ∷ (l , true , `Fin # 1) ∷ [] ⊢[ l ] (# 0 , # 1) : `Fin (# 2) × `Fin (# 2)
-- ?
-- Instead of true/false, let's use unused/used/disabled, and both unused/used are useable in type checking/equality.

-- Should lower mode terms be ignored in equality?
-- No, but they should use a different equality (as we have weak normal form/canonical term in simply typed setting)

-- Substitution should preserve the mode
-- Γ ⊢[ m ] M ⦂ S and
-- Δ ⊢[ m ] σ ⦂ Γ then
-- Δ ⊢[ m ] M [ σ ] ⦂ S [ σ ]
