{-# OPTIONS --without-K --safe #-}
open import TypeTheory.AMLTT.ModeSpec

module TypeTheory.AMLTT.Typing {ℓ₁ ℓ₂} (ℳ : ModeSpec ℓ₁ ℓ₂) where

open import Data.Bool as Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Product
open import Relation.Binary.PropositionalEquality

open ModeSpec ℳ

import TypeTheory.AMLTT.Syntax as S
import TypeTheory.AMLTT.ContextOperation as CO
open S ℳ
open CO ℳ
open Variable

-- Typing rules
--

-- Should lower mode terms be ignored in equality?
-- No, but they should use a different equality (as we have weak normal form/canonical term in simply typed setting)

-- Substitution should preserve the mode
-- Γ ⊢ M ⦂ S ⋆ m and
-- Δ ⊢ σ ⦂ Γ ∥ m then
-- Δ ⊢ M [ σ ] ⦂ S [ σ ] ∥ m

infix  4 _¿_⊢_⦂_⋆_
infix  4 _⊢ᵗ_⦂_⋆_
infix  4 _⊢ᵀ_⦂_⋆_
infix  4 _¿_⊢_≈[_≤]_⦂_⋆_
infix  4 _⊢ᵗ_≈[_≤]_⦂_⋆_
infix  4 _⊢ᵀ_≈[_≤]_⦂_⋆_
infix  4 _¿_⊢s_⦂_⋆_
infix  4 _⊢sᵗ_⦂_⋆_
infix  4 _⊢sᵀ_⦂_⋆_
infix  4 _¿_⊢s_≈[_≤]_⦂_⋆_
infix  4 _⊢sᵗ_≈[_≤]_⦂_⋆_
infix  4 _⊢sᵀ_≈[_≤]_⦂_⋆_

data _¿_⊢_⦂_⋆_ : Bool → `Context → `Term → `Type → `Mode → Set (ℓ₁ ⊔ ℓ₂)
data _¿_⊢_≈[_≤]_⦂_⋆_ : Bool → `Context → `Term → `Mode → `Term → `Type → `Mode → Set (ℓ₁ ⊔ ℓ₂)
data _¿_⊢s_⦂_⋆_ : Bool → `Context → `Subst → `Context → `Mode → Set (ℓ₁ ⊔ ℓ₂)
data _¿_⊢s_≈[_≤]_⦂_⋆_ : Bool → `Context → `Subst → `Mode → `Subst → `Context → `Mode → Set (ℓ₁ ⊔ ℓ₂)

_⊢ᵗ_⦂_⋆_ = true ¿_⊢_⦂_⋆_
_⊢ᵀ_⦂_⋆_ = false ¿_⊢_⦂_⋆_

_⊢ᵗ_≈[_≤]_⦂_⋆_ = true ¿_⊢_≈[_≤]_⦂_⋆_
_⊢ᵀ_≈[_≤]_⦂_⋆_ = false ¿_⊢_≈[_≤]_⦂_⋆_

_⊢sᵗ_⦂_⋆_ = true ¿_⊢s_⦂_⋆_
_⊢sᵀ_⦂_⋆_ = false ¿_⊢s_⦂_⋆_

_⊢sᵗ_≈[_≤]_⦂_⋆_ = true ¿_⊢s_≈[_≤]_⦂_⋆_
_⊢sᵀ_≈[_≤]_⦂_⋆_ = false ¿_⊢s_≈[_≤]_⦂_⋆_

data _¿_⊢_⦂_⋆_ where

data _¿_⊢_≈[_≤]_⦂_⋆_ where

data _¿_⊢s_⦂_⋆_ where

data _¿_⊢s_≈[_≤]_⦂_⋆_ where
