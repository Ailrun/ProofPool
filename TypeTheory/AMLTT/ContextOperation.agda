{-# OPTIONS --without-K --safe #-}
open import TypeTheory.AMLTT.ModeSpec

module TypeTheory.AMLTT.ContextOperation {ℓ₁ ℓ₂} (ℳ : ModeSpec ℓ₁ ℓ₂) where

open import Data.Bool as Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality

open ModeSpec ℳ

import TypeTheory.AMLTT.Syntax as S

open S ℳ
open Variable

------------------------------------------------------------
-- Context Operations
--

-- Context Splitting
--
infix   4 _≅_e⋈_
infix   4 _≅_⋈_

data _⋆_≅_a⋈_ : `Useability → `Mode → `Useability → `Useability → Set (ℓ₁ ⊔ ℓ₂) where
  `⁺`⁺ : Bool.T (stₘ m Coₘ) →
         ---------------------
         `⁺ ⋆ m ≅ `⁺ a⋈ `⁺

  `⁺`⁻ : ------------------
         `⁺ ⋆ m ≅ `⁺ a⋈ `⁻

  `⁻`⁺ : ------------------
         `⁺ ⋆ m ≅ `⁻ a⋈ `⁺

  `⁻`⁻ : ------------------
         `⁻ ⋆ m ≅ `⁻ a⋈ `⁻

  `Ø`Ø : ------------------
         `Ø ⋆ m ≅ `Ø a⋈ `Ø

data _≅_e⋈_ : `ContextEntry → `ContextEntry → `ContextEntry → Set (ℓ₁ ⊔ ℓ₂) where
  `e : S ≡ S₀ →
       S ≡ S₁ →
       a ⋆ m ≅ a₀ a⋈ a₁ →
       ---------------------------------------
       S / a ⋆ m ≅ S₀ / a₀ ⋆ m e⋈ S₁ / a₁ ⋆ m

data _≅_⋈_ : `Context → `Context → `Context → Set (ℓ₁ ⊔ ℓ₂) where
  []  : -------------
        [] ≅ [] ⋈ []

  _∷_ : e ≅ e₀ e⋈ e₁ →
        Γ ≅ Γ₀ ⋈ Γ₁ →
        --------------------------------------------------
        e ∷ Γ ≅ e₀ ∷ Γ₀ ⋈ e₁ ∷ Γ₁

-- Full Context Weakening
--
infix   4 _∁

data _⋆_a∁ : `Useability → `Mode → Set (ℓ₁ ⊔ ℓ₂) where
  `⁺  : Bool.T (stₘ m Wkₘ) →
        ---------------------
        `⁺ ⋆ m a∁

  `⁻  : ----------
        `⁻ ⋆ m a∁

  `Ø  : ----------
        `Ø ⋆ m a∁

data _∁ : `Context → Set (ℓ₁ ⊔ ℓ₂) where
  []  : -----
        [] ∁

  _∷_ : a ⋆ m a∁ →
        Γ ∁ →
        ----------------
        S / a ⋆ m ∷ Γ ∁

-- Context Weakening Modulo Mode
--
infix   4 _e∥[_≤]≅_
infix   4 _∥[_≤]≅_

data _⋆_a∥[_≤]≅_ : `Useability → `Mode → `Mode → `Useability → Set (ℓ₁ ⊔ ℓ₂) where
  `⁺`⁺ : n ≤ₘ m →
         --------------------
         `⁺ ⋆ m a∥[ n ≤]≅ `⁺

  `⁺`Ø : n ≰ₘ m →
         Bool.T (stₘ m Wkₘ) →
         ---------------------
         `⁺ ⋆ m a∥[ n ≤]≅ `Ø

  `⁻`⁻ : n ≤ₘ m →
         --------------------
         `⁻ ⋆ m a∥[ n ≤]≅ `⁻

  `⁻`Ø : n ≰ₘ m →
         --------------------
         `⁻ ⋆ m a∥[ n ≤]≅ `Ø

  `Ø`Ø : --------------------
         `Ø ⋆ m a∥[ n ≤]≅ `Ø

data _e∥[_≤]≅_ : `ContextEntry → `Mode → `ContextEntry → Set (ℓ₁ ⊔ ℓ₂) where
  `e : S ≡ S′ →
       a ⋆ m a∥[ n ≤]≅ a′ →
       --------------------------------
       S / a ⋆ m e∥[ n ≤]≅ S′ / a′ ⋆ m

data _∥[_≤]≅_ : `Context → `Mode → `Context → Set (ℓ₁ ⊔ ℓ₂) where
  []  : ---------------
        [] ∥[ n ≤]≅ []

  _∷_ : e e∥[ n ≤]≅ e′ →
        Γ ∥[ n ≤]≅ Γ′ →
        -----------------------
        e ∷ Γ ∥[ n ≤]≅ e′ ∷ Γ′

-- Context Membership
--
infix   4 _⦂ᵗ_⋆_∈_
infix   4 _⦂ᵀ_⋆_∈_
infix   4 _¿_⦂_⋆_∈_

data _⦂ᵗ_⋆_∈_ : ℕ → `Type → `Mode → `Context → Set (ℓ₁ ⊔ ℓ₂) where
  here  : S ≡ S′ →
          Γ ∁ →
          -----------------------------------
          0 ⦂ᵗ S ⋆ m ∈ S′ / `⁺ ⋆ m ∷ Γ

  there : a ⋆ n a∁ →
          x ⦂ᵗ S ⋆ m ∈ Γ →
          --------------------------------
          suc x ⦂ᵗ S ⋆ m ∈ S′ / a ⋆ n ∷ Γ

data _⦂ᵀ_⋆_∈_ : ℕ → `Type → `Mode → `Context → Set (ℓ₁ ⊔ ℓ₂) where
  here  : S ≡ S′ →
          a ≢ `Ø →
          -----------------------------------
          0 ⦂ᵀ S ⋆ m ∈ S′ / a ⋆ m ∷ Γ

  there : x ⦂ᵀ S ⋆ m ∈ Γ →
          --------------------------------
          suc x ⦂ᵀ S ⋆ m ∈ S′ / a ⋆ n ∷ Γ

_¿_⦂_⋆_∈_ : Bool → ℕ → `Type → `Mode → `Context → Set (ℓ₁ ⊔ ℓ₂)
_¿_⦂_⋆_∈_ true  = _⦂ᵗ_⋆_∈_
_¿_⦂_⋆_∈_ false = _⦂ᵀ_⋆_∈_
