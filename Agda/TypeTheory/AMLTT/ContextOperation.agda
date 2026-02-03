{-# OPTIONS --without-K --safe #-}
open import TypeTheory.AMLTT.ModeSpec

module TypeTheory.AMLTT.ContextOperation {ℓ₁ ℓ₂} (ℳ : ModeSpec ℓ₁ ℓ₂) where

open import Data.Bool as Bool using (Bool; true; false)
open import Data.List using (List; [])
open import Data.Nat as ℕ using (ℕ; zero; suc)
open import Data.Product using (_×_)
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
infix   4 _⋆_≅_a⋈ᵗ_
infix   4 _⋆_≅_a⋈ᵀ_
infix   4 _¿_⋆_≅_a⋈_
infix   4 _¿_≅_e⋈_
infix   4 _¿_≅_⋈_
infix   4 _≅_⋈ᵗ_
infix   4 _≅_⋈ᵀ_

data _⋆_≅_a⋈ᵗ_ : `Useability → `Mode → `Useability → `Useability → Set (ℓ₁ ⊔ ℓ₂) where
  `⁺`⁺ : Bool.T (stₘ m Coₘ) →
         ---------------------
         `⁺ ⋆ m ≅ `⁺ a⋈ᵗ `⁺

  `⁺`⁻ : -------------------
         `⁺ ⋆ m ≅ `⁺ a⋈ᵗ `⁻

  `⁻`⁺ : -------------------
         `⁺ ⋆ m ≅ `⁻ a⋈ᵗ `⁺

  `⁻`⁻ : -------------------
         `⁻ ⋆ m ≅ `⁻ a⋈ᵗ `⁻

  `Ø`Ø : -------------------
         `Ø ⋆ m ≅ `Ø a⋈ᵗ `Ø

data _⋆_≅_a⋈ᵀ_ : `Useability → `Mode → `Useability → `Useability → Set (ℓ₁ ⊔ ℓ₂) where
  `Co : ----------------
        a ⋆ m ≅ a a⋈ᵀ a

_¿_⋆_≅_a⋈_ : Bool → `Useability → `Mode → `Useability → `Useability → Set (ℓ₁ ⊔ ℓ₂)
_¿_⋆_≅_a⋈_ true  = _⋆_≅_a⋈ᵗ_
_¿_⋆_≅_a⋈_ false = _⋆_≅_a⋈ᵀ_

data _¿_≅_e⋈_ : Bool → `ContextEntry → `ContextEntry → `ContextEntry → Set (ℓ₁ ⊔ ℓ₂) where
  `⟨_⋆_⟩ : S ≡ S₀ × S ≡ S₁ →
           b ¿ a ⋆ m ≅ a₀ a⋈ a₁ →
           ----------------------------------------------------------
           b ¿ `⟨ S ⋆ m / a ⟩ ≅ `⟨ S₀ ⋆ m / a₀ ⟩ e⋈ `⟨ S₁ ⋆ m / a₁ ⟩

data _¿_≅_⋈_ : Bool → `Context → `Context → `Context → Set (ℓ₁ ⊔ ℓ₂) where
  []  : -----------------
        b ¿ [] ≅ [] ⋈ []

  _∷_ : b ¿ e ≅ e₀ e⋈ e₁ →
        b ¿ Γ ≅ Γ₀ ⋈ Γ₁ →
        ---------------------------------
        b ¿ Γ `∙ e ≅ Γ₀ `∙ e₀ ⋈ Γ₁ `∙ e₁

_≅_⋈ᵗ_ = true ¿_≅_⋈_
_≅_⋈ᵀ_ = false ¿_≅_⋈_

-- Full Context Weakening
--
infix   4 _¿_⋆_a∁
infix   4 _⋆_a∁ᵗ
infix   4 _⋆_a∁ᵀ
infix   4 _¿_e∁
infix   4 _e∁ᵗ
infix   4 _e∁ᵀ
infix   4 _¿_∁
infix   4 _∁ᵗ
infix   4 _∁ᵀ

data _¿_⋆_a∁ : Bool → `Useability → `Mode → Set (ℓ₁ ⊔ ℓ₂) where
  `⁺  : (Bool.T b → Bool.T (stₘ m Wkₘ)) →
        ----------------------------------
        b ¿ `⁺ ⋆ m a∁

  `⁻  : --------------
        b ¿ `⁻ ⋆ m a∁

  `Ø  : --------------
        b ¿ `Ø ⋆ m a∁

_¿_e∁ : Bool → `ContextEntry → Set (ℓ₁ ⊔ ℓ₂)
b ¿ `⟨ S ⋆ m / a ⟩ e∁ = b ¿ a ⋆ m a∁

data _¿_∁ : Bool → `Context → Set (ℓ₁ ⊔ ℓ₂) where
  []  : ---------
        b ¿ [] ∁

  _∷_ : b ¿ e e∁ →
        b ¿ Γ ∁ →
        ---------------
        b ¿ Γ `∙ e ∁

_⋆_a∁ᵗ = true ¿_⋆_a∁
_⋆_a∁ᵀ = false ¿_⋆_a∁
_e∁ᵗ = true ¿_e∁
_e∁ᵀ = false ¿_e∁
_∁ᵗ = true ¿_∁
_∁ᵀ = false ¿_∁

-- Context Weakening Modulo Mode
--
infix   4 _¿_e∥[_≤]≅_
infix   4 _¿_∥[_≤]≅_
infix   4 _∥[_≤]ᵗ≅_
infix   4 _∥[_≤]ᵀ≅_

data _¿_⋆_a∥[_≤]≅_ : Bool → `Useability → `Mode → `Mode → `Useability → Set (ℓ₁ ⊔ ℓ₂) where
  refl : n ≤ₘ m →
         ----------------------
         b ¿ a ⋆ m a∥[ n ≤]≅ a

  `Ø   : n ≰ₘ m →
         b ¿ a ⋆ m a∁ →
         -----------------------
         b ¿ a ⋆ m a∥[ n ≤]≅ `Ø

data _¿_e∥[_≤]≅_ : Bool → `ContextEntry → `Mode → `ContextEntry → Set (ℓ₁ ⊔ ℓ₂) where
  `⟨_⋆_⟩ : S ≡ S′ →
           b ¿ a ⋆ m a∥[ n ≤]≅ a′ →
           ----------------------------------------------
           b ¿ `⟨ S ⋆ m / a ⟩ e∥[ n ≤]≅ `⟨ S′ ⋆ m / a′ ⟩

data _¿_∥[_≤]≅_ : Bool → `Context → `Mode → `Context → Set (ℓ₁ ⊔ ℓ₂) where
  []  : -------------------
        b ¿ [] ∥[ n ≤]≅ []

  _∷_ : b ¿ e e∥[ n ≤]≅ e′ →
        b ¿ Γ ∥[ n ≤]≅ Γ′ →
        -----------------------------
        b ¿ Γ `∙ e ∥[ n ≤]≅ Γ′ `∙ e′

_∥[_≤]ᵗ≅_ = true ¿_∥[_≤]≅_
_∥[_≤]ᵀ≅_ = false ¿_∥[_≤]≅_

-- Context Membership
--
infix   4 _¿_is-useable
infix   4 _¿_⦂_⋆_∈_
infix   4 _⦂ᵗ_⋆_∈_
infix   4 _⦂ᵀ_⋆_∈_

data _¿_is-useable : Bool → `Useability → Set (ℓ₁ ⊔ ℓ₂) where
  `⁺ : ------------------
       b ¿ `⁺ is-useable

  `⁻ : ----------------------
       false ¿ `⁻ is-useable

data _¿_⦂_⋆_∈_ : Bool → ℕ → `Type → `Mode → `Context → Set (ℓ₁ ⊔ ℓ₂) where
  here  : S ≡ S′ →
          b ¿ a is-useable →
          b ¿ Γ ∁ →
          -------------------------------------
          b ¿ 0 ⦂ S ⋆ m ∈ Γ `∙ `⟨ S′ ⋆ m / a ⟩

  there : b ¿ a ⋆ n a∁ →
          b ¿ x ⦂ S ⋆ m ∈ Γ →
          -----------------------------------------
          b ¿ suc x ⦂ S ⋆ m ∈ Γ `∙ `⟨ S′ ⋆ n / a ⟩

_⦂ᵗ_⋆_∈_ = true ¿_⦂_⋆_∈_
_⦂ᵀ_⋆_∈_ = true ¿_⦂_⋆_∈_
