{-# OPTIONS --without-K --safe #-}
open import TypeTheory.AMLTT.ModeSpec

module TypeTheory.AMLTT.Typing {ℓ₁ ℓ₂} (ℳ : ModeSpec ℓ₁ ℓ₂) where

open import Data.Bool as Bool using (Bool; true; false)
open import Data.List using (List; [])
open import Data.Nat as ℕ using (ℕ; zero; suc)
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

infix  4 _e⊢_⋆_
infix  4 ⊢_⋆_
infix  4 _¿_⊢_⦂_⋆_
infix  4 _⊢ᵗ_⦂_⋆_
infix  4 _⊢ᵀ_⦂_⋆_
infix  4 _¿_⊢_≈[_≤]_⦂_⋆_
infix  4 _⊢ᵗ_≈[_≤]_⦂_⋆_
infix  4 _⊢ᵀ_≈[_≤]_⦂_⋆_
infix  4 _¿_s⊢_⦂_⋆_
infix  4 _s⊢ᵗ_⦂_⋆_
infix  4 _s⊢ᵀ_⦂_⋆_
infix  4 _¿_s⊢_≈[_≤]_⦂_⋆_
infix  4 _s⊢ᵗ_≈[_≤]_⦂_⋆_
infix  4 _s⊢ᵀ_≈[_≤]_⦂_⋆_

data ⊢_⋆_ : `Context → `Mode → Set (ℓ₁ ⊔ ℓ₂)
data ⊢_≈[_≤]_⋆_ : `Context → `Mode → `Context → `Mode → Set (ℓ₁ ⊔ ℓ₂)
data _¿_⊢_⦂_⋆_ : Bool → `Context → `Term → `Type → `Mode → Set (ℓ₁ ⊔ ℓ₂)
data _¿_⊢_≈[_≤]_⦂_⋆_ : Bool → `Context → `Term → `Mode → `Term → `Type → `Mode → Set (ℓ₁ ⊔ ℓ₂)
data _¿_s⊢_⦂_⋆_ : Bool → `Context → `Subst → `Context → `Mode → Set (ℓ₁ ⊔ ℓ₂)
data _¿_s⊢_≈[_≤]_⦂_⋆_ : Bool → `Context → `Subst → `Mode → `Subst → `Context → `Mode → Set (ℓ₁ ⊔ ℓ₂)

_⊢ᵗ_⦂_⋆_ = true ¿_⊢_⦂_⋆_
_⊢ᵀ_⦂_⋆_ = false ¿_⊢_⦂_⋆_

_⊢ᵗ_≈[_≤]_⦂_⋆_ = true ¿_⊢_≈[_≤]_⦂_⋆_
_⊢ᵀ_≈[_≤]_⦂_⋆_ = false ¿_⊢_≈[_≤]_⦂_⋆_

_s⊢ᵗ_⦂_⋆_ = true ¿_s⊢_⦂_⋆_
_s⊢ᵀ_⦂_⋆_ = false ¿_s⊢_⦂_⋆_

_s⊢ᵗ_≈[_≤]_⦂_⋆_ = true ¿_s⊢_≈[_≤]_⦂_⋆_
_s⊢ᵀ_≈[_≤]_⦂_⋆_ = false ¿_s⊢_≈[_≤]_⦂_⋆_

data a⊢_/_⋆_ : `Mode → `Useability → `Mode → Set (ℓ₁ ⊔ ℓ₂) where
  `⁺ : m ≤ₘ h →
       --------------
       a⊢ h / `⁺ ⋆ m

  `⁻ : m ≤ₘ h →
       --------------
       a⊢ h / `⁻ ⋆ m

  `Ø : --------------
       a⊢ h / `Ø ⋆ m

-- What's the relation between n and h?
data a⊢_/_≈[_≤]_/_⋆_ : `Mode → `Useability → `Mode → `Mode → `Useability → `Mode → Set (ℓ₁ ⊔ ℓ₂) where
  `⁺ : m ≤ₘ h →
       -----------------------------
       a⊢ h / `⁺ ≈[ n ≤] h / `⁺ ⋆ m

  `⁻ : m ≤ₘ h →
       -----------------------------
       a⊢ h / `⁻ ≈[ n ≤] h / `⁻ ⋆ m

  `Ø : -----------------------------
       a⊢ h / `Ø ≈[ n ≤] h / `Ø ⋆ m

data _e⊢_⋆_ : `Context → `ContextEntry → `Mode → Set (ℓ₁ ⊔ ℓ₂) where
  _⊢`⟨_⋆_⟩ : Γ ∥[ h ≤]ᵀ≅ Γ′ →
             Γ′ ⊢ᵀ S ⦂ `Univ i ⋆ h →
             a⊢ h / a ⋆ m →
             -------------------------
             Γ e⊢ `⟨ S ⋆ h / a ⟩ ⋆ m

data _e⊢_≈[_≤]_⋆_ : `Context → `ContextEntry → `Mode → `ContextEntry → `Mode → Set (ℓ₁ ⊔ ℓ₂) where
  _⊢`⟨_⋆_⟩ : Γ ∥[ h ≤]ᵀ≅ Γ′ →
             Γ′ ⊢ᵀ S ≈[ n ≤] S′ ⦂ `Univ i ⋆ h →
             a⊢ h / a ≈[ n ≤] h / a′ ⋆ m →
             -------------------------------------------------
             Γ e⊢ `⟨ S ⋆ h / a ⟩ ≈[ n ≤] `⟨ S′ ⋆ h / a′ ⟩ ⋆ m

data ⊢_⋆_ where
  []  : ---------
        ⊢ [] ⋆ m

  _∷_ : ⊢ Γ ⋆ m →
        Γ e⊢ e ⋆ m →
        -------------
        ⊢ Γ `∙ e ⋆ m

data ⊢_≈[_≤]_⋆_ where
  []  : --------------------
        ⊢ [] ≈[ n ≤] [] ⋆ m

  _∷_ : ⊢ Γ ≈[ n ≤] Γ′ ⋆ m →
        Γ e⊢ e ≈[ n ≤] e′ ⋆ m →
        ------------------------------
        ⊢ Γ `∙ e ≈[ n ≤] Γ′ `∙ e′ ⋆ m

data _¿_⊢_⦂_⋆_ where
  -- (Cumulative) Universe
  --
  _⊢`Univ  : b ¿ Γ ∁ →
             ------------------------------------
             b ¿ Γ ⊢ `Univ i ⦂ `Univ (suc i) ⋆ m

  `cumul   : b ¿ Γ ⊢ S ⦂ `Univ i ⋆ m →
             ------------------------------
             b ¿ Γ ⊢ S ⦂ `Univ (suc i) ⋆ m

  -- Upshift
  --
  `↑[_⇗_]_          : l <ₘ m →
                      Bool.T (opₘ m ↑ₘ) →
                      b ¿ Γ ⊢ S ⦂ `Univ i ⋆ l →
                      ------------------------------------
                      b ¿ Γ ⊢ `↑[ l ⇗ m ] S ⦂ `Univ i ⋆ m

  `lift[_⇗_]_       : l <ₘ m →
                      Bool.T (opₘ m ↑ₘ) →
                      b ¿ Γ ⊢ s ⦂ S ⋆ l →
                      ---------------------------------------------
                      b ¿ Γ ⊢ `lift[ l ⇗ m ] s ⦂ `↑[ l ⇗ m ] S ⋆ m

  _&_⊢`unlift[-⇗-]_ : ⊢ Γ ⋆ m →
                      b ¿ Γ ∥[ h ≤]≅ Γ′ →
                      b ¿ Γ′ ⊢ s ⦂ `↑[ m ⇗ h ] S ⋆ h →
                      -----------------------------------
                      b ¿ Γ ⊢ `unlift[ m ⇗ h ] s ⦂ S ⋆ m

  -- Downshift
  --
  _&_⊢`↓[_⇘_]_                : ⊢ Γ ⋆ m →
                                b ¿ Γ ∥[ h ≤]≅ Γ′ →
                                m <ₘ h →
                                Bool.T (opₘ m ↑ₘ) →
                                b ¿ Γ′ ⊢ S ⦂ `Univ i ⋆ h →
                                ------------------------------------
                                b ¿ Γ ⊢ `↓[ h ⇘ m ] S ⦂ `Univ i ⋆ m

  _&_⊢`return[_⇘_]_           : ⊢ Γ ⋆ m →
                                b ¿ Γ ∥[ h ≤]≅ Γ′ →
                                m <ₘ h →
                                Bool.T (opₘ m ↑ₘ) →
                                b ¿ Γ′ ⊢ s ⦂ S ⋆ h →
                                -----------------------------------------------
                                b ¿ Γ ⊢ `return[ m ⇘ h ] s ⦂ `↓[ h ⇘ m ] S ⋆ m

  _⊢`let-return[-⇘-]_then_of_ : b ¿ Γ ≅ Γ₀ ⋈ Γ₁ →
                                b ¿ Γ₀ ⊢ s ⦂ `↓[ h ⇘ m ] S ⋆ m →
                                b ¿ Γ₁ `∙ `⟨ S ⋆ h / `⁺ ⟩ ⊢ t ⦂ T `⟦| `return[ h ⇘ m ] `# 0 ⟧ ⋆ m →
                                Γ₁ `∙ `⟨ `↓[ h ⇘ m ] S ⋆ m / `⁺ ⟩ ⊢ᵀ T ⦂ `Univ i ⋆ m →
                                --------------------------------------------------------------
                                b ¿ Γ ⊢ `let-return[ m ⇘ h ] s then t of T ⦂ T `⟦| s ⟧ ⋆ m

  -- Natural number
  --
  _&_⊢`Nat : ⊢ Γ ⋆ m →
             b ¿ Γ ∁ →
             Bool.T (opₘ m Natₘ) →
             ---------------------------
             b ¿ Γ ⊢ `Nat ⦂ `Univ i ⋆ m

  `zero    : ⊢ Γ ⋆ m →
             b ¿ Γ ∁ →
             Bool.T (opₘ m Natₘ) →
             -------------------------
             b ¿ Γ ⊢ `zero ⦂ `Nat ⋆ m

  `suc     : b ¿ Γ ⊢ s ⦂ `Nat ⋆ m →
             --------------------------
             b ¿ Γ ⊢ `suc s ⦂ `Nat ⋆ m

  _⊢`rec   : b ¿ Γ ≅ Γ₀ ⋈ Γ₁ →
             Γ `∙ `⟨ `Nat ⋆ m / `⁺ ⟩ ⊢ᵀ S ⦂ `Univ i ⋆ m →
             b ¿ Γ₀ ⊢ t ⦂ `Nat ⋆ m →
             b ¿ Γ₁ ⊢ u ⦂ S `⟦| `zero ⟧ ⋆ m →
             b ¿ `⁺ ⋆ m ≅ a₀ a⋈ a₁ →
             b ¿ Γ₁ `∙ `⟨ `Nat ⋆ m / a₀ ⟩ `∙ `⟨ S ⋆ m / a₁ ⟩ ⊢ v ⦂ S `⟦ `rec-suc-subst ⟧ ⋆ m →
             ---------------------------------------------------------------------------------
             b ¿ Γ ⊢ `rec S t u v ⦂ S `⟦| t ⟧ ⋆ m

  -- Lambda-calculus
  --
  _⊢`Π_⊸_ : b ¿ Γ ≅ Γ₀ ⋈ Γ₁ →
            b ¿ Γ₀ ⊢ S ⦂ `Univ i ⋆ m →
            b ¿ Γ₁ `∙ `⟨ S ⋆ m / `⁺ ⟩ ⊢ T ⦂ `Univ i ⋆ m →
            ------------------------------------------------
            b ¿ Γ ⊢ `Π S ⊸ T ⦂ `Univ i ⋆ m

  `λ_⊸_   : Γ ⊢ᵀ S ⦂ `Univ i ⋆ m →
            b ¿ Γ `∙ `⟨ S ⋆ m / `⁺ ⟩ ⊢ t ⦂ T ⋆ m →
            ------------------------------------------------
            b ¿ Γ ⊢ `λ S ⊸ t ⦂ `Π S ⊸ T ⋆ m

  _⊢_`$_  : b ¿ Γ ≅ Γ₀ ⋈ Γ₁ →
            b ¿ Γ₀ ⊢ s ⦂ `Π T ⊸ S ⋆ m →
            b ¿ Γ₁ ⊢ t ⦂ T ⋆ m →
            ------------------------------------------------
            b ¿ Γ ⊢ s `$ t ⦂ S `⟦| t ⟧ ⋆ m

  _⊢`#_   : ⊢ Γ ⋆ m →
            b ¿ x ⦂ S ⋆ m ∈ Γ →
            ---------------------
            b ¿ Γ ⊢ `# x ⦂ S ⋆ m

  -- Explicit substitution
  --
  `sub : b ¿ Δ ⊢ s ⦂ S ⋆ m →
         b ¿ Γ s⊢ σ ⦂ Δ ⋆ m →
         --------------------------------
         b ¿ Γ ⊢ s `⟦ σ ⟧ ⦂ S `⟦ σ ⟧ ⋆ m

  -- Conversion
  --
  `conv : b ¿ Γ ⊢ t ⦂ T ⋆ m →
          Γ ⊢ᵀ T ≈[ m ≤] S ⦂ `Univ i ⋆ m →
          ---------------------------------
          b ¿ Γ ⊢ t ⦂ S ⋆ m

data _¿_⊢_≈[_≤]_⦂_⋆_ where
  -- (Cumulative) Universe
  --
  _⊢`Univ⟦_⟧  : b ¿ Γ ∁ →
                b ¿ Δ s⊢ σ ⦂ Γ ⋆ m →
                -----------------------------------------------------------
                b ¿ Γ ⊢ `Univ i `⟦ σ ⟧ ≈[ n ≤] `Univ i ⦂ `Univ (suc i) ⋆ m

  `cumul      : b ¿ Γ ⊢ S ≈[ n ≤] T ⦂ `Univ i ⋆ m →
                ----------------------------------------
                b ¿ Γ ⊢ S ≈[ n ≤] T ⦂ `Univ (suc i) ⋆ m

  -- Conversion
  --
  `conv : b ¿ Γ ⊢ t ≈[ n ≤] t′ ⦂ T ⋆ m →
          Γ ⊢ᵀ T ≈[ n ≤] T′ ⦂ `Univ i ⋆ m →
          ----------------------------------
          b ¿ Γ ⊢ t ≈[ n ≤] t′ ⦂ T′ ⋆ m

  -- PER
  --
  `sym   : b ¿ Γ ⊢ t ≈[ n ≤] t′ ⦂ T ⋆ m →
           -------------------------------
           b ¿ Γ ⊢ t′ ≈[ n ≤] t ⦂ T ⋆ m

  `trans : b ¿ Γ ⊢ t ≈[ n ≤] t′ ⦂ T ⋆ m →
           b ¿ Γ ⊢ t′ ≈[ n ≤] t″ ⦂ T ⋆ m →
           --------------------------------
           b ¿ Γ ⊢ t ≈[ n ≤] t″ ⦂ T ⋆ m

data _¿_s⊢_⦂_⋆_ where
  -- Substitution Constructors
  --
  `id            : ⊢ Γ ⋆ m →
                   ---------------------
                   b ¿ Γ s⊢ `id ⦂ Γ ⋆ m

  `wk            : ⊢ Γ `∙ e ⋆ m →
                   b ¿ e e∁ →
                   --------------------------
                   b ¿ Γ `∙ e s⊢ `wk ⦂ Γ ⋆ m

  _&_⊢_`,_⦂_⊢_/_ : b ¿ Γ ≅ Γ₀ ⋈ Γ₁ →
                   b ¿ Γ₁ ∥[ h ≤]≅ Γ′₁ →
                   b ¿ Γ₀ s⊢ σ ⦂ Δ ⋆ m →
                   b ¿ Γ′₁ ⊢ t ⦂ T `⟦ σ ⟧ ⋆ h →
                   Δ ∥[ h ≤]ᵀ≅ Δ′ →
                   Δ′ ⊢ᵀ T ⦂ `Univ i ⋆ h →
                   false ¿ a is-useable →
                   ------------------------------------------
                   b ¿ Γ s⊢ σ `, t ⦂ Δ `∙ `⟨ T ⋆ h / a ⟩ ⋆ m

  _`,Ø⦂_⊢_       : b ¿ Γ s⊢ σ ⦂ Δ ⋆ m →
                   Δ ∥[ h ≤]ᵀ≅ Δ′ →
                   Δ′ ⊢ᵀ T ⦂ `Univ i ⋆ h →
                   ------------------------------------------
                   b ¿ Γ s⊢ σ `,Ø ⦂ Δ `∙ `⟨ T ⋆ h / `Ø ⟩ ⋆ m

  _`∘_           : b ¿ Δ s⊢ σ ⦂ Ψ ⋆ m →
                   b ¿ Γ s⊢ τ ⦂ Δ ⋆ m →
                   ------------------------
                   b ¿ Γ s⊢ σ `∘ τ ⦂ Ψ ⋆ m

  -- Conversion
  --
  `conv          : b ¿ Γ s⊢ σ ⦂ Δ ⋆ m →
                   ⊢ Δ ≈[ n ≤] Δ′ ⋆ m →
                   ---------------------
                   b ¿ Γ s⊢ σ ⦂ Δ′ ⋆ m

data _¿_s⊢_≈[_≤]_⦂_⋆_ where
  -- Conversion
  --
  `conv : b ¿ Γ s⊢ σ ≈[ n ≤] σ′ ⦂ Δ ⋆ m →
          ⊢ Δ ≈[ n ≤] Δ′ ⋆ m →
          --------------------------------
          b ¿ Γ s⊢ σ ≈[ n ≤] σ′ ⦂ Δ′ ⋆ m

  -- PER
  --
  `sym   : b ¿ Γ s⊢ σ ≈[ n ≤] σ′ ⦂ Δ ⋆ m →
           -------------------------------
           b ¿ Γ s⊢ σ′ ≈[ n ≤] σ ⦂ Δ ⋆ m

  `trans : b ¿ Γ s⊢ σ ≈[ n ≤] σ′ ⦂ Δ ⋆ m →
           b ¿ Γ s⊢ σ′ ≈[ n ≤] σ″ ⦂ Δ ⋆ m →
           --------------------------------
           b ¿ Γ s⊢ σ ≈[ n ≤] σ″ ⦂ Δ ⋆ m
