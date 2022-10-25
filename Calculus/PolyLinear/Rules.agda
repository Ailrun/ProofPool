module Calculus.PolyLinear.Rules where

open import Calculus.PolyLinear.Syntax
open import Data.List
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality

infix 4 _⦂_𝕂∈_
infix 4 _⦂_𝕋∈_/_

data _⦂_𝕂∈_ : ℕ → 𝕂 → ℂ → Set where
  here  : K ≡ K′ →
          -------------------
          0 ⦂ K 𝕂∈ K′ /𝕂 ∷ Γ

  there : x ⦂ K 𝕂∈ Γ →
          -------------------
          suc x ⦂ K 𝕂∈ E ∷ Γ

data _⦂_𝕋∈_/_ : ℕ → 𝕋 → ℂ → ℂ → Set where
  here  : .{prf : useable𝕌 u} →
          T ≡ T′ →
          ----------------------------------------------------------------
          0 ⦂ wk∣ 1 ↑ 0 ∣ T 𝕋∈ (T′ , u) /𝕋 ∷ Γ / (T′ , inc𝕌 u prf) /𝕋 ∷ Γ

  there : x ⦂ T 𝕋∈ Γ / Γ′ →
          ----------------------------------------
          suc x ⦂ wk∣ 1 ↑ 0 ∣ T 𝕋∈ E ∷ Γ / E ∷ Γ′

infix 4 ℂ⊢_
infix 4 _ℂ𝔼⊢_
infix 4 _𝕋⊢_⦂_

data ℂ⊢_ : ℂ → Set
data _ℂ𝔼⊢_ : ℂ → ℂ𝔼 → Set
data _𝕋⊢_⦂_ : ℂ → 𝕋 → 𝕂 → Set

data ℂ⊢_ where
  []  : ------
        ℂ⊢ []

  _∷_ : Γ ℂ𝔼⊢ E →
        ℂ⊢ Γ →
        ---------
        ℂ⊢ E ∷ Γ

data _ℂ𝔼⊢_ where
  ⋆/𝕂 : Γ ℂ𝔼⊢ K /𝕂

  _/𝕋 : Γ 𝕋⊢ T ⦂ Tyₗ →
        -----------------
        Γ ℂ𝔼⊢ (T , u) /𝕋

data _𝕋⊢_⦂_ where
  tvarₗ : ℂ⊢ Γ →
          x ⦂ K 𝕂∈ Γ →
          -----------------
          Γ 𝕋⊢ tvarₗ x ⦂ K

  _⊸ₗ_  : Γ 𝕋⊢ T ⦂ Tyₗ →
          Γ 𝕋⊢ U ⦂ Tyₗ →
          ------------------
          Γ 𝕋⊢ T ⊸ₗ U ⦂ Tyₗ

  !ₗ_   : Γ 𝕋⊢ T ⦂ Tyₗ →
          ----------------
          Γ 𝕋⊢ !ₗ T ⦂ Tyₗ

  ∀ₗ⋆∙_ : K /𝕂 ∷ Γ 𝕋⊢ T ⦂ Tyₗ →
          ----------------------
          Γ 𝕋⊢ ∀ₗ K ∙ T ⦂ Tyₗ

infix 4 _𝕄⊢_⦂_/_

data _𝕄⊢_⦂_/_ : ℂ → 𝕄 → 𝕋 → ℂ → Set where
  varₗ           : x ⦂ T 𝕋∈ Γ / Γ′ →
                   ---------------------
                   Γ 𝕄⊢ varₗ x ⦂ T / Γ′

  λₗ_∘_          : Γ 𝕋⊢ T ⦂ Tyₗ →
                   (T , 0/1ₗ) /𝕋 ∷ Γ 𝕄⊢ M ⦂ wk∣ 1 ↑ 0 ∣ U / (T , 1/1ₗ) /𝕋 ∷ Γ′ →
                   --------------------------------------------------------------
                   Γ 𝕄⊢ λₗ T ∘ M ⦂ T ⊸ₗ U / Γ′

  _$ₗ∘_          : Γ 𝕄⊢ M ⦂ T ⊸ₗ U / Γ′ →
                   Γ′ 𝕄⊢ N ⦂ T / Γ″ →
                   -----------------------
                   Γ 𝕄⊢ M $ₗ∘ N ⦂ U / Γ″

  bangₗ          : Γ 𝕄⊢ M ⦂ T / Γ →
                   -------------------------
                   Γ 𝕄⊢ bangₗ M ⦂ !ₗ T / Γ

  let-bangₗ_inₗ_ : Γ 𝕄⊢ M ⦂ !ₗ T / Γ′ →
                   (T , ∞ₗ) /𝕋 ∷ Γ′ 𝕄⊢ N ⦂ wk∣ 1 ↑ 0 ∣ U / (T , ∞ₗ) /𝕋 ∷ Γ″ →
                   -------------------------------------------------------
                   Γ 𝕄⊢ let-bangₗ M inₗ N ⦂ U / Γ″

  Λₗ⋆∙_          : K /𝕂 ∷ Γ 𝕄⊢ M ⦂ T / K /𝕂 ∷ Γ′ →
                   ------------------------------
                   Γ 𝕄⊢ Λₗ K ∙ M ⦂ ∀ₗ K ∙ T / Γ′

  _$$ₗ∙_         : Γ 𝕄⊢ M ⦂ ∀ₗ K ∙ U / Γ′ →
                   Γ′ 𝕋⊢ T ⦂ K →
                   ----------------------------------
                   Γ 𝕄⊢ M $$ₗ∙ T ⦂ s∣ T /𝕋 / 0 ∣ U / Γ′

infix 4 _≤𝕌_
infix 4 _≤𝕌ℂ𝔼_
infix 4 _≤𝕌ℂ_

data _≤𝕌_ : 𝕌 → 𝕌 → Set where
  refl      : u ≤𝕌 u
  0/1ₗ≤1/1ₗ : 0/1ₗ ≤𝕌 1/1ₗ

data _≤𝕌ℂ𝔼_ : ℂ𝔼 → ℂ𝔼 → Set where
  refl/𝕂 : K /𝕂 ≤𝕌ℂ𝔼 K /𝕂
  _/𝕋    : u ≤𝕌 u′ →
           ----------------------------
           (T , u) /𝕋 ≤𝕌ℂ𝔼 (T , u′) /𝕋

data _≤𝕌ℂ_ : ℂ → ℂ → Set where
  []  : [] ≤𝕌ℂ []
  _∷_ : E ≤𝕌ℂ𝔼 E′ →
        Γ ≤𝕌ℂ Γ′ →
        ------------------
        E ∷ Γ ≤𝕌ℂ E′ ∷ Γ′
