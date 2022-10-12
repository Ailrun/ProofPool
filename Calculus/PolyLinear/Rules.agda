module Calculus.PolyLinear.Rules where

open import Calculus.PolyLinear.Syntax
open import Data.List
open import Data.Nat
open import Data.Product
open import Relation.Binary.PropositionalEquality

infix 4 _⦂_𝕂∈_
infix 4 _⦂_𝕋∈_/_

data _⦂_𝕂∈_ : ℕ → 𝕂 → ℂ → Set where
  here   : K ≡ K′ →
           ----------------
           0 ⦂ K 𝕂∈ K′ 𝕂∷ Γ

  there𝕂 : x ⦂ K 𝕂∈ Γ →
           ---------------------
           suc x ⦂ K 𝕂∈ K′ 𝕂∷ Γ

  there𝕋 : x ⦂ K 𝕂∈ Γ →
           --------------------------
           x ⦂ K 𝕂∈ (T , u) 𝕋∷ Γ

data _⦂_𝕋∈_/_ : ℕ → 𝕋 → ℂ → ℂ → Set where
  here   : .{prf : useable𝕌 u} →
           T ≡ T′ →
           --------------------------------------------
           0 ⦂ T 𝕋∈ (T′ , u) 𝕋∷ Γ / (T′ , inc𝕌 u prf) 𝕋∷ Γ

  there𝕋 : x ⦂ T 𝕋∈ Γ / Γ′ →
           --------------------------------------------
           suc x ⦂ T 𝕋∈ (T′ , u) 𝕋∷ Γ / (T′ , u) 𝕋∷ Γ′

  there𝕂 : x ⦂ T 𝕋∈ Γ / Γ′ →
           -------------------------
           x ⦂ T 𝕋∈ K 𝕂∷ Γ / K 𝕂∷ Γ′

infix 4 ℂ⊢_
infix 4 _𝕋⊢_⦂_

data ℂ⊢_ : ℂ → Set
data _𝕋⊢_⦂_ : ℂ → 𝕋 → 𝕂 → Set

data ℂ⊢_ where
  []   : ------
         ℂ⊢ []

  ⋆𝕂∷_ : ℂ⊢ Γ →
         ----------
         ℂ⊢ K 𝕂∷ Γ

  _𝕋∷_ : Γ 𝕋⊢ T ⦂ Tyₗ →
         ℂ⊢ Γ →
         ----------------
         ℂ⊢ (T , u) 𝕋∷ Γ

data _𝕋⊢_⦂_ where
  tvarₗ : x ⦂ K 𝕂∈ Γ →
          -----------------
          Γ 𝕋⊢ tvarₗ x ⦂ K

  _⊸ₗ_  : Γ 𝕋⊢ T ⦂ Tyₗ →
          Γ 𝕋⊢ U ⦂ Tyₗ →
          ------------------
          Γ 𝕋⊢ T ⊸ₗ U ⦂ Tyₗ

  !ₗ_   : Γ 𝕋⊢ T ⦂ Tyₗ →
          ----------------
          Γ 𝕋⊢ !ₗ T ⦂ Tyₗ

  ∀ₗ⋆∙_ : K 𝕂∷ Γ 𝕋⊢ T ⦂ Tyₗ →
          --------------------
          Γ 𝕋⊢ ∀ₗ K ∙ T ⦂ Tyₗ

infix 4 _𝕄⊢_⦂_/_

data _𝕄⊢_⦂_/_ : ℂ → 𝕄 → 𝕋 → ℂ → Set where
  varₗ           : x ⦂ T 𝕋∈ Γ / Γ′ →
                   ---------------------
                   Γ 𝕄⊢ varₗ x ⦂ T / Γ′

  λₗ_∘_          : Γ 𝕋⊢ T ⦂ Tyₗ →
                   (T , 0/1ₗ) 𝕋∷ Γ 𝕄⊢ M ⦂ U / (T , 1/1ₗ) 𝕋∷ Γ′ →
                   ----------------------------------------------
                   Γ 𝕄⊢ λₗ T ∘ M ⦂ T ⊸ₗ U / Γ′

  _$ₗ∘_          : Γ 𝕄⊢ M ⦂ T ⊸ₗ U / Γ′ →
                   Γ′ 𝕄⊢ N ⦂ T / Γ″ →
                   -----------------------
                   Γ 𝕄⊢ M $ₗ∘ N ⦂ U / Γ″

  bangₗ          : Γ 𝕄⊢ M ⦂ T / Γ →
                   -------------------------
                   Γ 𝕄⊢ bangₗ M ⦂ !ₗ T / Γ

  let-bangₗ_inₗ_ : Γ 𝕄⊢ M ⦂ !ₗ T / Γ′ →
                   (T , ∞ₗ) 𝕋∷ Γ′ 𝕄⊢ N ⦂ U / (T , ∞ₗ) 𝕋∷ Γ″ →
                   -------------------------------------------
                   Γ 𝕄⊢ let-bangₗ M inₗ N ⦂ U / Γ″

  Λₗ⋆∙_          : K 𝕂∷ Γ 𝕄⊢ M ⦂ T / K 𝕂∷ Γ′ →
                   ------------------------------
                   Γ 𝕄⊢ Λₗ K ∙ M ⦂ ∀ₗ K ∙ T / Γ′

  _$$ₗ∙_         : Γ 𝕄⊢ M ⦂ ∀ₗ K ∙ U / Γ′ →
                   Γ′ 𝕋⊢ T ⦂ K →
                   -------------------------
                   Γ 𝕄⊢ M $$ₗ∙ T ⦂ U / Γ′
