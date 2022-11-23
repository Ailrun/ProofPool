module Calculus.LinearSide.Syntax where

open import Agda.Builtin.FromNat public
open import Data.Nat hiding (_/_)
import Data.Nat.Literals as ℕ
open import Data.Fin using (Fin)
import Data.Fin.Literals as Fin
open import Data.Fin.Substitution
open import Data.Unit hiding (_≟_)
open import Data.Vec using (Vec)
import Data.Vec as Vec

instance
  Numberℕ : Number ℕ
  Numberℕ = ℕ.number

  NumberFin : ∀ {n} → Number (Fin n)
  NumberFin {n} = Fin.number n

infixr 9 _⊸ₗ_

-- Type
data 𝕋 : Set where
  baseₗ : 𝕋
  _⊸ₗ_  : 𝕋 → 𝕋 → 𝕋
  !ₗ    : 𝕋 → 𝕋

infixr 9 λₗ_∘ₗ_
infixl 9 _$∘ₗ_
infixr 9 let-bangₗ_inₗ_

-- Term
data 𝕄 (n : ℕ) : Set where
  varₗ           : Fin n → 𝕄 n
  λₗ_∘ₗ_         : 𝕋 → 𝕄 (suc n) → 𝕄 n
  _$∘ₗ_          : 𝕄 n → 𝕄 n → 𝕄 n
  bangₗ          : 𝕄 n → 𝕄 n
  let-bangₗ_inₗ_ : 𝕄 n → 𝕄 (suc n) → 𝕄 n

-- Context
ℂ = Vec 𝕋

-- Substitution
𝕊 = Sub 𝕄

variable
  n n′ n″ n‴ n₀ n₁ n₂ n₃ : ℕ
  m m′ m″ m‴ m₀ m₁ m₂ m₃ : ℕ
  l l′ l″ l‴ l₀ l₁ l₂ l₃ : ℕ

  x x′ x″ x‴ x₀ x₁ x₂ x₃ : Fin n
  y y′ y″ y‴ y₀ y₁ y₂ y₃ : Fin n
  z z′ z″ z‴ z₀ z₁ z₂ z₃ : Fin n

  T T′ T″ T‴ T₀ T₁ T₂ T₃ : 𝕋
  U U′ U″ U‴ U₀ U₁ U₂ U₃ : 𝕋
  V V′ V″ V‴ V₀ V₁ V₂ V₃ : 𝕋

  M M′ M″ M‴ M₀ M₁ M₂ M₃ : 𝕄 n
  N N′ N″ N‴ N₀ N₁ N₂ N₃ : 𝕄 n
  O O′ O″ O‴ O₀ O₁ O₂ O₃ : 𝕄 n
  P P′ P″ P‴ P₀ P₁ P₂ P₃ : 𝕄 n

  Γ Γ′ Γ″ Γ‴ Γ₀ Γ₁ Γ₂ Γ₃ : ℂ n
  Δ Δ′ Δ″ Δ‴ Δ₀ Δ₁ Δ₂ Δ₃ : ℂ n′
  Ψ Ψ′ Ψ″ Ψ‴ Ψ₀ Ψ₁ Ψ₂ Ψ₃ : ℂ n″

  σ σ′ σ″ σ‴ σ₀ σ₁ σ₂ σ₃ : 𝕊 n n′
  τ τ′ τ″ τ‴ τ₀ τ₁ τ₂ τ₃ : 𝕊 n n′

  ρ ρ′ ρ″ ρ‴ ρ₀ ρ₁ ρ₂ ρ₃ : Sub Fin n n′

pattern ⊤ₗ = baseₗ ⊸ₗ baseₗ
pattern ttₗ = λₗ baseₗ ∘ₗ varₗ Fin.zero

record HasLength (S : Set) : Set where
  inductive
  field
    len : S → ℕ

open HasLength {{...}} public

{-# DISPLAY HasLength.len s = len s #-}

instance
  HasLengthℂ : HasLength (ℂ n)
  len {{HasLengthℂ}} = Vec.length

  HasLength𝕊 : HasLength (𝕊 n n′)
  len {{HasLength𝕊}} = Vec.length
