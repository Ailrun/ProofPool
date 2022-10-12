module Calculus.PolyLinear.Syntax where

open import Data.Empty
open import Data.List
open import Data.Nat
open import Data.Product
open import Data.Unit
open import Relation.Nullary

-- Kind
data 𝕂 : Set where
  Tyₗ : 𝕂

infixr 30 tvarₗ
infixr 30 !ₗ_
infixr 29 _⊸ₗ_
infixr 28 ∀ₗ_∙_

-- Type
data 𝕋 : Set where
  tvarₗ : ℕ → 𝕋
  _⊸ₗ_  : 𝕋 → 𝕋 → 𝕋
  !ₗ_   : 𝕋 → 𝕋
  ∀ₗ_∙_ : 𝕂 → 𝕋 → 𝕋

infixr 30 varₗ
infixr 30 bangₗ
infixl 29 _$ₗ∘_
infixl 29 _$$ₗ∙_
infixr 28 let-bangₗ_inₗ_
infixr 27 λₗ_∘_
infixr 27 Λₗ_∙_

-- Term
data 𝕄 : Set where
  varₗ           : ℕ → 𝕄
  λₗ_∘_          : 𝕋 → 𝕄 → 𝕄
  _$ₗ∘_          : 𝕄 → 𝕄 → 𝕄
  bangₗ          : 𝕄 → 𝕄
  let-bangₗ_inₗ_ : 𝕄 → 𝕄 → 𝕄
  Λₗ_∙_          : 𝕂 → 𝕄 → 𝕄
  _$$ₗ∙_         : 𝕄 → 𝕋 → 𝕄

-- Usage
data 𝕌 : Set where
  ∞ₗ   : 𝕌
  0/1ₗ : 𝕌
  1/1ₗ : 𝕌

infixr 5 _𝕂∷_
infixr 5 _𝕋∷_

-- Context
data ℂ : Set where
  []   : ℂ
  _𝕂∷_ : 𝕂 → ℂ → ℂ
  _𝕋∷_ : 𝕋 × 𝕌 → ℂ → ℂ

-- Context Skeleton
data ℂ⁻ : Set where
  []   : ℂ⁻
  _𝕂∷_ : 𝕂 → ℂ⁻ → ℂ⁻
  _𝕋∷_ : 𝕋 → ℂ⁻ → ℂ⁻

variable
  x x′ x″ x₀ x₁ x₂ : ℕ
  y y′ y″ y₀ y₁ y₂ : ℕ
  z z′ z″ z₀ z₁ z₂ : ℕ

  K K′ K″ K₀ K₁ K₂ : 𝕂

  T T′ T″ T₀ T₁ T₂ : 𝕋
  U U′ U″ U₀ U₁ U₂ : 𝕋
  V V′ V″ V₀ V₁ V₂ : 𝕋

  M M′ M″ M₀ M₁ M₂ : 𝕄
  N N′ N″ N₀ N₁ N₂ : 𝕄
  O O′ O″ O₀ O₁ O₂ : 𝕄
  P P′ P″ P₀ P₁ P₂ : 𝕄

  u u′ u″ u₀ u₁ u₂ : 𝕌

  Γ Γ′ Γ″ Γ₀ Γ₁ Γ₂ : ℂ
  Δ Δ′ Δ″ Δ₀ Δ₁ Δ₂ : ℂ
  Ψ Ψ′ Ψ″ Ψ₀ Ψ₁ Ψ₂ : ℂ

  Γ⁻ Γ⁻′ Γ⁻″ Γ⁻₀ Γ⁻₁ Γ⁻₂ : ℂ⁻
  Δ⁻ Δ⁻′ Δ⁻″ Δ⁻₀ Δ⁻₁ Δ⁻₂ : ℂ⁻
  Ψ⁻ Ψ⁻′ Ψ⁻″ Ψ⁻₀ Ψ⁻₁ Ψ⁻₂ : ℂ⁻

infixr 30 wkℕ∣ℕ_/↑_∣_
infixr 30 wk𝕋∣𝕋_/↑_∣_
infixr 30 wk𝕄∣𝕋_/↑_∣_
infixr 30 wk𝕄∣𝕄_/↑_∣_

wkℕ∣ℕ_/↑_∣_ : ℕ → ℕ → ℕ → ℕ
wkℕ∣ℕ n /↑ m ∣ x
  with x ≥? m
...  | no  _ = x
...  | yes _ = n + x

wk𝕋∣𝕋_/↑_∣_ : ℕ → ℕ → 𝕋 → 𝕋
wk𝕋∣𝕋 n /↑ m ∣ tvarₗ x    = tvarₗ (wkℕ∣ℕ n /↑ m ∣ x)
wk𝕋∣𝕋 n /↑ m ∣ (T ⊸ₗ U)   = wk𝕋∣𝕋 n /↑ m ∣ T ⊸ₗ wk𝕋∣𝕋 n /↑ m ∣ U
wk𝕋∣𝕋 n /↑ m ∣ (!ₗ T)     = !ₗ (wk𝕋∣𝕋 n /↑ m ∣ T)
wk𝕋∣𝕋 n /↑ m ∣ (∀ₗ K ∙ T) = ∀ₗ K ∙ wk𝕋∣𝕋 n /↑ suc m ∣ T

wk𝕄∣𝕋_/↑_∣_ : ℕ → ℕ → 𝕄 → 𝕄
wk𝕄∣𝕋 n /↑ m ∣ varₗ x              = varₗ x
wk𝕄∣𝕋 n /↑ m ∣ (λₗ T ∘ M)          = λₗ wk𝕋∣𝕋 n /↑ m ∣ T ∘ wk𝕄∣𝕋 n /↑ m ∣ M
wk𝕄∣𝕋 n /↑ m ∣ (M $ₗ∘ N)           = wk𝕄∣𝕋 n /↑ m ∣ M $ₗ∘ wk𝕄∣𝕋 n /↑ m ∣ N
wk𝕄∣𝕋 n /↑ m ∣ bangₗ M             = bangₗ (wk𝕄∣𝕋 n /↑ m ∣ M)
wk𝕄∣𝕋 n /↑ m ∣ (let-bangₗ M inₗ N) = let-bangₗ wk𝕄∣𝕋 n /↑ m ∣ M inₗ wk𝕄∣𝕋 n /↑ m ∣ N
wk𝕄∣𝕋 n /↑ m ∣ (Λₗ K ∙ M)          = Λₗ K ∙ wk𝕄∣𝕋 n /↑ suc m ∣ M
wk𝕄∣𝕋 n /↑ m ∣ (M $$ₗ∙ T)          = wk𝕄∣𝕋 n /↑ m ∣ M $$ₗ∙ wk𝕋∣𝕋 n /↑ m ∣ T

wk𝕄∣𝕄_/↑_∣_ : ℕ → ℕ → 𝕄 → 𝕄
wk𝕄∣𝕄 n /↑ m ∣ varₗ x              = varₗ (wkℕ∣ℕ n /↑ m ∣ x)
wk𝕄∣𝕄 n /↑ m ∣ (λₗ T ∘ M)          = λₗ T ∘ wk𝕄∣𝕄 n /↑ suc m ∣ M
wk𝕄∣𝕄 n /↑ m ∣ (M $ₗ∘ N)           = wk𝕄∣𝕄 n /↑ m ∣ M $ₗ∘ wk𝕄∣𝕄 n /↑ m ∣ N
wk𝕄∣𝕄 n /↑ m ∣ bangₗ M             = bangₗ (wk𝕄∣𝕄 n /↑ m ∣ M)
wk𝕄∣𝕄 n /↑ m ∣ (let-bangₗ M inₗ N) = let-bangₗ wk𝕄∣𝕄 n /↑ m ∣ M inₗ wk𝕄∣𝕄 n /↑ suc m ∣ N
wk𝕄∣𝕄 n /↑ m ∣ (Λₗ K ∙ M)          = Λₗ K ∙ wk𝕄∣𝕄 n /↑ m ∣ M
wk𝕄∣𝕄 n /↑ m ∣ (M $$ₗ∙ T)          = wk𝕄∣𝕄 n /↑ m ∣ M $$ₗ∙ T

λₗ_∙_ : 𝕋 → 𝕄 → 𝕄
λₗ T ∙ M = λₗ !ₗ T ∘ let-bangₗ varₗ 0 inₗ wk𝕄∣𝕄 1 /↑ 1 ∣ M

useable𝕌 : 𝕌 → Set
useable𝕌 ∞ₗ   = ⊤
useable𝕌 0/1ₗ = ⊤
useable𝕌 1/1ₗ = ⊥

inc𝕌 : (u : 𝕌) → .(useable𝕌 u) → 𝕌
inc𝕌 ∞ₗ   _ = ∞ₗ
inc𝕌 0/1ₗ _ = 1/1ₗ

extractℂ⁻ : ℂ → ℂ⁻
extractℂ⁻ []             = []
extractℂ⁻ (K       𝕂∷ Γ) = K 𝕂∷ extractℂ⁻ Γ
extractℂ⁻ ((T , _) 𝕋∷ Γ) = T 𝕋∷ extractℂ⁻ Γ
