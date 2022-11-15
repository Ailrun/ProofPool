module Calculus.PolyLinear.Syntax where

open import Data.Empty
open import Data.List
open import Data.Nat
open import Data.Product
open import Data.Unit hiding (_≟_)
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
  0/1ₗ : 𝕌
  1/1ₗ : 𝕌
  ∞ₗ   : 𝕌

infix 6 _/𝕂
infix 6 _/𝕋

data ℂ𝔼 : Set where
  _/𝕂 : 𝕂 → ℂ𝔼
  _/𝕋 : 𝕋 × 𝕌 → ℂ𝔼

data ℂ𝔼⁻ : Set where
  _/𝕂 : 𝕂 → ℂ𝔼⁻
  _/𝕋 : 𝕋 → ℂ𝔼⁻

-- Context
ℂ  = List ℂ𝔼
-- Context Skeleton
ℂ⁻ = List ℂ𝔼⁻

data 𝕊𝔼 : Set where
  _/𝕋 : 𝕋 → 𝕊𝔼
  _/𝕄 : 𝕄 → 𝕊𝔼

-- Substitution
𝕊 = List 𝕊𝔼

variable
  x x′ x″ x‴ x₀ x₁ x₂ x₃ : ℕ
  y y′ y″ y‴ y₀ y₁ y₂ y₃ : ℕ
  z z′ z″ z‴ z₀ z₁ z₂ z₃ : ℕ

  K K′ K″ K‴ K₀ K₁ K₂ K₃ : 𝕂

  T T′ T″ T‴ T₀ T₁ T₂ T₃ : 𝕋
  U U′ U″ U‴ U₀ U₁ U₂ U₃ : 𝕋
  V V′ V″ V‴ V₀ V₁ V₂ V₃ : 𝕋

  M M′ M″ M‴ M₀ M₁ M₂ M₃ : 𝕄
  N N′ N″ N‴ N₀ N₁ N₂ N₃ : 𝕄
  O O′ O″ O‴ O₀ O₁ O₂ O₃ : 𝕄
  P P′ P″ P‴ P₀ P₁ P₂ P₃ : 𝕄

  u u′ u″ u‴ u₀ u₁ u₂ u₃ : 𝕌

  Γ Γ′ Γ″ Γ‴ Γ₀ Γ₁ Γ₂ Γ₃ : ℂ
  Δ Δ′ Δ″ Δ‴ Δ₀ Δ₁ Δ₂ Δ₃ : ℂ
  Ψ Ψ′ Ψ″ Ψ‴ Ψ₀ Ψ₁ Ψ₂ Ψ₃ : ℂ

  E E′ E″ E‴ E₀ E₁ E₂ E₃ : ℂ𝔼

  Γ⁻ Γ⁻′ Γ⁻″ Γ⁻‴ Γ⁻₀ Γ⁻₁ Γ⁻₂ Γ⁻₃ : ℂ⁻
  Δ⁻ Δ⁻′ Δ⁻″ Δ⁻‴ Δ⁻₀ Δ⁻₁ Δ⁻₂ Δ⁻₃ : ℂ⁻
  Ψ⁻ Ψ⁻′ Ψ⁻″ Ψ⁻‴ Ψ⁻₀ Ψ⁻₁ Ψ⁻₂ Ψ⁻₃ : ℂ⁻

  E⁻ E⁻′ E⁻″ E⁻‴ E⁻₀ E⁻₁ E⁻₂ E⁻₃ : ℂ𝔼⁻

  s s′ s″ s‴ s₀ s₁ s₂ s₃ : 𝕊𝔼

  σ σ′ σ″ σ‴ σ₀ σ₁ σ₂ σ₃ : 𝕊
  τ τ′ τ″ τ‴ τ₀ τ₁ τ₂ τ₃ : 𝕊

pattern ⊤ₗ = ∀ₗ Tyₗ ∙ tvarₗ 0 ⊸ₗ tvarₗ 0
pattern ttₗ = Λₗ Tyₗ ∙ λₗ tvarₗ 0 ∘ varₗ 0

useable𝕌 : 𝕌 → Set
useable𝕌 0/1ₗ = ⊤
useable𝕌 1/1ₗ = ⊥
useable𝕌 ∞ₗ   = ⊤

inc𝕌 : (u : 𝕌) → .(useable𝕌 u) → 𝕌
inc𝕌 0/1ₗ _ = 1/1ₗ
inc𝕌 ∞ₗ   _ = ∞ₗ

extractℂ⁻ : ℂ → ℂ⁻
extractℂ⁻ []             = []
extractℂ⁻ (K       /𝕂 ∷ Γ) = K /𝕂 ∷ extractℂ⁻ Γ
extractℂ⁻ ((T , _) /𝕋 ∷ Γ) = T /𝕋 ∷ extractℂ⁻ Γ

record HasLength (S : Set) : Set where
  inductive
  field
    len : S → ℕ

open HasLength {{...}} public

{-# DISPLAY HasLength.len s = len s #-}

instance
  HasLengthℂ : HasLength ℂ
  len {{HasLengthℂ}} = length

  HasLengthℂ⁻ : HasLength ℂ⁻
  len {{HasLengthℂ⁻}} = length

  HasLength𝕊 : HasLength 𝕊
  len {{HasLength𝕊}} = length

_𝕌×𝕌_ : 𝕌 → 𝕌 → 𝕌
u    𝕌×𝕌 0/1ₗ = 0/1ₗ
u    𝕌×𝕌 1/1ₗ = u
0/1ₗ 𝕌×𝕌 ∞ₗ   = 0/1ₗ
1/1ₗ 𝕌×𝕌 ∞ₗ   = ∞ₗ
∞ₗ   𝕌×𝕌 ∞ₗ   = ∞ₗ

_ℂ×𝕌_ : ℂ → 𝕌 → ℂ
[]             ℂ×𝕌 u′ = []
(K       /𝕂 ∷ Γ) ℂ×𝕌 u′ = K /𝕂 ∷ (Γ ℂ×𝕌 u′)
((T , u) /𝕋 ∷ Γ) ℂ×𝕌 u′ = (T , u 𝕌×𝕌 u′) /𝕋 ∷ (Γ ℂ×𝕌 u′)

infixr 30 wkℕ∣_↑_∣_
infixr 30 wk𝕂∣_↑_∣_
infixr 30 wk𝕋∣_↑_∣_
infixr 30 wkℂ𝔼∣_↑_∣_
infixr 30 wkℂ𝔼⁻∣_↑_∣_
infixr 30 wkℂ∣_↑_∣_
infixr 30 wkℂ⁻∣_↑_∣_
infixr 30 wk𝕄∣_↑_∣_
infixr 30 wk𝕊𝔼∣_↑_∣_
infixr 30 wk𝕊∣_↑_∣_

wkℕ∣_↑_∣_ : ℕ → ℕ → ℕ → ℕ
wkℕ∣ n ↑ x ∣ y
  with y ≥? x
...  | no  _ = y
...  | yes _ = n + y

wk𝕂∣_↑_∣_ : ℕ → ℕ → 𝕂 → 𝕂
wk𝕂∣ n ↑ x ∣ Tyₗ = Tyₗ

wk𝕋∣_↑_∣_ : ℕ → ℕ → 𝕋 → 𝕋
wk𝕋∣ n ↑ x ∣ tvarₗ y    = tvarₗ (wkℕ∣ n ↑ x ∣ y)
wk𝕋∣ n ↑ x ∣ (T ⊸ₗ U)   = wk𝕋∣ n ↑ x ∣ T ⊸ₗ wk𝕋∣ n ↑ x ∣ U
wk𝕋∣ n ↑ x ∣ (!ₗ T)     = !ₗ (wk𝕋∣ n ↑ x ∣ T)
wk𝕋∣ n ↑ x ∣ (∀ₗ K ∙ T) = ∀ₗ wk𝕂∣ n ↑ x ∣ K ∙ wk𝕋∣ n ↑ suc x ∣ T

wkℂ𝔼∣_↑_∣_ : ℕ → ℕ → ℂ𝔼 → ℂ𝔼
wkℂ𝔼∣ n ↑ x ∣ (K /𝕂)       = wk𝕂∣ n ↑ x ∣ K /𝕂
wkℂ𝔼∣ n ↑ x ∣ ((T , u) /𝕋) = (wk𝕋∣ n ↑ x ∣ T , u) /𝕋

wkℂ𝔼⁻∣_↑_∣_ : ℕ → ℕ → ℂ𝔼⁻ → ℂ𝔼⁻
wkℂ𝔼⁻∣ n ↑ x ∣ (K /𝕂) = wk𝕂∣ n ↑ x ∣ K /𝕂
wkℂ𝔼⁻∣ n ↑ x ∣ (T /𝕋) = wk𝕋∣ n ↑ x ∣ T /𝕋

wkℂ∣_↑_∣_ : ℕ → ℕ → ℂ → ℂ
wkℂ∣ n ↑ zero  ∣ Γ       = Γ
wkℂ∣ n ↑ suc x ∣ []      = []
wkℂ∣ n ↑ suc x ∣ (E ∷ Γ) = wkℂ𝔼∣ n ↑ x ∣ E ∷ wkℂ∣ n ↑ x ∣ Γ

wkℂ⁻∣_↑_∣_ : ℕ → ℕ → ℂ⁻ → ℂ⁻
wkℂ⁻∣ n ↑ zero  ∣ Γ       = Γ
wkℂ⁻∣ n ↑ suc x ∣ []      = []
wkℂ⁻∣ n ↑ suc x ∣ (E ∷ Γ) = wkℂ𝔼⁻∣ n ↑ x ∣ E ∷ wkℂ⁻∣ n ↑ x ∣ Γ

wk𝕄∣_↑_∣_ : ℕ → ℕ → 𝕄 → 𝕄
wk𝕄∣ n ↑ x ∣ varₗ y              = varₗ (wkℕ∣ n ↑ x ∣ y)
wk𝕄∣ n ↑ x ∣ (λₗ T ∘ M)          = λₗ wk𝕋∣ n ↑ x ∣ T ∘ wk𝕄∣ n ↑ suc x ∣ M
wk𝕄∣ n ↑ x ∣ (M $ₗ∘ N)           = wk𝕄∣ n ↑ x ∣ M $ₗ∘ wk𝕄∣ n ↑ x ∣ N
wk𝕄∣ n ↑ x ∣ bangₗ M             = bangₗ (wk𝕄∣ n ↑ x ∣ M)
wk𝕄∣ n ↑ x ∣ (let-bangₗ M inₗ N) = let-bangₗ wk𝕄∣ n ↑ x ∣ M inₗ wk𝕄∣ n ↑ suc x ∣ N
wk𝕄∣ n ↑ x ∣ (Λₗ K ∙ M)          = Λₗ wk𝕂∣ n ↑ x ∣ K ∙ wk𝕄∣ n ↑ suc x ∣ M
wk𝕄∣ n ↑ x ∣ (M $$ₗ∙ T)          = wk𝕄∣ n ↑ x ∣ M $$ₗ∙ wk𝕋∣ n ↑ x ∣ T

wk𝕊𝔼∣_↑_∣_ : ℕ → ℕ → 𝕊𝔼 → 𝕊𝔼
wk𝕊𝔼∣ n ↑ x ∣ (T /𝕋) = wk𝕋∣ n ↑ x ∣ T /𝕋
wk𝕊𝔼∣ n ↑ x ∣ (M /𝕄) = wk𝕄∣ n ↑ x ∣ M /𝕄

wk𝕊∣_↑_∣_ : ℕ → ℕ → 𝕊 → 𝕊
wk𝕊∣ n ↑ x ∣ []      = []
wk𝕊∣ n ↑ x ∣ (E ∷ Γ) = wk𝕊𝔼∣ n ↑ x ∣ E ∷ wk𝕊∣ n ↑ x ∣ Γ

record Weakening (S : Set) : Set where
  inductive
  constructor mkWeakening
  infixr 30 wk∣_↑_∣_
  field
    wk∣_↑_∣_ : ℕ → ℕ → S → S

open Weakening {{...}} public

{-# DISPLAY Weakening.wk∣_↑_∣_ n m s = wk∣ n ↑ m ∣ s #-}

instance
  Weakeningℕ : Weakening ℕ
  wk∣_↑_∣_ {{Weakeningℕ}} = wkℕ∣_↑_∣_

  Weakening𝕂 : Weakening 𝕂
  wk∣_↑_∣_ {{Weakening𝕂}} = wk𝕂∣_↑_∣_

  Weakening𝕋 : Weakening 𝕋
  wk∣_↑_∣_ {{Weakening𝕋}} = wk𝕋∣_↑_∣_

  Weakeningℂ𝔼 : Weakening ℂ𝔼
  wk∣_↑_∣_ {{Weakeningℂ𝔼}} = wkℂ𝔼∣_↑_∣_

  Weakeningℂ𝔼⁻ : Weakening ℂ𝔼⁻
  wk∣_↑_∣_ {{Weakeningℂ𝔼⁻}} = wkℂ𝔼⁻∣_↑_∣_

  Weakeningℂ : Weakening ℂ
  wk∣_↑_∣_ {{Weakeningℂ}} = wkℂ∣_↑_∣_

  Weakeningℂ⁻ : Weakening ℂ⁻
  wk∣_↑_∣_ {{Weakeningℂ⁻}} = wkℂ⁻∣_↑_∣_

  Weakening𝕄 : Weakening 𝕄
  wk∣_↑_∣_ {{Weakening𝕄}} = wk𝕄∣_↑_∣_

  Weakening𝕊𝔼 : Weakening 𝕊𝔼
  wk∣_↑_∣_ {{Weakening𝕊𝔼}} = wk𝕊𝔼∣_↑_∣_

  Weakening𝕊 : Weakening 𝕊
  wk∣_↑_∣_ {{Weakening𝕊}} = wk𝕊∣_↑_∣_

infixr 30 s𝕂∣𝕊𝔼_/_∣_
infixr 30 s𝕋∣𝕊𝔼_/_∣_
infixr 30 s𝕄∣𝕊𝔼_/_∣_
infixr 30 sℂ∣ℂ_/_∣_

s𝕂∣𝕊𝔼_/_∣_ : 𝕊𝔼 → ℕ → 𝕂 → 𝕂
s𝕂∣𝕊𝔼 s / x ∣ Tyₗ = Tyₗ

s𝕋∣𝕊𝔼_/_∣_ : 𝕊𝔼 → ℕ → 𝕋 → 𝕋
s𝕋∣𝕊𝔼 s / x ∣ tvarₗ y
  with y ≥? x
...  | no  _             = tvarₗ y
...  | yes _
    with y ≟ x
...    | no  _           = tvarₗ (y ∸ 1)
...    | yes _
      with s
...      | T /𝕋          = T
...      | _ /𝕄          = ⊤ₗ
s𝕋∣𝕊𝔼 s / x ∣ (U ⊸ₗ V)   = s𝕋∣𝕊𝔼 s / x ∣ U ⊸ₗ s𝕋∣𝕊𝔼 s / x ∣ V
s𝕋∣𝕊𝔼 s / x ∣ (!ₗ U)     = !ₗ s𝕋∣𝕊𝔼 s / x ∣ U
s𝕋∣𝕊𝔼 s / x ∣ (∀ₗ K ∙ U) = ∀ₗ s𝕂∣𝕊𝔼 s / x ∣ K ∙ s𝕋∣𝕊𝔼 wk∣ 1 ↑ 0 ∣ s / suc x ∣ U

s𝕄∣𝕊𝔼_/_∣_ : 𝕊𝔼 → ℕ → 𝕄 → 𝕄
s𝕄∣𝕊𝔼 s / x ∣ varₗ y
  with y ≥? x
...  | no  _                      = varₗ y
...  | yes _
    with y ≟ x
...    | no  _                    = varₗ (y ∸ 1)
...    | yes _
      with s
...      | M /𝕄                   = M
...      | _ /𝕋                   = ttₗ
s𝕄∣𝕊𝔼 s / x ∣ (λₗ T ∘ N)          = λₗ s𝕋∣𝕊𝔼 s / x ∣ T ∘ s𝕄∣𝕊𝔼 wk∣ 1 ↑ 0 ∣ s / suc x ∣ N
s𝕄∣𝕊𝔼 s / x ∣ (N $ₗ∘ O)           = s𝕄∣𝕊𝔼 s / x ∣ N $ₗ∘ s𝕄∣𝕊𝔼 s / x ∣ O
s𝕄∣𝕊𝔼 s / x ∣ bangₗ N             = bangₗ (s𝕄∣𝕊𝔼 s / x ∣ N)
s𝕄∣𝕊𝔼 s / x ∣ (let-bangₗ N inₗ O) = let-bangₗ s𝕄∣𝕊𝔼 s / x ∣ N inₗ s𝕄∣𝕊𝔼 wk∣ 1 ↑ 0 ∣ s / suc x ∣ O
s𝕄∣𝕊𝔼 s / x ∣ (Λₗ K ∙ N)          = Λₗ s𝕂∣𝕊𝔼 s / x ∣ K ∙ s𝕄∣𝕊𝔼 wk∣ 1 ↑ 0 ∣ s / suc x ∣ N
s𝕄∣𝕊𝔼 s / x ∣ (N $$ₗ∙ T)          = s𝕄∣𝕊𝔼 s / x ∣ N $$ₗ∙ s𝕋∣𝕊𝔼 s / x ∣ T

s𝕊𝔼∣𝕊𝔼_/_∣_ : 𝕊𝔼 → ℕ → 𝕊𝔼 → 𝕊𝔼
s𝕊𝔼∣𝕊𝔼 s / x ∣ (T /𝕋) = s𝕋∣𝕊𝔼 s / x ∣ T /𝕋
s𝕊𝔼∣𝕊𝔼 s / x ∣ (M /𝕄) = s𝕄∣𝕊𝔼 s / x ∣ M /𝕄

-- Do we really want this?
sℂ∣ℂ_/_∣_ : ℂ → ℕ → ℂ → ℂ
sℂ∣ℂ Γ / x     ∣ []               = []
sℂ∣ℂ Γ / zero  ∣ (K       /𝕂 ∷ Δ) = Γ ++ Δ
sℂ∣ℂ Γ / suc x ∣ (K       /𝕂 ∷ Δ) = s𝕂∣𝕊𝔼 ⊤ₗ /𝕋 / x ∣ wk∣ len Γ ↑ suc x ∣ K /𝕂 ∷ sℂ∣ℂ Γ / x ∣ Δ
sℂ∣ℂ Γ / zero  ∣ ((T , u) /𝕋 ∷ Δ) = Γ ℂ×𝕌 u ++ Δ
sℂ∣ℂ Γ / suc x ∣ ((T , u) /𝕋 ∷ Δ) = (s𝕋∣𝕊𝔼 ttₗ /𝕄 / x ∣ wk∣ len Γ ↑ suc x ∣ T , u) /𝕋 ∷ sℂ∣ℂ Γ / x ∣ Δ

record Substitution (S : Set) (T : Set) : Set where
  inductive
  constructor mkSubstitution
  infixr 30 s∣_/_∣_
  field
    s∣_/_∣_ : T → ℕ → S → S

open Substitution {{...}} public

{-# DISPLAY Substitution.s∣_/_∣_ t m s = s∣ t / m ∣ s #-}

instance
  Substitution𝕂𝕊𝔼 : Substitution 𝕂 𝕊𝔼
  s∣_/_∣_ {{Substitution𝕂𝕊𝔼}} = s𝕂∣𝕊𝔼_/_∣_

  Substitution𝕋𝕊𝔼 : Substitution 𝕋 𝕊𝔼
  s∣_/_∣_ {{Substitution𝕋𝕊𝔼}} = s𝕋∣𝕊𝔼_/_∣_

  Substitution𝕄𝕊𝔼 : Substitution 𝕄 𝕊𝔼
  s∣_/_∣_ {{Substitution𝕄𝕊𝔼}} = s𝕄∣𝕊𝔼_/_∣_

  Substitution𝕊𝔼𝕊𝔼 : Substitution 𝕊𝔼 𝕊𝔼
  s∣_/_∣_ {{Substitution𝕊𝔼𝕊𝔼}} = s𝕊𝔼∣𝕊𝔼_/_∣_

  Substitutionℂℂ : Substitution ℂ ℂ
  s∣_/_∣_ {{Substitutionℂℂ}} M = sℂ∣ℂ M /_∣_

λₗ_∙_ : 𝕋 → 𝕄 → 𝕄
λₗ T ∙ M = λₗ !ₗ T ∘ let-bangₗ varₗ 0 inₗ wk∣ 1 ↑ 1 ∣ M
