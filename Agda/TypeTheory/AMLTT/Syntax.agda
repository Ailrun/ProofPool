{-# OPTIONS --without-K --safe #-}
open import TypeTheory.AMLTT.ModeSpec

module TypeTheory.AMLTT.Syntax {ℓ₁ ℓ₂} (ℳ : ModeSpec ℓ₁ ℓ₂) where

open import Data.Bool using (Bool)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤)

open ModeSpec ℳ

open import TypeTheory.AMLTT.TypeClass public

------------------------------------------------------------
-- Term, i.e. Type and Simultaneous Substitution
--
infix  24 `Univ
infixr 24 `↑[_⇗_]_
infixr 24 `lift[_⇗_]_
infixr 24 `unlift[_⇗_]_
infixr 24 `↓[_⇘_]_
infixr 24 `return[_⇘_]_
infixr 22 `let-return[_⇘_]_then_of_
infixr 24 `suc
infixr 24 `rec
infixr 22 `Π_⊸_
infixr 22 _`⊸_
infixr 22 `Π[_⇘_]_⊸_of_
infixr 22 `λ_⊸_
infixr 22 `λ[_⇘_]_⊸_of_
infixl 23 _`$_
infixl 23 _`$[_⇘_]_
infixl 25 `#_

infixr  4 _`⟦|_⟧

data `Term : Set ℓ₁
data `Subst : Set ℓ₁
`Type : Set ℓ₁

`Type = `Term
data `Term where
  -- (Cumulative) Universe
  --
  `Univ : (i : ℕ) → `Type

  -- Upshift
  --
  -- "`↑[ l ⇗ h ] T" shifts "T" at mode "l" up to mode "h".
  --
  `↑[_⇗_]_      : (l h : `Mode) (S : `Type) → `Type
  `lift[_⇗_]_   : (l h : `Mode) (s : `Term) → `Term
  `unlift[_⇗_]_ : (l h : `Mode) (s : `Term) → `Term

  -- Downshift
  --
  -- "`↓[ h ⇘ l ] T" shifts "T" at mode "h" down to mode "l".
  --
  `↓[_⇘_]_                  : (h l : `Mode) (S : `Type)               → `Type
  `return[_⇘_]_             : (h l : `Mode) (s : `Term)               → `Term
  `let-return[_⇘_]_then_of_ : (h l : `Mode) (s t : `Term) (T : `Type) → `Term

  -- Natural number
  --
  `Nat  :                               `Type
  `zero :                               `Term
  `suc  : (s : `Term)                 → `Term
  `rec  : (S : `Type) (t u v : `Term) → `Term

  -- Lambda-calculus
  --
  `Π_⊸_ : (S T : `Type)                   → `Type
  `λ_⊸_ : (S : `Type) (t : `Term)         → `Term
  _`$_  : (s t : `Term)                   → `Term
  `#_   :                         (x : ℕ) → `Term

  -- Explicit substitution
  --
  -- We introduce this as substitution is a partial function
  `sub : (s : `Term) (σ : `Subst) → `Term

infixl  4 _`,_
infixl  3 _`∘_

data `Subst where
  `id  :                              `Subst
  `wk  :                              `Subst
  _`,_ : (σ : `Subst)   (s : `Term) → `Subst
  _`∘_ : (σ τ : `Subst)             → `Subst

------------------------------------------------------------
-- Useability
--

-- How should we deal with something like
--
--   (`Nat , true , l) ∷ (`Fin # 0 , true , l) ∷ (`Fin # 1 , true , l) ∷ [] ⊢[ l ] (# 1 , # 0) : `Fin (# 2) × `Fin (# 2)
--
-- ?
-- Instead of true/false, let's use used/unused/disabled, and both unused/used are useable in type checking/equality.
-- Then, we can treat
--
--   (`Nat , `used , l) ∷ (`Fin # 0 , `unused , l) ∷ (`Fin # 0 , `used , l) ∷ [] ⊢[ l ] # 1 : `Fin (# 2)
--
-- as well-typed (i.e. since we allow types to use "`used" variables) to make "(# 1 , # 0)" be well-typed.

data `Useability : Set where
  `⁺ : `Useability -- Unused (in terms)
  `⁻ : `Useability -- Used (in terms)
  `Ø : `Useability -- Disabled

------------------------------------------------------------
-- Typing Context
--
infixl  5 _`∙_
infix   6 `⟨_⋆_/_⟩

record `ContextEntry : Set ℓ₁ where
  constructor `⟨_⋆_/_⟩
  field
    type : `Type
    mode : `Mode
    useability : `Useability

`Context : Set ℓ₁
`Context = List `ContextEntry

pattern _`∙_ as a = a ∷ as

module Variable where
  variable
    -- Boolean
    b b₀ b₁ b₂ b₃ b′ b′₀ b′₁ b′₂ b′₃ b″ b″₀ b″₁ b″₂ b″₃ b‴ b‴₀ b‴₁ b‴₂ b‴₃ : Bool

    -- Universe levels
    i i₀ i₁ i₂ i₃ i′ i′₀ i′₁ i′₂ i′₃ i″ i″₀ i″₁ i″₂ i″₃ i‴ i‴₀ i‴₁ i‴₂ i‴₃ : ℕ
    j j₀ j₁ j₂ j₃ j′ j′₀ j′₁ j′₂ j′₃ j″ j″₀ j″₁ j″₂ j″₃ j‴ j‴₀ j‴₁ j‴₂ j‴₃ : ℕ

    -- Variable indices
    x x₀ x₁ x₂ x₃ x′ x′₀ x′₁ x′₂ x′₃ x″ x″₀ x″₁ x″₂ x″₃ x‴ x‴₀ x‴₁ x‴₂ x‴₃ : ℕ
    y y₀ y₁ y₂ y₃ y′ y′₀ y′₁ y′₂ y′₃ y″ y″₀ y″₁ y″₂ y″₃ y‴ y‴₀ y‴₁ y‴₂ y‴₃ : ℕ
    z z₀ z₁ z₂ z₃ z′ z′₀ z′₁ z′₂ z′₃ z″ z″₀ z″₁ z″₂ z″₃ z‴ z‴₀ z‴₁ z‴₂ z‴₃ : ℕ

    -- Modes
    h h₀ h₁ h₂ h₃ h′ h′₀ h′₁ h′₂ h′₃ h″ h″₀ h″₁ h″₂ h″₃ h‴ h‴₀ h‴₁ h‴₂ h‴₃ : `Mode
    l l₀ l₁ l₂ l₃ l′ l′₀ l′₁ l′₂ l′₃ l″ l″₀ l″₁ l″₂ l″₃ l‴ l‴₀ l‴₁ l‴₂ l‴₃ : `Mode
    m m₀ m₁ m₂ m₃ m′ m′₀ m′₁ m′₂ m′₃ m″ m″₀ m″₁ m″₂ m″₃ m‴ m‴₀ m‴₁ m‴₂ m‴₃ : `Mode
    n n₀ n₁ n₂ n₃ n′ n′₀ n′₁ n′₂ n′₃ n″ n″₀ n″₁ n″₂ n″₃ n‴ n‴₀ n‴₁ n‴₂ n‴₃ : `Mode

    -- Types
    S S₀ S₁ S₂ S₃ S′ S′₀ S′₁ S′₂ S′₃ S″ S″₀ S″₁ S″₂ S″₃ S‴ S‴₀ S‴₁ S‴₂ S‴₃ : `Type
    T T₀ T₁ T₂ T₃ T′ T′₀ T′₁ T′₂ T′₃ T″ T″₀ T″₁ T″₂ T″₃ T‴ T‴₀ T‴₁ T‴₂ T‴₃ : `Type
    U U₀ U₁ U₂ U₃ U′ U′₀ U′₁ U′₂ U′₃ U″ U″₀ U″₁ U″₂ U″₃ U‴ U‴₀ U‴₁ U‴₂ U‴₃ : `Type
    V V₀ V₁ V₂ V₃ V′ V′₀ V′₁ V′₂ V′₃ V″ V″₀ V″₁ V″₂ V″₃ V‴ V‴₀ V‴₁ V‴₂ V‴₃ : `Type
    W W₀ W₁ W₂ W₃ W′ W′₀ W′₁ W′₂ W′₃ W″ W″₀ W″₁ W″₂ W″₃ W‴ W‴₀ W‴₁ W‴₂ W‴₃ : `Type

    -- Terms
    s s₀ s₁ s₂ s₃ s′ s′₀ s′₁ s′₂ s′₃ s″ s″₀ s″₁ s″₂ s″₃ s‴ s‴₀ s‴₁ s‴₂ s‴₃ : `Term
    t t₀ t₁ t₂ t₃ t′ t′₀ t′₁ t′₂ t′₃ t″ t″₀ t″₁ t″₂ t″₃ t‴ t‴₀ t‴₁ t‴₂ t‴₃ : `Term
    u u₀ u₁ u₂ u₃ u′ u′₀ u′₁ u′₂ u′₃ u″ u″₀ u″₁ u″₂ u″₃ u‴ u‴₀ u‴₁ u‴₂ u‴₃ : `Term
    v v₀ v₁ v₂ v₃ v′ v′₀ v′₁ v′₂ v′₃ v″ v″₀ v″₁ v″₂ v″₃ v‴ v‴₀ v‴₁ v‴₂ v‴₃ : `Term
    w w₀ w₁ w₂ w₃ w′ w′₀ w′₁ w′₂ w′₃ w″ w″₀ w″₁ w″₂ w″₃ w‴ w‴₀ w‴₁ w‴₂ w‴₃ : `Term

    -- Substitutions
    σ σ₀ σ₁ σ₂ σ₃ σ′ σ′₀ σ′₁ σ′₂ σ′₃ σ″ σ″₀ σ″₁ σ″₂ σ″₃ σ‴ σ‴₀ σ‴₁ σ‴₂ σ‴₃ : `Subst
    τ τ₀ τ₁ τ₂ τ₃ τ′ τ′₀ τ′₁ τ′₂ τ′₃ τ″ τ″₀ τ″₁ τ″₂ τ″₃ τ‴ τ‴₀ τ‴₁ τ‴₂ τ‴₃ : `Subst
    υ υ₀ υ₁ υ₂ υ₃ υ′ υ′₀ υ′₁ υ′₂ υ′₃ υ″ υ″₀ υ″₁ υ″₂ υ″₃ υ‴ υ‴₀ υ‴₁ υ‴₂ υ‴₃ : `Subst

    -- Useability
    a a₀ a₁ a₂ a₃ a′ a′₀ a′₁ a′₂ a′₃ a″ a″₀ a″₁ a″₂ a″₃ a‴ a‴₀ a‴₁ a‴₂ a‴₃ : `Useability

    -- Context Entries
    e e₀ e₁ e₂ e₃ e′ e′₀ e′₁ e′₂ e′₃ e″ e″₀ e″₁ e″₂ e″₃ e‴ e‴₀ e‴₁ e‴₂ e‴₃ : `ContextEntry

    -- Contexts
    Γ Γ₀ Γ₁ Γ₂ Γ₃ Γ′ Γ′₀ Γ′₁ Γ′₂ Γ′₃ Γ″ Γ″₀ Γ″₁ Γ″₂ Γ″₃ Γ‴ Γ‴₀ Γ‴₁ Γ‴₂ Γ‴₃ : `Context
    Δ Δ₀ Δ₁ Δ₂ Δ₃ Δ′ Δ′₀ Δ′₁ Δ′₂ Δ′₃ Δ″ Δ″₀ Δ″₁ Δ″₂ Δ″₃ Δ‴ Δ‴₀ Δ‴₁ Δ‴₂ Δ‴₃ : `Context
    Φ Φ₀ Φ₁ Φ₂ Φ₃ Φ′ Φ′₀ Φ′₁ Φ′₂ Φ′₃ Φ″ Φ″₀ Φ″₁ Φ″₂ Φ″₃ Φ‴ Φ‴₀ Φ‴₁ Φ‴₂ Φ‴₃ : `Context
    Ψ Ψ₀ Ψ₁ Ψ₂ Ψ₃ Ψ′ Ψ′₀ Ψ′₁ Ψ′₂ Ψ′₃ Ψ″ Ψ″₀ Ψ″₁ Ψ″₂ Ψ″₃ Ψ‴ Ψ‴₀ Ψ‴₁ Ψ‴₂ Ψ‴₃ : `Context

open Variable

------------------------------------------------------------
-- Normal/neutral/canonical form
--
data `Norm : `Term → Set (ℓ₁ ⊔ ℓ₂)
data `Neut : `Term → Set (ℓ₁ ⊔ ℓ₂)
-- Read this "⋆" as "at".
data `Canon⋆ (m : `Mode) : `Term → Set (ℓ₁ ⊔ ℓ₂)

data `Norm where
  `Univ : (i : ℕ) → `Norm (`Univ i)

  `↑[_⇗_]_    : (l h : `Mode) (NS : `Norm S)                    → `Norm (`↑[ l ⇗ h ] S)
  `lift[_⇗_]_ : (l h : `Mode)                (Cs : `Canon⋆ h s) → `Norm (`lift[ l ⇗ h ] s)
  
  `↓[_⇘_]_      : (h l : `Mode) (NS : `Norm S)                → `Norm (`↓[ h ⇘ l ] S)
  `return[_⇘_]_ : (h l : `Mode)                (Ns : `Norm s) → `Norm (`return[ h ⇘ l ] s)

  `Nat  :                  `Norm `Nat
  `zero :                  `Norm `zero
  `suc  : (Ns : `Norm s) → `Norm (`suc s)

  `Π_⊸_ : (NS : `Norm S) (NT : `Norm T)                → `Norm (`Π S ⊸ T)
  `λ_⊸_ : (NS : `Norm S)                (Nt : `Norm t) → `Norm (`λ S ⊸ t)

  `neut : (Rs : `Neut s) → `Norm s

data `Neut where
  `unlift[_⇗_]_ : (l h : `Mode) (Rs : `Neut s) → `Neut (`unlift[ l ⇗ h ] s)

  `let-return[_⇘_]_then_of_ : (h l : `Mode) (Rs : `Neut s) (Nt : `Norm t) (Nt : `Norm T) → `Neut (`let-return[ h ⇘ l ] s then t of T)

  `rec : (NS : `Norm S) (Rt : `Neut t) (Nu : `Norm u) (Nv : `Norm v) → `Neut (`rec S t u v)

  _`$_ : (Rs : `Neut s) (Nt : `Norm t) → `Neut (s `$ t)
  `#_  : (x : ℕ)                       → `Neut (`# x)

¬lift : `Term → Set
¬lift (`Univ i)                            = ⊤
¬lift (`↑[ l ⇗ h ] S)                      = ⊤
¬lift (`lift[ l ⇗ h ] s)                   = ⊥
¬lift (`unlift[ l ⇗ h ] s)                 = ⊤
¬lift (`↓[ h ⇘ l ] S)                      = ⊤
¬lift (`return[ h ⇘ l ] s)                 = ⊤
¬lift (`let-return[ h ⇘ l ] s then t of T) = ⊤
¬lift `Nat                                 = ⊤
¬lift `zero                                = ⊤
¬lift (`suc s)                             = ⊤
¬lift (`rec S t u v)                       = ⊤
¬lift (`Π S ⊸ T)                           = ⊤
¬lift (`λ S ⊸ t)                           = ⊤
¬lift (s `$ t)                             = ⊤
¬lift (`# x)                               = ⊤
¬lift (`sub s σ)                           = ⊤

data `Canon⋆ m where
  `Univ : (i : ℕ) → `Canon⋆ m (`Univ i)

  `↑[_⇗_]_       : (l h : `Mode)                          (CS : `Canon⋆ m S)                    → `Canon⋆ m (`↑[ l ⇗ h ] S)
  `lift[_⇗_]_    : (l h : `Mode)                          (Cs : `Canon⋆ m s)                    → `Canon⋆ m (`lift[ l ⇗ h ] s)
  `unlift[≰_⇗_]_ : {l : `Mode} (m≰l : m ≰ₘ l) (h : `Mode) (Cs : `Canon⋆ m s)                    → `Canon⋆ m (`unlift[ l ⇗ h ] s)
  `unlift[≤_⇗_]_ : {l : `Mode} (m≤l : m ≤ₘ l) (h : `Mode) (Ns : `Norm s)     {¬lifts : ¬lift s} → `Canon⋆ m (`unlift[ l ⇗ h ] s)

  `↓[_⇘_]_                  : (h l : `Mode)                          (CS : `Canon⋆ m S)                                       → `Canon⋆ m (`↓[ h ⇘ l ] S)
  `return[_⇘≰_]_            : (h : `Mode) {l : `Mode} (m≰l : m ≰ₘ l) (Cs : `Canon⋆ m s)                                       → `Canon⋆ m (`return[ h ⇘ l ] s)
  `return[_⇘≤_]_            : (h : `Mode) {l : `Mode} (m≤l : m ≤ₘ l) (Ns : `Norm s)                                           → `Canon⋆ m (`return[ h ⇘ l ] s)
  `let-return[_⇘_]_then_of_ : (h l : `Mode)                          (Cs : `Canon⋆ m s) (Ct : `Canon⋆ m t) (CT : `Canon⋆ m T) → `Canon⋆ m (`let-return[ h ⇘ l ] s then t of T)

  `Nat  :                                                                               `Canon⋆ m `Nat
  `zero :                                                                               `Canon⋆ m `zero
  `suc :                     (Cs : `Canon⋆ m s)                                       → `Canon⋆ m (`suc s)
  `rec  : (CS : `Canon⋆ m S) (Cv : `Canon⋆ m v) (Cu : `Canon⋆ m u) (Cv : `Canon⋆ m v) → `Canon⋆ m (`rec S t u v)

  `Π_⊸_ : (CS : `Canon⋆ m S) (CT : `Canon⋆ m T)                    → `Canon⋆ m (`Π S ⊸ T)
  `λ_⊸_ : (CS : `Canon⋆ m S) (Ct : `Canon⋆ m t)                    → `Canon⋆ m (`λ S ⊸ t)
  _`$_  :                    (Cs : `Canon⋆ m s) (Ct : `Canon⋆ m t) → `Canon⋆ m (s `$ t)
  `#_   :                    (x : ℕ)                               → `Canon⋆ m (`# x)

------------------------------------------------------------
-- Helper instances
--
instance
  `TermHasSubst : HasSubst `Term `Subst
  `TermHasSubst = record { _`⟦_⟧ = `sub }

  `SubstHasSubst : HasSubst `Subst `Subst
  `SubstHasSubst = record { _`⟦_⟧ = _`∘_ }

------------------------------------------------------------
-- Helper definitions
--

-- Single substitution
_`⟦|_⟧ : `Term → `Term → `Term
s `⟦| t ⟧ = s `⟦ `id `, t ⟧

_`⟦|Ø⟧ : `Term → `Term
s `⟦|Ø⟧ = s `⟦ `id `,Ø ⟧

-- Projection of substitution
--
-- This sends
--   Γ ⊢ σ ⦂ Δ ⸴ A
-- to
--   Γ ⊢ `p σ ⦂ Δ
`pr : `Subst → `Subst
`pr = `wk `∘_

-- Hoisting of substitution
--
-- This sends
--   Γ ⊢ σ ⦂ Δ
-- to
--   Γ , S `⟦ σ ⟧ ⊢ `h σ ⦂ Δ ⸴ S
`ho : `Subst → `Subst
`ho σ = (σ `∘ `wk) `, `# 0

`rec-suc-subst : `Subst
`rec-suc-subst = (`wk `∘ `wk) `, `suc (`# 1)

-- Non-dependent function space

_`⊸_ : (S T : `Type) → `Type
S `⊸ T = `Π S ⊸ T `⟦ `wk ⟧

-- Cross-mode function space
`Π[_⇘_]_⊸_of_ : (h l : `Mode) (S T : `Type) (i : ℕ) → `Type
`Π[ h ⇘ l ] S ⊸ T of i = `Π `↓[ h ⇘ l ] S ⊸ `let-return[ h ⇘ l ] `# 0 then T `⟦ `ho `wk ⟧ of `Univ i

`λ[_⇘_]_⊸_of_ : (h l : `Mode) (S : `Type) (t : `Term) (T : `Type) → `Term
`λ[ h ⇘ l ] S ⊸ t of T = `λ `↓[ h ⇘ l ] S ⊸ `let-return[ h ⇘ l ] `# 0 then t `⟦ `ho `wk ⟧ of T

_`$[_⇘_]_ : (s : `Term) (h l : `Mode) (t : `Term) → `Term
s `$[ h ⇘ l ] t = s `$ `return[ h ⇘ l ] t

-- τ : Γ ⇒ Γ′
-- σ , M : Γ′ ⇒ Γ″ , A
-- σ , M ∘ τ : Γ ⇒ Γ″ , A
-- (σ ∘ τ) , M `⟦ τ ⟧ : Γ ⇒ Γ″ , A
--
-- τ : Γ ⇒ Γ′ , A
-- σ : Γ′ ⇒ Γ″
-- wk σ : Γ′ , A ⇒ Γ″
-- wk σ ∘ τ : Γ ⇒ Γ″
--
-- τ , L : Γ ⇒ Γ′ , A
-- wk : Γ′ , A ⇒ Γ′
-- τ : Γ ⇒ Γ′

-- _`∘_ : (σ τ : `Subst) → `Subst
-- (σ `, L)      `∘ τ        = (σ `∘ τ) `, (L `⟦ τ ⟧)
-- (σ `,Ø)       `∘ τ        = (σ `∘ τ) `,Ø
-- (`wk 0)       `∘ τ        = τ
-- (`wk (suc n)) `∘ (`wk m)  = `wk (suc (n + m))
-- (`wk (suc n)) `∘ (τ `, L) = `wk n `∘ τ
-- (`wk (suc n)) `∘ (τ `,Ø)  = `wk n `∘ τ
