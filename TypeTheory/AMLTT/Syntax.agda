{-# OPTIONS --without-K --safe #-}
open import TypeTheory.AMLTT.ModeSpec

module TypeTheory.AMLTT.Syntax {ℓ₁ ℓ₂} (ℳ : `ModeSpec ℓ₁ ℓ₂) where

open import Agda.Primitive
open import Data.Bool using (Bool)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_)
open import Data.Unit using (⊤)

open `ModeSpec ℳ

open import TypeTheory.AMLTT.TypeClass

------------------------------------------------------------
-- Term, i.e. Type and Simultaneous Substitution
--
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
  `↑[_⇗_]_      : (l h : `Mode) (A : `Type)             → `Type
  `lift[_⇗_]_   : (l h : `Mode)             (L : `Term) → `Term
  `unlift[_⇗_]_ : (l h : `Mode)             (L : `Term) → `Term

  -- Downshift
  --
  -- "`↓[ h ⇘ l ] T" shifts "T" at mode "h" down to mode "l".
  --
  `↓[_⇘_]_          : (h l : `Mode) (A : `Type)               → `Type
  `return[_⇘_]_     : (h l : `Mode)             (L : `Term)   → `Term
  `let[_⇘_]_return_ : (h l : `Mode)             (L M : `Term) → `Term

  -- Natural number
  --
  `Nat  :                               `Type
  `zero :                               `Term
  `succ :             (L : `Term)     → `Term
  `rec  : (A : `Type) (L M N : `Term) → `Term

  -- Lambda-calculus
  --
  `Π_⊸_ : (A B : `Type)               → `Type
  `λ_⊸_ : (A : `Type)   (L : `Term)   → `Term
  _`$_  :               (L M : `Term) → `Term
  `#_   :               (x : ℕ)       → `Term

  -- Explicit substitution
  --
  -- We introduce this as substitution is a partial function
  `sub : (L : `Term) (σ : `Subst) → `Term

data `Subst where
  `id  :                              `Subst
  `wk  :                              `Subst
  _`,_ : (σ : `Subst)   (L : `Term) → `Subst
  _`,Ø : (σ : `Subst)               → `Subst
  _`∘_ : (σ τ : `Subst)             → `Subst

------------------------------------------------------------
-- Normal/neutral/canonical form
--
data `Norm : Set (ℓ₁ ⊔ ℓ₂)
data `Neut : Set (ℓ₁ ⊔ ℓ₂)
data `Canon[_≤] (m : `Mode) : Set (ℓ₁ ⊔ ℓ₂)

data `Norm where
  `Univ : (i : ℕ) → `Norm

  `↑[_⇗_]_    : (l h : `Mode) (U : `Norm)                    → `Norm
  `lift[_⇗_]_ : (l h : `Mode)             (C : `Canon[ h ≤]) → `Norm
  
  `↓[_⇘_]_      : (h l : `Mode) (U : `Norm)             → `Norm
  `return[_⇘_]_ : (h l : `Mode)             (U : `Norm) → `Norm

  `Nat  :               `Norm
  `zero :               `Norm
  `succ : (U : `Norm) → `Norm

  `Π_⊸_ : (U V : `Norm)             → `Norm
  `λ_⊸_ : (U : `Norm)   (V : `Norm) → `Norm

  `neut : (R : `Neut) → `Norm

data `Neut where
  `unlift[_⇗_]_ : (l h : `Mode) (R : `Neut) → `Neut

  `let[_⇘_]_return_ : (h l : `Mode) (R : `Neut) (U : `Norm) → `Neut

  `rec : (U : `Norm) (R : `Neut) (V W : `Norm) → `Neut

  _`$_ : (R : `Neut) (U : `Norm) → `Neut
  `#_  :             (x : ℕ)     → `Neut

¬lift : (U : `Norm) → Set
¬lift (`Univ i)            = ⊤
¬lift (`↑[ l ⇗ h ] U)      = ⊤
¬lift (`lift[ l ⇗ h ] C)   = ⊥
¬lift (`↓[ h ⇘ l ] U)      = ⊤
¬lift (`return[ h ⇘ l ] U) = ⊤
¬lift `Nat                 = ⊤
¬lift `zero                = ⊤
¬lift (`succ U)            = ⊤
¬lift (`Π U ⊸ V)           = ⊤
¬lift (`λ U ⊸ V)           = ⊤
¬lift (`neut R)            = ⊤

data `Canon[_≤] m where
  `Univ : (i : ℕ) → `Canon[ m ≤]

  `↑[_⇗_]_       : (l h : `Mode)                          (C : `Canon[ m ≤])                                       → `Canon[ m ≤]
  `lift[_⇗_]_    : (l h : `Mode)                                             (C : `Canon[ m ≤])                    → `Canon[ m ≤]
  `unlift[≰_⇗_]_ : {l : `Mode} (m≰l : m ≰ₘ l) (h : `Mode)                    (C : `Canon[ m ≤])                    → `Canon[ m ≤]
  `unlift[≤_⇗_]_ : {l : `Mode} (m≤l : m ≤ₘ l) (h : `Mode)                    (U : `Norm)        {¬liftU : ¬lift U} → `Canon[ m ≤]

  `↓[_⇘_]_          : (h l : `Mode)                          (C : `Canon[ m ≤])                      → `Canon[ m ≤]
  `return[_⇘≰_]_    : (h : `Mode) {l : `Mode} (m≰l : m ≰ₘ l)                    (C : `Canon[ m ≤])   → `Canon[ m ≤]
  `return[_⇘≤_]_    : (h : `Mode) {l : `Mode} (m≤l : m ≤ₘ l)                    (U : `Norm)          → `Canon[ m ≤]
  `let[_⇘_]_return_ : (h l : `Mode)                                             (C D : `Canon[ m ≤]) → `Canon[ m ≤]

  `Nat  :                                             `Canon[ m ≤]
  `zero :                                             `Canon[ m ≤]
  `succ :                    (C : `Canon[ m ≤])     → `Canon[ m ≤]
  `rec  : (C : `Canon[ m ≤]) (D E F : `Canon[ m ≤]) → `Canon[ m ≤]

  `Π_⊸_ : (C D : `Canon[ m ≤])                      → `Canon[ m ≤]
  `λ_⊸_ : (C : `Canon[ m ≤])   (D : `Canon[ m ≤])   → `Canon[ m ≤]
  _`$_  :                      (C D : `Canon[ m ≤]) → `Canon[ m ≤]
  `#_   :                      (x : ℕ)              → `Canon[ m ≤]

------------------------------------------------------------
-- Typing Context
--
`Context : Set ℓ₁
`Context = List (`Mode × `Type × Bool)

------------------------------------------------------------
-- Helper instances
--
instance
  `TermHasSubst : HasSubst `Term `Subst
  `TermHasSubst = record { _`⟦_⟧ = `sub }

------------------------------------------------------------
-- Helper definitions
--
_`⊸_ : (A B : `Type) → `Type
A `⊸ B = `Π A ⊸ B `⟦ `wk ⟧

_`⟦|_⟧ : `Term → `Term → `Term
L `⟦| M ⟧ = L `⟦ `id `, M ⟧
