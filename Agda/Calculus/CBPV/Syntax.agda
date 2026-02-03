{-# OPTIONS --safe #-}
module Calculus.CBPV.Syntax where

open import Data.Fin using (Fin)
open import Data.List using (List)
open import Data.Nat using (ℕ)
open import Data.Vec using (Vec)

data TypeV : Set
data TypeC : Set

data TypeV where
  `1   : TypeV
  _`×_ : TypeV → TypeV → TypeV
  `Σ_  : ∀ {n} → Vec TypeV n → TypeV
  -- We use `↑ instead of U for its similarity with Adjoint Logic
  `↑_  : TypeC → TypeV

data TypeC where
  _`→_ : TypeV → TypeC → TypeC
  `Π_  : ∀ {n} → Vec TypeC n → TypeC
  -- We use `↓ instead of F for its similarity with Adjoint Logic
  `↓_  : TypeV → TypeC

Context : Set
Context = List TypeV

data TermV : Set
data TermC : Set

data TermV where
  `#_    : ℕ → TermV

  `one   : TermV

  _`,_   : TermV → TermV → TermV

  ⦅_⦆`,_ : ∀ {n} → Fin n → TermV → TermV

  `thunk : TermC → TermV

data TermC where
  `pm_as`one⇒_ : TermV → TermC → TermC

  `pm_as`,⇒_   : TermV → TermC → TermC

  `pm_as∥_∥    : ∀ {n} → TermV → Vec TermC n → TermC

  `force       : TermV → TermC

  `λ_          : TermC → TermC
  _`&_         : TermV → TermC → TermC

  `λ∥_∥        : ∀ {n} → Vec TermC n → TermC
  ⦅_⦆`&_       : ∀ {n} → Fin n → TermC → TermC

  `return      : TermV → TermC
  _`to_        : TermC → TermC → TermC

  `print_and_  : ℕ → TermC → TermC

module Variable where
  variable
    x x′ x″ y y′ y″ z z′ z″ : ℕ

    Γ Γ′ Γ″ Δ Δ′ Δ″ Ψ Ψ′ Ψ″ : Context
    A A′ A″ B B′ B″ : TypeV
    S S′ S″ T T′ T″ : TypeC
    U U′ U″ V V′ V″ W W′ W″ : TermV
    L L′ L″ M M′ M″ N N′ N″ : TermC
