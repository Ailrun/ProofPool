------------------------------------------------------------
-- Static Rules for DP Modal Calculus
------------------------------------------------------------

{-# OPTIONS --safe #-}
module Calculus.LambdaBox.Typing where

open import Data.Nat using (ℕ; suc)
open import Data.List using (List; []; _∷_)

open import Calculus.LambdaBox.Syntax

infix   4 _⦂_∈_
infix   4 _⍮_⊢_⦂_

data _⦂_∈_ : ℕ → Type → List Type → Set where
  here  : --------------
          0 ⦂ S ∈ S ∷ Γ

  there : x ⦂ S ∈ Γ →
          ------------------
          suc x ⦂ S ∈ T ∷ Γ

data _⍮_⊢_⦂_ : Context → Context → Term → Type → Set where
  `unit         : -------------------
                  Δ ⍮ Γ ⊢ `unit ⦂ `⊤

  `box          : Δ ⍮ [] ⊢ L ⦂ S →
                  ----------------------
                  Δ ⍮ Γ ⊢ `box L ⦂ `□ S

  `let-box_`in_ : Δ ⍮ Γ ⊢ L ⦂ `□ S →
                  S ∷ Δ ⍮ Γ ⊢ M ⦂ T →
                  -----------------------------
                  Δ ⍮ Γ ⊢ `let-box L `in M ⦂ T

  `λ⦂-∙_        : Δ ⍮ S ∷ Γ ⊢ L ⦂ T →
                  ---------------------------
                  Δ ⍮ Γ ⊢ `λ⦂ S ∙ L ⦂ S `→ T

  _`$_          : Δ ⍮ Γ ⊢ L ⦂ S `→ T →
                  Δ ⍮ Γ ⊢ M ⦂ S →
                  ---------------------
                  Δ ⍮ Γ ⊢ L `$ M ⦂ T

  `#¹_          : u ⦂ S ∈ Δ →
                  ------------------
                  Δ ⍮ Γ ⊢ `#¹ u ⦂ S

  `#⁰_          : x ⦂ S ∈ Γ →
                  ------------------
                  Δ ⍮ Γ ⊢ `#⁰ x ⦂ S
