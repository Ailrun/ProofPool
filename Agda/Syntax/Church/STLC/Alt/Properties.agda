{-# OPTIONS --safe #-}
module Syntax.Church.STLC.Alt.Properties where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂)

open import Syntax.Church.STLC.Alt.Base
open Variables

`++-identityʳ : ∀ (es : ExEs Γ A B) →
                ----------------------
                es `++ [] ≡ es
`++-identityʳ []        = refl
`++-identityʳ (ee ∷ es) = cong (_ ∷_) (`++-identityʳ es)

`++-assoc : ∀ (es₀ : ExEs Γ A B) (es₁ : ExEs Γ B C) {es₂ : ExEs Γ C D} →
            -------------------------------------------------------------
            es₀ `++ (es₁ `++ es₂) ≡ (es₀ `++ es₁) `++ es₂
`++-assoc []          es₁ = refl
`++-assoc (ee₀ ∷ es₀) es₁ = cong (_ ∷_) (`++-assoc es₀ es₁)
