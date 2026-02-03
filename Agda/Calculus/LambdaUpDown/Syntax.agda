{-# OPTIONS --without-K --safe #-}
module Calculus.LambdaUpDown.Syntax where

open import Data.Empty
open import Data.List
open import Data.Nat
open import Data.Product
open import Data.Unit hiding (_≟_)
open import Relation.Nullary

infix  23 ↑_
infix  23 ↓_
infix  23 #_
infix  22 _⇒_
infixl 22 _$$_
infix  21 Λ_∙_

data Mode : Set where
  prog : Mode
  code : Mode

data Type : Set where
  ↑_  : Type → Type
  ↓_  : Type → Type
  _⇒_ : Type → Type → Type
  Top : Type

data Term : Set where
  lift       : Term → Term
  unlift     : Term → Term
  return     : Term → Term
  let-return : Term → Term → Term

  #_         : ℕ → Term

  Λ_∙_       : Type → Term → Term
  _$$_       : Term → Term → Term
  unit       : Term

Ctx = List (Mode × Type)

infixr 5 _∷ᶜ_
infixr 5 _∷ᵖ_

pattern _∷ᶜ_ S Γ = (code , S) ∷ Γ
pattern _∷ᵖ_ S Γ = (prog , S) ∷ Γ

module Variable where
  variable
    x x′ x″ y y′ y″ z z′ z″ : ℕ

    Γ Γ′ Γ″ Δ Δ′ Δ″ Ψ Ψ′ Ψ″ : Ctx
    S S′ S″ T T′ T″ : Type
    M M′ M″ N N′ N″ L L′ L″ : Term

    md md′ md″ : Mode
