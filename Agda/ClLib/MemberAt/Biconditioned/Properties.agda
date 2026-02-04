{-# OPTIONS --cubical-compatible --safe #-}
module ClLib.MemberAt.Biconditioned.Properties where

open import Agda.Primitive using (Level; _⊔_)
open import Data.List as List using (List; []; _∷_; _++_; length)
open import Data.List.Relation.Unary.All as ListAll using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties as ListAll
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Unit using (tt)
open import Function using (it)
open import Relation.Binary.Core using (REL)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Unary using (Pred; U)

import ClLib.MemberAt.Biconditioned as MemberAt

private
  variable
    ℓa ℓa′ ℓa″ ℓb ℓb′ ℓb″ ℓ ℓ₀ ℓ₁ ℓ₂ : Level
    A : Set ℓa
    A′ : Set ℓa′
    A″ : Set ℓa″
    B : Set ℓb
    B′ : Set ℓb′
    B″ : Set ℓb″

module _ (_~_ : REL A B ℓ₀) (Pre : Pred A ℓ₁) (Post : Pred A ℓ₂) where
  open MemberAt _~_ Pre Post

  private
    variable
      x : ℕ
      a a′ a″ : A
      b b′ b″ : B
      Γ Γ′ Γ″ : List A

  Γ⦅⦆↘⇒Γ++⦅⦆↘ : {{All Post Γ′}} →
                Γ ⦅ x ⦆↘ b →
                Γ ++ Γ′ ⦅ x ⦆↘ b
  Γ⦅⦆↘⇒Γ++⦅⦆↘ (here {{AllPostΓ}} a~b) = here {{ListAll.++⁺ AllPostΓ it}} a~b
  Γ⦅⦆↘⇒Γ++⦅⦆↘ (there Γ⦅x⦆)            = there (Γ⦅⦆↘⇒Γ++⦅⦆↘ Γ⦅x⦆)

  Γ⦅⦆↘⇒++Γ⦅⦆↘ : All Pre Γ′ →
                Γ ⦅ x ⦆↘ b →
                Γ′ ++ Γ ⦅ length Γ′ + x ⦆↘ b
  Γ⦅⦆↘⇒++Γ⦅⦆↘ []                 Γ⦅x⦆ = Γ⦅x⦆
  Γ⦅⦆↘⇒++Γ⦅⦆↘ (a′Pre ∷ AllPreΓ′) Γ⦅x⦆ = there {{a′Pre}} (Γ⦅⦆↘⇒++Γ⦅⦆↘ AllPreΓ′ Γ⦅x⦆)
