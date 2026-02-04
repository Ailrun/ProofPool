{-# OPTIONS --cubical-compatible --safe #-}
open import Agda.Primitive using (_⊔_)
open import Data.List as List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.Core using (REL)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Unary using (Pred)

module ClLib.MemberAt.Biconditioned
  {ℓa ℓb ℓ₀ ℓ₁ ℓ₂} {A : Set ℓa} {B : Set ℓb}
  (_~_ : REL A B ℓ₀) (Pre : Pred A ℓ₁) (Post : Pred A ℓ₂) where

private
  variable
    x : ℕ
    a a′ a″ : A
    b b′ b″ : B
    Γ Γ′ Γ″ : List A

infix   4 _⦅_⦆↘_
data _⦅_⦆↘_ : List A → ℕ → B → Set (ℓa ⊔ ℓb ⊔ ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂) where
  here  : {{All Post Γ}} →
          a ~ b →
          ----------------
          a ∷ Γ ⦅ 0 ⦆↘ b

  there : {{Pre a″}} →
          Γ ⦅ x ⦆↘ b →
          ---------------------
          a′ ∷ Γ ⦅ suc x ⦆↘ b

afterSome : All Pre Γ → a ~ b → {{All Post Γ′}} → Γ ++ a ∷ Γ′ ⦅ List.length Γ ⦆↘ b
afterSome []                a~b = here a~b
afterSome (a′Pre ∷ AllPreΓ) a~b = there {{a′Pre}} (afterSome AllPreΓ a~b)

size : Γ ⦅ x ⦆↘ b → ℕ
size (here a~b)   = 0
size (there Γ⦅x⦆) = suc (size Γ⦅x⦆)
