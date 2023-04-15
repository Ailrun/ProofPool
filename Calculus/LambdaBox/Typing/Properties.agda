{-# OPTIONS --safe #-}
module Calculus.LambdaBox.Typing.Properties where

open import Data.Nat as ℕ using (ℕ; suc; s≤s; _+_)
open import Data.Nat.Properties as ℕ
open import Data.List using (List; []; _∷_; _++_; length)

open import Calculus.LambdaBox.Syntax
open import Calculus.LambdaBox.Typing

∈-++ˡ : ∀ Γ₁ →
        x ⦂ S ∈ Γ₀ →
        ----------------------------
        length Γ₁ + x ⦂ S ∈ Γ₁ ++ Γ₀
∈-++ˡ {x = x} []      x∈
  rewrite ℕ.+-identityʳ x     = x∈
∈-++ˡ {x = x} (b ∷ Γ₁) x∈
  rewrite +-suc x (length Γ₁) = there (∈-++ˡ Γ₁ x∈)

∈-++ʳ : ∀ Γ₀ →
        x ⦂ S ∈ Γ₁ →
        -------------------
        x ⦂ S ∈ Γ₁ ++ Γ₀
∈-++ʳ Γ₀ here       = here
∈-++ʳ Γ₀ (there x∈) = there (∈-++ʳ Γ₀ x∈)

>∈-++⇒∈ : ∀ Γ₁ →
          length Γ₁ ℕ.> x →
          x ⦂ S ∈ Γ₁ ++ Γ₀ →
          -------------------
          x ⦂ S ∈ Γ₁
>∈-++⇒∈ (_ ∷ Γ₁) >x       here       = here
>∈-++⇒∈ (_ ∷ Γ₁) (s≤s >x) (there x∈) = there (>∈-++⇒∈ Γ₁ >x x∈)
