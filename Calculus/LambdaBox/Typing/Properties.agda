{-# OPTIONS --safe #-}
module Calculus.LambdaBox.Typing.Properties where

open import Data.Nat as ℕ using (ℕ; suc; s≤s)
open import Data.List using (List; []; _∷_; _++_; length)

open import Calculus.LambdaBox.Syntax
open import Calculus.LambdaBox.Typing

>∈-++⇒∈ : ∀ Γ₁ →
          length Γ₁ ℕ.> x →
          x ⦂ S ∈ Γ₁ ++ Γ₀ →
          -------------------
          x ⦂ S ∈ Γ₁
>∈-++⇒∈ (_ ∷ Γ₁) >x       here       = here
>∈-++⇒∈ (_ ∷ Γ₁) (s≤s >x) (there x∈) = there (>∈-++⇒∈ Γ₁ >x x∈)
