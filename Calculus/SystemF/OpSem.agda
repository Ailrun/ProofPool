module Calculus.SystemF.OpSem where

open import Calculus.GeneralOpSem
open import Calculus.SystemF.Syntax

infix   4 _⟶_

data _⟶_ : Tm → Tm → Set where
  ξ-Λ‼ : q ⟶ q′ →
         -------------
         Λ‼ q ⟶ Λ‼ q′

  ξ-$‼ : q ⟶ q′ →
         -----------------
         q $‼ Q ⟶ q′ $‼ Q

  β-‼  : ----------------------------
         (Λ‼ q) $‼ Q ⟶ [Ty Q / 0 ] q

  ξ-λ  : q ⟶ q′ →
         ---------------------
         λ⦂ Q ∙ q ⟶ λ⦂ Q ∙ q′

  ξ-$ˡ : q ⟶ q′ →
         ---------------
         q $ r ⟶ q′ $ r

  ξ-$ʳ : r ⟶ r′ →
         ---------------
         q $ r ⟶ q $ r′

  β-⇒  : -----------------------------
         (λ⦂ Q ∙ q) $ r ⟶ [ r / 0 ] q

open ⟶* _⟶_ public
