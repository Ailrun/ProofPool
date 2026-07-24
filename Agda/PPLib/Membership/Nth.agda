{-# OPTIONS --safe --without-K #-}
module PPLib.Membership.Nth where

open import Data.List                                 using ([]; _∷_)
open import Data.List.Membership.Propositional        using (_∈_)
open import Data.List.Relation.Unary.Any              using (here; there)
open import Data.Nat
open import Data.Unit                                 using (⊤; tt)
open import Reflection
-- open import Reflection.TypeChecking.Monad.Categorical using (monad)
open import Relation.Binary.PropositionalEquality     using (refl)

hereTerm : Term → Term
hereTerm x = con (quote here) (arg (arg-info visible (modality relevant quantity-ω)) x ∷ [])

thereTerm : Term → Term
thereTerm x = con (quote there) (arg (arg-info visible (modality relevant quantity-ω)) x ∷ [])

reflTerm : Term
reflTerm = con (quote refl) []

nthTerm : ℕ → Term
nthTerm zero    = hereTerm reflTerm
nthTerm (suc n) = thereTerm (nthTerm n)

macro
  nthMacro : ℕ → Term → TC ⊤
  nthMacro n hole = unify hole (nthTerm n)

infix  30 nthMacro
syntax nthMacro n = `!! n
