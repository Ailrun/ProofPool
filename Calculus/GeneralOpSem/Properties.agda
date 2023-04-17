{-# OPTIONS --safe #-}
module Calculus.GeneralOpSem.Properties where

open import Agda.Primitive
open import Data.Nat as ℕ using (ℕ; suc; s≤s; _+_)
import Data.Nat.Properties as ℕ
open import Data.Product as × using (proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)
open import Relation.Nullary.Decidable using (dec-yes; dec-no)

open import Calculus.GeneralOpSem

wkidx[↑suc]suc≡sucwkidx[↑] : ∀ n x y →
                             wkidx[ n ↑ suc x ] suc y ≡ suc (wkidx[ n ↑ x ] y)
wkidx[↑suc]suc≡sucwkidx[↑] n x y
  with suc y ℕ.≥? suc x
...  | yes (s≤s y≥x)
    rewrite proj₂ (dec-yes (_ ℕ.≥? _) y≥x)            = ℕ.+-suc n y
...  | no  y≱x
    rewrite dec-no (_ ℕ.≥? _) (λ y≥x → y≱x (s≤s y≥x)) = refl
