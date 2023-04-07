{-# OPTIONS --safe #-}
module Calculus.GeneralOpSem where

open import Agda.Primitive
open import Data.Nat as ℕ using (ℕ; suc; _+_)
open import Relation.Binary using (Rel)
open import Relation.Nullary using (yes; no)

infixr 25 wkidx[_↑_]_
infixr 25 idx[_/_]_along_

wkidx[_↑_]_ : ℕ → ℕ → ℕ → ℕ
wkidx[ n ↑ x ] y
  with y ℕ.≥? x
...  | no  _ = y
...  | yes _ = n + y

idx[_/_]_along_ : ∀ {ℓ} {A : Set ℓ} → A → ℕ → ℕ → (ℕ → A) → A
idx[ L / x ] y along `#_
  with y ℕ.≥? x
...  | no  _ = `# y
...  | yes _
    with y ℕ.≟ x
...    | no  _ = `# (ℕ.pred y)
...    | yes _ = L

module ⟶* {ℓ ℓ′} {A : Set ℓ} (_⟶_ : Rel A ℓ′) where
  open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star)
  open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_) public 

  infix   4 _⟶*_

  _⟶*_ = Star _⟶_

  ξ-of-⟶* : (f : A → A) →
            (∀ {L L′} → L ⟶ L′ → f L ⟶ f L′) →
            ∀ {L L′} → L ⟶* L′ → f L ⟶* f L′
  ξ-of-⟶* f ξ-rule ε           = ε
  ξ-of-⟶* f ξ-rule (L⟶ ◅ L′⟶*) = ξ-rule L⟶ ◅ ξ-of-⟶* f ξ-rule L′⟶*
