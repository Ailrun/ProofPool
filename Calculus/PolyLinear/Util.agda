module Calculus.PolyLinear.Util where

open import Agda.Primitive

case : ∀ {l m : Level} {A : Set l} {B : A → Set m}
       (x : A) →
       ((x : A) → B x) →
       ----------------------
       B x
case x f = f x
