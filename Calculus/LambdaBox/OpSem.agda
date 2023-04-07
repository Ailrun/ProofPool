------------------------------------------------------------
-- Dynamic Rules for DP Modal Calculus
------------------------------------------------------------

{-# OPTIONS --safe #-}
module Calculus.LambdaBox.OpSem where

open import Data.Nat using (ℕ; suc)

open import Calculus.GeneralOpSem
open import Calculus.LambdaBox.Syntax

data Value : Term → Set where
  `unit  : ------------
           Value `unit

  `box   : ∀ M →
           -------------------
           Value (`box M)

  `λ⦂_∙_ : ∀ S M →
           ------------------
           Value (`λ⦂ S ∙ M)

infix  25 wk[_↑¹_]_
infix  25 wk[_↑⁰_]_
infix  25 wk¹_
infix  25 wk⁰_
infix  25 [_/¹_]_
infix  25 [_/⁰_]_

wk[_↑¹_]_ : ℕ → ℕ → Term → Term
wk[ n ↑¹ u ] `unit = `unit
wk[ n ↑¹ u ] `box L = `box (wk[ n ↑¹ u ] L)
wk[ n ↑¹ u ] (`let-box L `in M) = `let-box wk[ n ↑¹ u ] L `in wk[ n ↑¹ suc u ] M
wk[ n ↑¹ u ] (`λ⦂ S ∙ L) = `λ⦂ S ∙ wk[ n ↑¹ u ] L
wk[ n ↑¹ u ] (L `$ M) = wk[ n ↑¹ u ] L `$ wk[ n ↑¹ u ] M
wk[ n ↑¹ u ] (`#¹ v) = `#¹ wkidx[ n ↑ u ] v
wk[ n ↑¹ u ] (`#⁰ y) = `#⁰ y

wk¹_ : Term → Term
wk¹_ = wk[ 1 ↑¹ 0 ]_

wk[_↑⁰_]_ : ℕ → ℕ → Term → Term
wk[ n ↑⁰ x ] `unit = `unit
wk[ n ↑⁰ x ] `box L = `box L
wk[ n ↑⁰ x ] (`let-box L `in M) = `let-box wk[ n ↑⁰ x ] L `in wk[ n ↑⁰ x ] M
wk[ n ↑⁰ x ] (`λ⦂ S ∙ L) = `λ⦂ S ∙ wk[ n ↑⁰ suc x ] L
wk[ n ↑⁰ x ] (L `$ M) = wk[ n ↑⁰ x ] L `$ wk[ n ↑⁰ x ] M
wk[ n ↑⁰ x ] (`#¹ v) = `#¹ v
wk[ n ↑⁰ x ] (`#⁰ y) = `#⁰ wkidx[ n ↑ x ] y

wk⁰_ : Term → Term
wk⁰_ = wk[ 1 ↑⁰ 0 ]_

[_/¹_]_ : Term → ℕ → Term → Term
[ L /¹ u ] `unit              = `unit
[ L /¹ u ] (`box M)           = `box ([ L /¹ u ] M)
[ L /¹ u ] (`let-box M `in N) = `let-box [ L /¹ u ] M `in [ wk¹ L /¹ suc u ] N
[ L /¹ u ] (`#¹ v)            = idx[ L / u ] v along `#¹_
[ L /¹ u ] (`#⁰ x)            = `#⁰ x
[ L /¹ u ] (`λ⦂ S ∙ M)        = `λ⦂ S ∙ [ L /¹ u ] M
[ L /¹ u ] (M `$ N)           = [ L /¹ u ] M `$ [ L /¹ u ] N

[_/⁰_]_ : Term → ℕ → Term → Term
[ L /⁰ x ] `unit              = `unit
[ L /⁰ x ] (`box M)           = `box M
[ L /⁰ x ] (`let-box M `in N) = `let-box [ L /⁰ x ] M `in [ wk¹ L /⁰ x ] N
[ L /⁰ x ] (`#¹ u)            = `#¹ u
[ L /⁰ x ] (`#⁰ y)            = idx[ L / x ] y along `#⁰_
[ L /⁰ x ] (`λ⦂ S ∙ M)        = `λ⦂ S ∙ [ wk⁰ L /⁰ suc x ] M
[ L /⁰ x ] (M `$ N)           = [ L /⁰ x ] M `$ [ L /⁰ x ] N

infix  4 _⟶_

data _⟶_ : Term → Term → Set where
  ξ-`let-box_`in- : L ⟶ L′ →
                    -------------------------------------
                    `let-box L `in M ⟶ `let-box L′ `in M

  β-`□            : -------------------------------------
                    `let-box `box L `in M ⟶ [ L /¹ 0 ] M

  ξ-_`$?          : L ⟶ L′ →
                    -----------------
                    L `$ M ⟶ L′ `$ M

  ξ-!_`$_         : Value L →
                    M ⟶ M′ →
                    -----------------
                    L `$ M ⟶ L `$ M′

  β-`→            : Value M →
                    --------------------------------
                    (`λ⦂ S ∙ L) `$ M ⟶ [ M /⁰ 0 ] L

open ⟶* _⟶_ public
