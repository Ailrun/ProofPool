{-# OPTIONS --safe #-}
module Calculus.CBPV.AbstractMachine where

open import Data.Empty using (⊥)
open import Data.Fin using (Fin; toℕ)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; nothing; just)
import Data.Maybe as Maybe
open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)

open import Calculus.CBPV.Syntax
open import Calculus.CBPV.OpSem

CodeC : Set
data InstC : Set
data InstV : Set

CodeC = List InstC

data InstC where
  `push    : InstV → InstC
  `pop     : InstC
  `pushtag : ℕ → InstC
  `poptag  : InstC
  `move    : InstV → InstC
  `print   : ℕ → InstC
  `pm-one  : CodeC → InstC
  `pm-`,   : CodeC → InstC
  `pm-⦅⦆`, : List CodeC → InstC
  `switch  : List CodeC → InstC
  `jump    : InstV → InstC
  `return  : InstV → InstC
  `readret : InstC

data InstV where
  -- from a register
  `of         : ℕ → InstV
  `one        : InstV
  _`,_        : InstV → InstV → InstV
  ⦅_⦆`,_      : ℕ → InstV → InstV
  `closure-of : CodeC → InstV

module _ where
  open Data.Maybe

  compileC  : TermC → Maybe CodeC
  compileCs : ∀ {n} → Vec TermC n → Maybe (List CodeC)
  compileV  : TermV → Maybe InstV

  compileC (`pm U as`one⇒ L) = do
    Uc ← compileV U
    Lc ← compileC L
    just (`move Uc ∷ `pm-one Lc ∷ [])
  compileC (`pm U as`,⇒ L) = do
    Uc ← compileV U
    Lc ← compileC L
    just (`move Uc ∷ `pm-`, Lc ∷ [])
  compileC `pm U as∥ Ls ∥ = do
    Uc ← compileV U
    Lsc ← compileCs Ls
    just (`move Uc ∷ `pm-⦅⦆`, Lsc ∷ [])
  compileC (`force U) = do
    Uc ← compileV U
    just (`jump Uc ∷ [])
  compileC (`λ L) = do
    Lc ← compileC L
    just (`pop ∷ Lc)
  compileC (U `& L) = do
    Uc ← compileV U
    Lc ← compileC L
    just (`push Uc ∷ Lc)
  compileC `λ∥ Ls ∥ = do
    Lsc ← compileCs Ls
    just (`poptag ∷ `switch Lsc ∷ [])
  compileC (⦅ i ⦆`& L) = do
    Lc ← compileC L
    just (`pushtag (toℕ i) ∷ Lc)
  compileC (`return U) = do
    Uc ← compileV U
    just (`return Uc ∷ [])
  compileC (L `to M)   = do
    Lc ← compileC L
    Mc ← compileC M
    just (Lc ++ `readret ∷ Mc)
  compileC (`print c and L) = do
    Lc ← compileC L
    just (`print c ∷ Lc)

  compileCs [] = just []
  compileCs (L ∷ Ls) = do
    Lc ← compileC L
    Lsc ← compileCs Ls
    just (Lc ∷ Lsc)

  compileV (`# x) = just (`of x)
  compileV `one = just `one
  compileV (U `, V) = do
    Uc ← compileV U
    Vc ← compileV V
    just (Uc `, Vc)
  compileV (⦅ i ⦆`, U) = do
    Uc ← compileV U
    just (⦅ toℕ i ⦆`, Uc)
  compileV (`thunk L) = do
    Lc ← compileC L
    just (`closure-of Lc)
