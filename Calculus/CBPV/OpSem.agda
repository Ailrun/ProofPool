{-# OPTIONS --safe #-}
module Calculus.CBPV.OpSem where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Vec using (Vec; []; _∷_)

open import Calculus.GeneralOpSem

open import Calculus.CBPV.Syntax

record WeakeningOp (X : Set) : Set where
  infixr 30 wk∥_↑_∥_
  field
    wk∥_↑_∥_ : ℕ → ℕ → X → X

  infixr 30 wk_
  wk_ = wk∥ 1 ↑ 0 ∥_

record SubstitutionOp (X : Set) : Set where
  infixr 30 ⟦_/_⟧_
  field
    ⟦_/_⟧_ : TermV → ℕ → X → X

  infixr 30 ⟦_0⟧_
  ⟦_0⟧_ = ⟦_/ 0 ⟧_

open WeakeningOp ⦃...⦄
open SubstitutionOp ⦃...⦄

instance
  WeakeningOpV : WeakeningOp TermV
  WeakeningOpC : WeakeningOp TermC
  WeakeningOpVecC : ∀ {n} → WeakeningOp (Vec TermC n)

  wk∥_↑_∥_ ⦃ WeakeningOpV ⦄ n x (`# y)      = `# (wkidx[ n ↑ x ] y)
  wk∥_↑_∥_ ⦃ WeakeningOpV ⦄ n x `one        = `one
  wk∥_↑_∥_ ⦃ WeakeningOpV ⦄ n x (U `, V)    = wk∥ n ↑ x ∥ U `, wk∥ n ↑ x ∥ V
  wk∥_↑_∥_ ⦃ WeakeningOpV ⦄ n x (⦅ i ⦆`, U) = ⦅ i ⦆`, wk∥ n ↑ x ∥ U
  wk∥_↑_∥_ ⦃ WeakeningOpV ⦄ n x (`thunk L)  = `thunk (wk∥ n ↑ x ∥ L)

  wk∥_↑_∥_ ⦃ WeakeningOpC ⦄ n x (`pm U as`one⇒ L) = `pm wk∥ n ↑ x ∥ U as`one⇒ wk∥ n ↑ x ∥ L
  wk∥_↑_∥_ ⦃ WeakeningOpC ⦄ n x (`pm U as`,⇒ L)   = `pm wk∥ n ↑ x ∥ U as`,⇒ wk∥ n ↑ suc (suc x) ∥ L
  wk∥_↑_∥_ ⦃ WeakeningOpC ⦄ n x (`pm U as∥ Ls ∥)  = `pm wk∥ n ↑ x ∥ U as∥ wk∥ n ↑ suc x ∥ Ls ∥
  wk∥_↑_∥_ ⦃ WeakeningOpC ⦄ n x (`force U)        = `force (wk∥ n ↑ x ∥ U)
  wk∥_↑_∥_ ⦃ WeakeningOpC ⦄ n x (`λ L)            = `λ wk∥ n ↑ suc x ∥ L
  wk∥_↑_∥_ ⦃ WeakeningOpC ⦄ n x (U `& L)          = wk∥ n ↑ x ∥ U `& wk∥ n ↑ x ∥ L
  wk∥_↑_∥_ ⦃ WeakeningOpC ⦄ n x `λ∥ Ls ∥          = `λ∥ wk∥ n ↑ x ∥ Ls ∥
  wk∥_↑_∥_ ⦃ WeakeningOpC ⦄ n x (⦅ i ⦆`& L)       = ⦅ i ⦆`& wk∥ n ↑ x ∥ L
  wk∥_↑_∥_ ⦃ WeakeningOpC ⦄ n x (`return U)       = `return (wk∥ n ↑ x ∥ U)
  wk∥_↑_∥_ ⦃ WeakeningOpC ⦄ n x (L `to M)         = wk∥ n ↑ x ∥ L `to wk∥ n ↑ suc x ∥ M
  wk∥_↑_∥_ ⦃ WeakeningOpC ⦄ n x (`print c and L)  = `print c and wk∥ n ↑ x ∥ L

  wk∥_↑_∥_ ⦃ WeakeningOpVecC ⦄ n x []       = []
  wk∥_↑_∥_ ⦃ WeakeningOpVecC ⦄ n x (L ∷ Ls) = wk∥ n ↑ x ∥ L ∷ wk∥ n ↑ x ∥ Ls

  SubstitutionOpV : SubstitutionOp TermV
  SubstitutionOpC : SubstitutionOp TermC
  SubstitutionOpVecC : ∀ {n} → SubstitutionOp (Vec TermC n)

  ⟦_/_⟧_ ⦃ SubstitutionOpV ⦄ U x (`# y)      = idx[ U / x ] y along `#_
  ⟦_/_⟧_ ⦃ SubstitutionOpV ⦄ U x `one        = `one
  ⟦_/_⟧_ ⦃ SubstitutionOpV ⦄ U x (V `, W)    = ⟦ U / x ⟧ V `, ⟦ U / x ⟧ W
  ⟦_/_⟧_ ⦃ SubstitutionOpV ⦄ U x (⦅ i ⦆`, V) = ⦅ i ⦆`, ⟦ U / x ⟧ V
  ⟦_/_⟧_ ⦃ SubstitutionOpV ⦄ U x (`thunk L)  = `thunk (⟦ U / x ⟧ L)

  ⟦_/_⟧_ ⦃ SubstitutionOpC ⦄ U x (`pm V as`one⇒ L) = `pm ⟦ U / x ⟧ V as`one⇒ ⟦ U / x ⟧ L
  ⟦_/_⟧_ ⦃ SubstitutionOpC ⦄ U x (`pm V as`,⇒ L)   = `pm ⟦ U / x ⟧ V as`,⇒ ⟦ U / suc (suc x) ⟧ L
  ⟦_/_⟧_ ⦃ SubstitutionOpC ⦄ U x (`pm V as∥ Ls ∥)  = `pm ⟦ U / x ⟧ V as∥ ⟦ U / suc x ⟧ Ls ∥
  ⟦_/_⟧_ ⦃ SubstitutionOpC ⦄ U x (`force V)        = `force (⟦ U / x ⟧ V)
  ⟦_/_⟧_ ⦃ SubstitutionOpC ⦄ U x (`λ L)            = `λ ⟦ U / suc x ⟧ L
  ⟦_/_⟧_ ⦃ SubstitutionOpC ⦄ U x (V `& L)          = ⟦ U / x ⟧ V `& ⟦ U / x ⟧ L
  ⟦_/_⟧_ ⦃ SubstitutionOpC ⦄ U x `λ∥ Ls ∥          = `λ∥ ⟦ U / x ⟧ Ls ∥
  ⟦_/_⟧_ ⦃ SubstitutionOpC ⦄ U x (⦅ i ⦆`& L)       = ⦅ i ⦆`& ⟦ U / x ⟧ L
  ⟦_/_⟧_ ⦃ SubstitutionOpC ⦄ U x (`return V)       = `return (⟦ U / x ⟧ V)
  ⟦_/_⟧_ ⦃ SubstitutionOpC ⦄ U x (L `to M)         = ⟦ U / x ⟧ L `to ⟦ U / suc x ⟧ M
  ⟦_/_⟧_ ⦃ SubstitutionOpC ⦄ U x (`print c and L)  = `print c and ⟦ U / x ⟧ L

  ⟦_/_⟧_ ⦃ SubstitutionOpVecC ⦄ U x []       = []
  ⟦_/_⟧_ ⦃ SubstitutionOpVecC ⦄ U x (L ∷ Ls) = ⟦ U / x ⟧ L ∷ ⟦ U / x ⟧ Ls
