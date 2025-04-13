{-# OPTIONS --safe #-}
module Calculus.CBPV.Typing where

open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ; suc)
open import Data.Vec using (Vec; []; _∷_)
import Data.Vec as Vec
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Calculus.CBPV.Syntax
open Variable

infix   4 _⦂_∈_
infix   4 _⊢V_⦂_
infix   4 _⊢C_⦂_

data _⦂_∈_ : ℕ → TypeV → Context → Set where
  here  : --------------
          0 ⦂ A ∈ A ∷ Γ

  there : x ⦂ A ∈ Γ →
          ------------------
          suc x ⦂ A ∈ B ∷ Γ

data _⊢V_⦂_ : Context → TermV → TypeV → Set
data _⊢C_⦂_ : Context → TermC → TypeC → Set

data _⊢V_⦂_ where
  `#_    :  x ⦂ A ∈ Γ →
           --------------
            Γ ⊢V `# x ⦂ A

  `one   : ----------------
            Γ ⊢V `one ⦂ `1

  _`,_   :  Γ ⊢V U ⦂ A →
            Γ ⊢V V ⦂ B →
           ----------------------
            Γ ⊢V U `, V ⦂ A `× B

  ⦅_⦆`,_ : ∀ {n}
             {As : Vec TypeV n}
             {i : Fin n} →
            Γ ⊢V U ⦂ Vec.lookup As i →
           ----------------------------
            Γ ⊢V ⦅ i ⦆`, U ⦂ `Σ As

  `thunk :  Γ ⊢C L ⦂ S →
           ----------------------
            Γ ⊢V `thunk L ⦂ `↑ S

data _⊢C_⦂_ where
  `pm_as`one⇒_ :  Γ ⊢V U ⦂ `1 →
                  Γ ⊢C L ⦂ S →
                 --------------------------
                  Γ ⊢C `pm U as`one⇒ L ⦂ S

  `pm_as`,⇒_   :  Γ ⊢V U ⦂ A `× B →
                  B ∷ A ∷ Γ ⊢C L ⦂ S →
                 ------------------------
                  Γ ⊢C `pm U as`,⇒ L ⦂ S

  `pm_as∥_∥    : ∀ {n}
                   {As : Vec TypeV n}
                   {Ls : Vec TermC n} →
                  Γ ⊢V U ⦂ `Σ As →
                  (∀ {i} → Vec.lookup As i ∷ Γ ⊢C Vec.lookup Ls i ⦂ S) →
                 --------------------------------------------------------
                  Γ ⊢C `pm U as∥ Ls ∥ ⦂ S

  `force       :  Γ ⊢V U ⦂ `↑ S →
                 -------------------
                  Γ ⊢C `force U ⦂ S

  `λ_          :  A ∷ Γ ⊢C L ⦂ S →
                 --------------------
                  Γ ⊢C `λ L ⦂ A `→ S
  _`&_         :  Γ ⊢V U ⦂ A →
                  Γ ⊢C L ⦂ A `→ S →
                 -------------------
                  Γ ⊢C U `& L ⦂ S

  `λ∥_∥        : ∀ {n}
                   {Ss : Vec TypeC n}
                   {Ls : Vec TermC n} →
                  (∀ {i} → Γ ⊢C Vec.lookup Ls i ⦂ Vec.lookup Ss i) →
                 ----------------------------------------------------
                  Γ ⊢C `λ∥ Ls ∥ ⦂ `Π Ss
  ⦅_⦆`&_       : ∀ {n}
                   {Ss : Vec TypeC n}
                   {i : Fin n} →
                  Vec.lookup Ss i ≡ S →
                  Γ ⊢C L ⦂ `Π Ss →
                 -----------------------
                  Γ ⊢C ⦅ i ⦆`& L ⦂ S

  `return      :  Γ ⊢V U ⦂ A →
                 -----------------------
                  Γ ⊢C `return U ⦂ `↓ A
  _`to_        :  Γ ⊢C L ⦂ `↓ A →
                  A ∷ Γ ⊢C M ⦂ S →
                 ------------------
                  Γ ⊢C L `to M ⦂ S

  `print_and_  : ∀ c →
                  Γ ⊢C M ⦂ S →
                 -------------------------
                  Γ ⊢C `print c and M ⦂ S
