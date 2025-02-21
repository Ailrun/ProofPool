module Calculus.SystemF.Typing where

open import Data.List using ([]; _∷_; _++_)
open import Data.Nat using (ℕ; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Calculus.SystemF.Syntax

infix   4 _⦂Ty∈_
infix   4 _⦂_∈_
infix   4 _⊢_⦂Ty
infix   4 ⊢_wf
infix   4 _⊢_⦂_

data _⦂Ty∈_ : ℕ → Ctx → Set where
  here    : ------------------
            0 ⦂Ty∈ kindTy ∷ Γ

  thereTy : a ⦂Ty∈ Γ →
            ----------------------
            suc a ⦂Ty∈ kindTy ∷ Γ

  thereTm : a ⦂Ty∈ Γ →
            ----------------
            a ⦂Ty∈ ty Q ∷ Γ

data _⦂_∈_ : ℕ → Ty → Ctx → Set where
  here    : -----------------
            0 ⦂ Q ∈ ty Q ∷ Γ

  thereTy : a ⦂ Q′ ∈ Γ →
            Q ≡ wkTy Q′ →
            -------------------
            a ⦂ Q ∈ kindTy ∷ Γ

  thereTm : a ⦂ Q ∈ Γ →
            ---------------------
            suc a ⦂ Q ∈ ty R ∷ Γ

data _⊢_⦂Ty : Ctx → Ty → Set where
  bot : ------------
        Γ ⊢ bot ⦂Ty

  _⇒_ : Γ ⊢ Q ⦂Ty →
        Γ ⊢ R ⦂Ty →
        --------------
        Γ ⊢ Q ⇒ R ⦂Ty

  ‼_  : kindTy ∷ Γ ⊢ Q ⦂Ty →
        ---------------------
        Γ ⊢ ‼ Q ⦂Ty

  #_  : a ⦂Ty∈ Γ →
        ------------
        Γ ⊢ # a ⦂Ty

data ⊢_wf : Ctx → Set where
  []   : --------
         ⊢ [] wf

  Ty∷_ : ⊢ Γ wf →
         ----------------
         ⊢ kindTy ∷ Γ wf

  _∷_  : Γ ⊢ Q ⦂Ty →
         ⊢ Γ wf →
         --------------
         ⊢ ty Q ∷ Γ wf

data _⊢_⦂_ : Ctx → Tm → Ty → Set where
  Λ‼_    : kindTy ∷ Γ ⊢ q ⦂ Q →
           ---------------------
           Γ ⊢ Λ‼ q ⦂ ‼ Q

  _$‼_/_ : Γ ⊢ q ⦂ ‼ R′ →
           Γ ⊢ Q ⦂Ty →
           R ≡ Ty[ Q / 0 ] R′ →
           ---------------------
           Γ ⊢ q $‼ Q ⦂ R

  λ⦂_∙_  : Γ ⊢ Q ⦂Ty →
           ty Q ∷ Γ ⊢ q ⦂ R →
           ---------------------
           Γ ⊢ λ⦂ Q ∙ q ⦂ Q ⇒ R

  _$_    : Γ ⊢ q ⦂ Q ⇒ R →
           Γ ⊢ r ⦂ Q →
           ----------------
           Γ ⊢ q $ r ⦂ R

  #_     : x ⦂ Q ∈ Γ →
           ------------
           Γ ⊢ # x ⦂ Q
