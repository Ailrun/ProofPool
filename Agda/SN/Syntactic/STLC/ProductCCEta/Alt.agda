{-# OPTIONS --safe #-}
module SN.Syntactic.STLC.ProductCCEta.Alt where

open import Agda.Primitive                                                   using (Level; lzero)
open import Data.Empty                                                       using (⊥)
open import Data.List                                                        using ([]; _∷_; _++_)
open import Data.List.Membership.Propositional                               using (_∈_)
open import Data.List.Relation.Unary.Any                                     using (here; there)
open import Data.Nat
open import Data.Nat.Induction
import Data.Nat.Properties                                                   as ℕ
open import Data.Product                                                     using (_×_; _,_; proj₁; proj₂; ∃-syntax; Σ-syntax)
open import Data.Sum                                                         as ⊎ using (_⊎_; inj₁; inj₂)
open import Data.Wrap                                                        using (Wrap; [_]; get)
open import Function                                                         using (case_of_; flip; id; Morphism; _on_; _∘_; _∋_)
open import Induction.WellFounded                                            using (Acc; acc; WellFounded; WfRec)
open import Relation.Binary                                                  using (REL; Rel; _=[_]⇒_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive            as Star using (Star; ε; _◅_; _◅◅_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties using (◅◅-assoc)
open import Relation.Binary.Construct.Closure.Transitive                     using (TransClosure; [_]; _∷_)
import Relation.Binary.Construct.Closure.Transitive                          as TransClosure
open import Relation.Binary.Construct.Union                                  using (_∪_)
open import Relation.Binary.PropositionalEquality                            using (_≡_; refl; cong; subst; sym; trans)
open import Relation.Unary                                                   using (Pred)

open import PPLib.Base
open import PPLib.Membership.Nth
open import Syntax.Church.STLC.WithProduct.Positive.Alt.Base         hiding (module Variables)
open import Syntax.Church.STLC.WithProduct.Positive.Alt.Substitution
open import SN.Syntactic.STLC.ProductCC.Alt                          using (`×χ-result; `×χ-result*)
import SN.Syntactic.STLC.ProductCC.Alt                               as β

variable
  ℓ ℓ′ ℓ″ ℓ‴ : Level

open Variables

module OpSem where
  ----------------------------------------------------------
  -- Weak Head Neutral Form
  ----------------------------------------------------------
  infix   4 _∈WHNe

  data _∈WHNe : Pred (Ex Γ A) lzero where
    `#_   : ∀ (x : A ∈ Γ) →
            ----------------
            `# x ∈WHNe

    _`∷ᵉ? : e ∈WHNe →
            ---------------
            e `∷ᵉ ee ∈WHNe

  ----------------------------------------------------------
  -- Single-step η-only Reduction
  ----------------------------------------------------------
  infix   4 _⟶′_
  infix   4 _⟶′ˢ_
  infix   4 _⟶′ᵉ_
  data _⟶′_ : Rel (Ex Γ A) lzero
  data _⟶′ˢ_ : Rel (Ex Γ A) lzero
  data _⟶′ᵉ_ : Rel (ExE Γ A B) lzero

  data _⟶′_ where
    `∷ᵉs : e ⟶′ˢ e′ →
           -----------
           e ⟶′ e′

    `λ_  : e ⟶′ e′ →
           --------------
           `λ e ⟶′ `λ e′

    _`,? : eₗ ⟶′ e′ₗ →
           ----------------------
           eₗ `, eᵣ ⟶′ e′ₗ `, eᵣ

    ?`,_ : eᵣ ⟶′ e′ᵣ →
           ----------------------
           eₗ `, eᵣ ⟶′ eₗ `, e′ᵣ

    `×η  : ∀ {e : Ex Γ (A `→ B)} →
           e ∈WHNe →
           ----------------------------------------
           e ⟶′ `λ (⟦ Wkᵛ ⟧ᵛ e `∷ᵉ -`$ (`# `!! 0))

  data _⟶′ˢ_ where
    _`∷ᵉ? : e ⟶′ˢ e′ →
            -----------------------
            e `∷ᵉ ee ⟶′ˢ e′ `∷ᵉ ee

    ?`∷ᵉ_ : ee ⟶′ᵉ ee′ →
            -----------------------
            e `∷ᵉ ee ⟶′ˢ e `∷ᵉ ee′

  data _⟶′ᵉ_ where
    -`$_      : e ⟶′ e′ →
                --------------------------
                -`$_ {B = B} e ⟶′ᵉ -`$ e′

    `let-`in_ : f ⟶′ˢ f′ →
                ---------------------------
                `let-`in f ⟶′ᵉ `let-`in f′

  infix   4 _⟶′*_
  _⟶′*_ : Rel (Ex Γ A) _
  _⟶′*_ = Star _⟶′_

  infix   4 _⟶ᶜ_
  _⟶ᶜ_ : Rel (Ex Γ A) lzero
  _⟶ᶜ_ = β._⟶_ ∪ _⟶′_

  module Properties where

open OpSem hiding (module Properties) public
open OpSem.Properties public

-- ⟶ᶜ*
-- v.s.
-- ⟶* × ⟶′*
--
-- SN-⟶ and SN-⟶′
--
-- inf : ⟶ ⟶ ⟶ ⟶′ ⟶′ ⟶ ...
