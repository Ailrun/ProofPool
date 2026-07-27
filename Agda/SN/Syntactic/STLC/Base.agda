{-# OPTIONS --safe #-}
module SN.Syntactic.STLC.Base where

open import Agda.Primitive        using (Level; lzero)
open import Data.List             using (_∷_)
open import Function              using (flip)
open import Induction.WellFounded using (Acc; acc; WellFounded)
open import Relation.Binary       using (Rel)
open import Relation.Unary        using (Pred)

open import Syntax.Church.STLC.Base         hiding (module Variables)
open import Syntax.Church.STLC.Substitution
import Syntax.Church.STLC.Alt.Base          as 𝒜
import Syntax.Church.STLC.Alt.Conversion    as 𝒜
import SN.Syntactic.STLC.Alt                as 𝒜

variable
  ℓ ℓ′ ℓ″ ℓ‴ : Level

open Variables

module OpSem where
  infix 4 _⟶_
  data _⟶_ : Rel (Tm Γ A) lzero where
    `λ_  : M ⟶ M′ →
           -------------
           `λ M ⟶ `λ M′

    _`$? : (M⟶M′ : M ⟶ M′) →
           ------------------
           M `$ N ⟶ M′ `$ N

    ?`$_ : (N⟶N′ : N ⟶ N′) →
           ------------------
           M `$ N ⟶ M `$ N′

    `→β  : ∀ {M : Tm (A ∷ Γ) B} {N : Tm Γ A} →
           ------------------------------------
           (`λ M) `$ N ⟶ ⟦ !ˢ N ⟧ᵛ M

  ----------------------------------------------------------
  -- Flipped Reductions
  ----------------------------------------------------------

  infix 4 _⟵_
  _⟵_ : Rel (Tm Γ A) _
  _⟵_ = flip _⟶_

  module Properties where
    convEx⟶  : ∀ {e e′ : 𝒜.Ex Γ A} →
               e 𝒜.⟶ e′ →
               𝒜.convEx e ⟶ 𝒜.convEx e′
    convEx⟶ᵉ : ∀ {ee ee′ : 𝒜.ExE Γ A B} {M : Tm Γ A} →
               ee 𝒜.⟶ᵉ ee′ →
               𝒜.convExE ee M ⟶ 𝒜.convExE ee′ M

    convEx⟶ (𝒜._`∷ᵉ? {ee = 𝒜.-`$ f} e⟶)     = convEx⟶ e⟶ `$?
    convEx⟶ (𝒜.?`∷ᵉ ee⟶)                    = convEx⟶ᵉ ee⟶
    convEx⟶ (𝒜.`λ e⟶)                       = `λ convEx⟶ e⟶
    convEx⟶ (𝒜.`→β {e = e} {f})
      rewrite 𝒜.convEx-preserves-⟦!ˢ-⟧ˢ e f = `→β

    convEx⟶ᵉ (𝒜.-`$ e⟶) = ?`$ (convEx⟶ e⟶)

    convTm⟶  : ∀ {M M′ : Tm Γ A} →
               M ⟶ M′ →
               𝒜.convTm M 𝒜.⟶ 𝒜.convTm M′
    convTm⟶ (`λ M⟶)                         = 𝒜.`λ convTm⟶ M⟶
    convTm⟶ (M⟶ `$?)                        = convTm⟶ M⟶ 𝒜.`∷ᵉ?
    convTm⟶ (?`$ M⟶)                        = 𝒜.?`∷ᵉ (𝒜.-`$ convTm⟶ M⟶)
    convTm⟶ (`→β {M = M} {N})
      rewrite 𝒜.convTm-preserves-⟦!ˢ-⟧ˢ M N = 𝒜.`→β

open OpSem hiding (module Properties)
open OpSem.Properties

module AccessibilitySN where
  infix   4 _∈sn
  _∈sn : Pred (Tm Γ A) _
  _∈sn = Acc _⟵_

open AccessibilitySN

strong-normalization : ∀ (M : Tm Γ A) →
                       M ∈sn
strong-normalization M = lemma (𝒜.strong-normalization (𝒜.convTm M))
  where
    lemma : ∀ {Γ A} {M : Tm Γ A} →
            𝒜.convTm M 𝒜.∈sn →
            M ∈sn
    lemma (acc erec) = acc (λ M⟶ → lemma (erec (convTm⟶ M⟶)))

strong-normalization′ : ∀ {Γ A} →
                        WellFounded (_⟵_ {Γ} {A})
strong-normalization′ = strong-normalization
