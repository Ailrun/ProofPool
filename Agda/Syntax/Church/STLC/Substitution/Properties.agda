{-# OPTIONS --safe #-}
module Syntax.Church.STLC.Substitution.Properties where

open import Agda.Primitive                        using (lzero)
open import Data.List                             using (_∷_)
open import Data.List.Membership.Propositional    using (_∈_)
open import Data.List.Relation.Unary.Any          using (here; there)
open import Function                              using (_∘_)
open import Relation.Binary.PropositionalEquality hiding (J)

open import PPLib.Membership.Nth
open import Syntax.Church.STLC.Base              hiding (module Variables)
open import Syntax.Church.STLC.Substitution.Base

open Variables

----------------------------------------------------------
-- Useful Properties for Substitutions
----------------------------------------------------------

liftᵛ-preserves-qᵛ : ∀ (δ : Ext Γ Δ) →
                     liftᵛ∘ (qᵉᵉ δ) ≈ᵛ qᵉˢ_ {A = A} (liftᵛ∘ δ)
liftᵛ-preserves-qᵛ δ = liftᵛ-preserves-,ᵛ (Wkᵛ ∘ᵛ δ) (`!! 0)

instance
  ExtLiftId : VarSubLiftId ⦃ ExtVarSub ⦄ ⦃ SubVarSub ⦄
  ExtLiftId .liftᵛ-preserves-Idᵛ x = refl

  SubWkSpec : VarSubWkSpec ⦃ SubVarSub ⦄
  SubWkSpec .Wkᵛ-spec x = refl

  SubOutHeadSpec : VarSubOutHeadSpec ⦃ SubVarSub ⦄
  SubOutHeadSpec .R-headᵛ-spec = refl

  AppSubExtensional : ∀ {R}
                        ⦃ varSub : VarSubBase {lzero} R ⦄
                        ⦃ _ : RawVarSubOutHead ⦃ varSub ⦄ ⦄
                        ⦃ _ : RawVarSubLift ⦃ varSub ⦄ ⦃ SubVarSub ⦄ ⦄
                        ⦃ _ : RawVarSubApp ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄
                        ⦃ _ : VarSubAppExtensional ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄ →
                      VarSubAppExtensional ⦃ varSub ⦄ ⦃ SubVarSub ⦄ ⦃ SubVarSub ⦄
  AppSubExtensional .⟦-⟧ᵛ-extensional (`# x)   equiv = cong liftᵛ (equiv x)
  AppSubExtensional .⟦-⟧ᵛ-extensional (`λ M)   equiv = cong `λ_ (⟦-⟧ᵛ-extensional M (qᵛ-congᵛ equiv))
  AppSubExtensional .⟦-⟧ᵛ-extensional (M `$ N) equiv = cong₂ _`$_ (⟦-⟧ᵛ-extensional M equiv) (⟦-⟧ᵛ-extensional N equiv)

  AppSubCompositionalExt : ∀ {R}
                             ⦃ varSub : VarSubBase {lzero} R ⦄
                             ⦃ _ : RawVarSubOutHead ⦃ varSub ⦄ ⦄
                             ⦃ _ : RawVarSubLift ⦃ varSub ⦄ ⦃ SubVarSub ⦄ ⦄
                             ⦃ _ : RawVarSubApp ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄ →
                           VarSubAppCompositional ⦃ varSub ⦄ ⦃ SubVarSub ⦄ ⦃ ExtVarSub ⦄
  AppSubCompositionalExt .⟦-⟧ᵛ-compositional σ τ x = refl

  ExtLiftSubApp : VarSubLiftApp ⦃ ExtVarSub ⦄ ⦃ SubVarSub ⦄ ⦃ SubVarSub ⦄ ⦃ SubVarSub ⦄
  ExtLiftSubApp .liftᵛ-preserves-Appᵛ δ (`# x)   = refl
  ExtLiftSubApp .liftᵛ-preserves-Appᵛ δ (`λ M)   = cong `λ_ (trans (sym (⟦-⟧ᵛ-extensional M (liftᵛ-preserves-qᵛ δ))) (liftᵛ-preserves-Appᵛ (qᵉ δ) M))
  ExtLiftSubApp .liftᵛ-preserves-Appᵛ δ (M `$ N) = cong₂ _`$_ (liftᵛ-preserves-Appᵛ δ M) (liftᵛ-preserves-Appᵛ δ N)

  SubIdNoOpExtˡ : VarSubIdNoOpˡ ⦃ SubVarSub ⦄ ⦃ ExtVarSub ⦄ ⦃ SubVarSub ⦄
  SubIdNoOpExtˡ .Idᵛ-idˡ σ x = refl

  ExtIdNoOpSubˡ : VarSubIdNoOpˡ ⦃ ExtVarSub ⦄ ⦃ SubVarSub ⦄ ⦃ SubVarSub ⦄
  ExtIdNoOpSubˡ .Idᵛ-idˡ = λ σ x → cong liftᵛ (helper (σ x))
    where
      helper : ∀ (M : Tm Γ A) → ⟦ Idᵛ ⦃ ExtVarSub ⦄ ⟧ᵛ M ≡ M
      helper (`# x)   = refl
      helper (`λ M)   = cong `λ_ (trans (⟦-⟧ᵛ-extensional M qᵉᵉ-Idᵉ-id) (helper M))
      helper (M `$ N) = cong₂ _`$_ (helper M) (helper N)

  SubIdNoOpSubˡ : VarSubIdNoOpˡ ⦃ SubVarSub ⦄ ⦃ SubVarSub ⦄ ⦃ SubVarSub ⦄
  SubIdNoOpSubˡ .Idᵛ-idˡ = λ σ x → helper (σ x)
    where
      helper : ∀ (M : Tm Γ A) → ⟦ Idᵛ ⦃ SubVarSub ⦄ ⟧ᵛ M ≡ M
      helper M = trans (liftᵛ-preserves-Appᵛ (Idᵛ ⦃ ExtVarSub ⦄) M) (⟦Idᵛ⟧ᵛ≡liftᵛ M)

  IdNoOpSubʳ : ∀ {R}
                 ⦃ varSub : VarSubBase {lzero} R ⦄
                 ⦃ _ : RawVarSubOutHead ⦃ varSub ⦄ ⦄
                 ⦃ _ : RawVarSubLift ⦃ varSub ⦄ ⦃ SubVarSub ⦄ ⦄
                 ⦃ _ : RawVarSubApp ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄ →
               VarSubIdNoOpʳ ⦃ varSub ⦄ ⦃ SubVarSub ⦄ ⦃ SubVarSub ⦄
  IdNoOpSubʳ .Idᵛ-idʳ σ x = refl

instance
  ExtAppExtCompositionalSub : VarSubAppCompositional ⦃ ExtVarSub ⦄ ⦃ ExtVarSub ⦄ ⦃ SubVarSub ⦄
  ExtAppExtCompositionalSub .⟦-⟧ᵛ-compositional δ γ (`# x)   = refl
  ExtAppExtCompositionalSub .⟦-⟧ᵛ-compositional δ γ (`λ M)   = cong `λ_ (trans (⟦-⟧ᵛ-compositional (qᵉ δ) (qᵉ γ) M) (sym (⟦-⟧ᵛ-extensional M (qᵉ-distrib-∘ᵛ δ _))))
  ExtAppExtCompositionalSub .⟦-⟧ᵛ-compositional δ γ (M `$ N) = cong₂ _`$_ (⟦-⟧ᵛ-compositional δ γ M) (⟦-⟧ᵛ-compositional δ γ N)

qᵉ-distrib-∘ˢᵉ = qᵛ-distrib-∘ᵛ ⦃ ExtVarSub ⦄ ⦃ SubVarSub ⦄ ⦃ ExtVarSub ⦄ ⦃ SubVarSub ⦄

instance
  SubAppExtCompositionalSub : VarSubAppCompositional ⦃ SubVarSub ⦄ ⦃ ExtVarSub ⦄ ⦃ SubVarSub ⦄
  SubAppExtCompositionalSub .⟦-⟧ᵛ-compositional σ δ (`# x)   = refl
  SubAppExtCompositionalSub .⟦-⟧ᵛ-compositional σ δ (`λ M)   = cong `λ_ (trans (⟦-⟧ᵛ-compositional (qᵉ σ) (qᵉ δ) M) (sym (⟦-⟧ᵛ-extensional M (qᵉ-distrib-∘ˢᵉ σ _))))
  SubAppExtCompositionalSub .⟦-⟧ᵛ-compositional σ δ (M `$ N) = cong₂ _`$_ (⟦-⟧ᵛ-compositional σ δ M) (⟦-⟧ᵛ-compositional σ δ N)

qᵉ-distrib-∘ᵉˢ = qᵛ-distrib-∘ᵛ ⦃ ExtVarSub ⦄ ⦃ ExtVarSub ⦄ ⦃ SubVarSub ⦄ ⦃ SubVarSub ⦄

instance
  ExtAppSubCompositionalSub : VarSubAppCompositional ⦃ ExtVarSub ⦄ ⦃ SubVarSub ⦄ ⦃ SubVarSub ⦄
  ExtAppSubCompositionalSub .⟦-⟧ᵛ-compositional δ σ (`# x)   = refl
  ExtAppSubCompositionalSub .⟦-⟧ᵛ-compositional δ σ (`λ M)   = cong `λ_ (trans (⟦-⟧ᵛ-compositional (qᵉ δ) (qᵉ σ) M) (sym (⟦-⟧ᵛ-extensional M (qᵉ-distrib-∘ᵉˢ _ σ))))
  ExtAppSubCompositionalSub .⟦-⟧ᵛ-compositional δ σ (M `$ N) = cong₂ _`$_ (⟦-⟧ᵛ-compositional δ σ M) (⟦-⟧ᵛ-compositional δ σ N)

qᵉ-distrib-∘ˢ = qᵛ-distrib-∘ᵛ ⦃ ExtVarSub ⦄ ⦃ SubVarSub ⦄ ⦃ SubVarSub ⦄ ⦃ SubVarSub ⦄

instance
  SubAppSubCompositionalSub : VarSubAppCompositional ⦃ SubVarSub ⦄ ⦃ SubVarSub ⦄ ⦃ SubVarSub ⦄
  SubAppSubCompositionalSub .⟦-⟧ᵛ-compositional σ τ (`# x)   = refl
  SubAppSubCompositionalSub .⟦-⟧ᵛ-compositional σ τ (`λ M)   = cong `λ_ (trans (⟦-⟧ᵛ-compositional (qᵉ σ) (qᵉ τ) M) (sym (⟦-⟧ᵛ-extensional M (qᵉ-distrib-∘ˢ _ τ))))
  SubAppSubCompositionalSub .⟦-⟧ᵛ-compositional σ τ (M `$ N) = cong₂ _`$_ (⟦-⟧ᵛ-compositional σ τ M) (⟦-⟧ᵛ-compositional σ τ N)
