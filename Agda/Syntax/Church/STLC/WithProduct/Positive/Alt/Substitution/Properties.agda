{-# OPTIONS --safe #-}
module Syntax.Church.STLC.WithProduct.Positive.Alt.Substitution.Properties where

open import Agda.Primitive                                                   using (lzero)
open import Data.List                                                        using ([]; _∷_)
open import Data.List.Membership.Propositional                               using (_∈_)
open import Data.List.Relation.Unary.Any                                     using (here; there)
open import Function                                                         using (id; it; _∘_; _∋_)
open import Relation.Binary                                                  using ( IsEquivalence; Reflexive
                                                                                   ; REL; Rel; Setoid
                                                                                   ; Symmetric; Transitive
                                                                                   ; _Preserves_⟶_; _Preserves₂_⟶_⟶_
                                                                                   )
open import Relation.Binary.Construct.Closure.ReflexiveTransitive            using (Star; ε; _◅_; _◅◅_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties using (gmap-cong; gmap-id; gmap-◅◅)
open import Relation.Binary.PropositionalEquality                            using ( _≡_; refl
                                                                                   ; cong; cong₂; sym; trans
                                                                                   ; module ≡-Reasoning)

open import PPLib.Base
open import PPLib.Membership.Nth
open import Syntax.Church.STLC.WithProduct.Positive.Alt.Base              hiding (module Variables)
open import Syntax.Church.STLC.WithProduct.Positive.Alt.Substitution.Base

open Variables

`++ˢ-⟦-⟧ᵛ-commute : ∀ {R}
                      ⦃ varSub : VarSubBase {lzero} R ⦄
                      ⦃ _ : RawVarSubOutHead ⦃ varSub ⦄ ⦄
                      ⦃ _ : RawVarSubLift ⦃ varSub ⦄ ⦃ SubVarSub ⦄ ⦄
                      ⦃ _ : RawVarSubApp ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄
                      (δ : VarSub ⦃ varSub ⦄ Δ Γ) (e : Ex Γ A) (es : ExEs Γ A B) →
                    ⟦ δ ⟧ᵛ (e `++ˢ es) ≡ ⟦ δ ⟧ᵛ e `++ˢ ⟦ δ ⟧ᵛ* es
`++ˢ-⟦-⟧ᵛ-commute _ _ ε        = refl
`++ˢ-⟦-⟧ᵛ-commute _ _ (_ ◅ es) = `++ˢ-⟦-⟧ᵛ-commute _ (_ `∷ᵉ _) es

◅◅-⟦-⟧ᵛ-commute : ∀ {R}
                    ⦃ varSub : VarSubBase {lzero} R ⦄
                    ⦃ _ : RawVarSubOutHead ⦃ varSub ⦄ ⦄
                    ⦃ _ : RawVarSubLift ⦃ varSub ⦄ ⦃ SubVarSub ⦄ ⦄
                    ⦃ _ : RawVarSubApp ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄
                    (δ : VarSub ⦃ varSub ⦄ Δ Γ) (es₀ : ExEs Γ A B) (es₁ : ExEs Γ B C) →
                  ⟦ δ ⟧ᵛ* (es₀ ◅◅ es₁) ≡ ⟦ δ ⟧ᵛ* es₀ ◅◅ ⟦ δ ⟧ᵛ* es₁
◅◅-⟦-⟧ᵛ-commute δ = gmap-◅◅ id (RawAppSub.forExE δ)

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
  AppSubExtensional ⦃ varSub = varSub ⦄ = record { ⟦-⟧ᵛ-extensional = forEx }
    module AppSubExtensional where
      forEx  : ∀ (e : Ex Γ A) →
               (λ (δ : VarSub Δ Γ) → ⟦ δ ⟧ᵛ e) Preserves (_≈ᵛ_ ⦃ varSub ⦄) ⟶ _≡_
      forExE : ∀ (ee : ExE Γ A B) →
               (λ (δ : VarSub Δ Γ) → RawAppSub.forExE δ ee) Preserves (_≈ᵛ_ ⦃ varSub ⦄) ⟶ _≡_

      forEx (`# x)     equiv = cong liftᵛ (equiv x)
      forEx (`λ e)     equiv = cong `λ_ (forEx e (qᵛ-congᵛ equiv))
      forEx (e `, f)   equiv = cong₂ _`,_ (forEx e equiv) (forEx f equiv)
      forEx (e `∷ᵉ ee) equiv = cong₂ _`∷ᵉ_ (forEx e equiv) (forExE ee equiv)

      forExE (-`$ f)      equiv = cong -`$_ (forEx f equiv)
      forExE (`let-`in f) equiv = cong `let-`in_ (forEx f (qᵛ-congᵛ (qᵛ-congᵛ equiv)))

  AppSubCompositionalExt : ∀ {R}
                             ⦃ varSub : VarSubBase {lzero} R ⦄
                             ⦃ _ : RawVarSubOutHead ⦃ varSub ⦄ ⦄
                             ⦃ _ : RawVarSubLift ⦃ varSub ⦄ ⦃ SubVarSub ⦄ ⦄
                             ⦃ _ : RawVarSubApp ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄ →
                           VarSubAppCompositional ⦃ varSub ⦄ ⦃ SubVarSub ⦄ ⦃ ExtVarSub ⦄
  AppSubCompositionalExt .⟦-⟧ᵛ-compositional σ τ x = refl

  ExtLiftSubApp : VarSubLiftApp ⦃ ExtVarSub ⦄ ⦃ SubVarSub ⦄ ⦃ SubVarSub ⦄ ⦃ SubVarSub ⦄
  ExtLiftSubApp = record { liftᵛ-preserves-Appᵛ = forEx }
    module ExtLiftSubApp where
      forEx  : ∀ (δ : Ext Δ Γ) (e : Ex Γ A) →
               ⟦ liftᵛ∘ ⦃ _ ⦄ ⦃ SubVarSub ⦄ δ ⟧ᵛ e ≡ ⟦ δ ⟧ᵛ e
      forExE : ∀ (δ : Ext Δ Γ) (ee : ExE Γ A B) →
               RawAppSub.forExE (liftᵛ∘ ⦃ _ ⦄ ⦃ SubVarSub ⦄ δ) ee ≡ RawAppSub.forExE δ ee

      forEx δ (`# x)     = refl
      forEx δ (`λ e)     = cong `λ_ (trans (sym (⟦-⟧ᵛ-extensional e (liftᵛ-preserves-qᵛ δ))) (forEx (qᵉ δ) e))
      forEx δ (e `, f)   = cong₂ _`,_ (forEx δ e) (forEx δ f)
      forEx δ (e `∷ᵉ ee) = cong₂ _`∷ᵉ_ (forEx δ e) (forExE δ ee)

      forExE δ (-`$ f)      = cong -`$_ (forEx δ f)
      forExE δ (`let-`in f) = cong `let-`in_ (trans (sym (⟦-⟧ᵛ-extensional f (transᵛ (liftᵛ-preserves-qᵛ (qᵉ δ)) (qᵛ-congᵛ (liftᵛ-preserves-qᵛ δ))))) (forEx (qᵉ qᵉ δ) f))

  SubIdNoOpExtˡ : VarSubIdNoOpˡ ⦃ SubVarSub ⦄ ⦃ ExtVarSub ⦄ ⦃ SubVarSub ⦄
  SubIdNoOpExtˡ .Idᵛ-idˡ σ x = refl

  ExtIdNoOpSubˡ : VarSubIdNoOpˡ ⦃ ExtVarSub ⦄ ⦃ SubVarSub ⦄ ⦃ SubVarSub ⦄
  ExtIdNoOpSubˡ = record { Idᵛ-idˡ = λ σ x → cong liftᵛ (forEx (σ x)) }
    module ExtIdNoOpSubˡ where
      forEx  : ∀ (e : Ex Γ A) → ⟦ Idᵛ ⦃ ExtVarSub ⦄ ⟧ᵛ e ≡ e
      forExE : ∀ (ee : ExE Γ A B) → RawAppSub.forExE (Idᵛ ⦃ ExtVarSub ⦄) ee ≡ ee

      forEx (`# x)     = refl
      forEx (`λ e)     = cong `λ_ (trans (⟦-⟧ᵛ-extensional e qᵉᵉ-preserves-Idᵛ) (forEx e))
      forEx (e `, f)   = cong₂ _`,_ (forEx e) (forEx f)
      forEx (e `∷ᵉ ee) = cong₂ _`∷ᵉ_ (forEx e) (forExE ee)

      forExE (-`$ f)      = cong -`$_ (forEx f)
      forExE (`let-`in f) = cong `let-`in_ (trans (⟦-⟧ᵛ-extensional f qᵉᵉ⟦ _ ∷ _ ∷ [] ⟧-preserves-Idᵛ) (forEx f))

  SubIdNoOpSubˡ : VarSubIdNoOpˡ ⦃ SubVarSub ⦄ ⦃ SubVarSub ⦄ ⦃ SubVarSub ⦄
  SubIdNoOpSubˡ .Idᵛ-idˡ = λ σ x → helper (σ x)
    where
      helper : ∀ (e : Ex Γ A) → ⟦ Idᵛ ⦃ SubVarSub ⦄ ⟧ᵛ e ≡ e
      helper e = trans (liftᵛ-preserves-Appᵛ ⦃ ExtVarSub ⦄ Idᵛ e) (⟦Idᵛ⟧ᵛ≡liftᵛ e)

  IdNoOpSubʳ : ∀ {R}
                 ⦃ varSub : VarSubBase {lzero} R ⦄
                 ⦃ _ : RawVarSubOutHead ⦃ varSub ⦄ ⦄
                 ⦃ _ : RawVarSubLift ⦃ varSub ⦄ ⦃ SubVarSub ⦄ ⦄
                 ⦃ _ : RawVarSubApp ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄ →
               VarSubIdNoOpʳ ⦃ varSub ⦄ ⦃ SubVarSub ⦄ ⦃ SubVarSub ⦄
  IdNoOpSubʳ .Idᵛ-idʳ σ x = refl

instance
  ExtAppExtCompositionalSub : VarSubAppCompositional ⦃ ExtVarSub ⦄ ⦃ ExtVarSub ⦄ ⦃ SubVarSub ⦄
  ExtAppExtCompositionalSub = record { ⟦-⟧ᵛ-compositional = forEx }
    module ExtAppExtCompositionalSub where
      forEx  : ∀ (δ : Ext Ψ Δ) (γ : Ext Δ Γ) (e : Ex Γ A) →
               ⟦ δ ⟧ᵛ (⟦ γ ⟧ᵛ e) ≡ ⟦ δ ∘ᵛ γ ⟧ᵛ e
      forExE : ∀ (δ : Ext Ψ Δ) (γ : Ext Δ Γ) (ee : ExE Γ A B) →
               RawAppSub.forExE δ (RawAppSub.forExE γ ee) ≡ RawAppSub.forExE (δ ∘ᵛ γ) ee

      forEx δ γ (`# x)     = refl
      forEx δ γ (`λ e)     = cong `λ_ (trans (forEx (qᵉ δ) (qᵉ γ) e) (sym (⟦-⟧ᵛ-extensional e (qᵛ-distrib-∘ᵛ δ γ))))
      forEx δ γ (e `, f)   = cong₂ _`,_ (forEx δ γ e) (forEx δ γ f)
      forEx δ γ (e `∷ᵉ ee) = cong₂ _`∷ᵉ_ (forEx δ γ e) (forExE δ γ ee)

      forExE δ γ (-`$ f)      = cong -`$_ (forEx δ γ f)
      forExE δ γ (`let-`in f) = cong `let-`in_ (trans (forEx (qᵉ qᵉ δ) (qᵉ qᵉ γ) f) (sym (⟦-⟧ᵛ-extensional f (qᵛ⟦ _ ∷ _ ∷ [] ⟧-distrib-∘ᵛ δ γ))))

instance
  SubAppExtCompositionalSub : VarSubAppCompositional ⦃ SubVarSub ⦄ ⦃ ExtVarSub ⦄ ⦃ SubVarSub ⦄
  SubAppExtCompositionalSub = record { ⟦-⟧ᵛ-compositional = forEx }
    module SubAppExtCompositionalSub where
      forEx  : ∀ (σ : Sub Ψ Δ) (δ : Ext Δ Γ) (e : Ex Γ A) →
               ⟦ σ ⟧ᵛ (⟦ δ ⟧ᵛ e) ≡ ⟦ σ ∘ᵛ δ ⟧ᵛ e
      forExE : ∀ (σ : Sub Ψ Δ) (δ : Ext Δ Γ) (ee : ExE Γ A B) →
               RawAppSub.forExE σ (RawAppSub.forExE δ ee) ≡ RawAppSub.forExE (σ ∘ᵛ δ) ee

      forEx σ δ (`# x)     = refl
      forEx σ δ (`λ e)     = cong `λ_ (trans (forEx (qᵉ σ) (qᵉ δ) e) (sym (⟦-⟧ᵛ-extensional e (qᵛ-distrib-∘ᵛ σ δ))))
      forEx σ δ (e `, f)   = cong₂ _`,_ (forEx σ δ e) (forEx σ δ f)
      forEx σ δ (e `∷ᵉ ee) = cong₂ _`∷ᵉ_ (forEx σ δ e) (forExE σ δ ee)

      forExE σ δ (-`$ f)      = cong -`$_ (forEx σ δ f)
      forExE σ δ (`let-`in f) = cong `let-`in_ (trans (forEx (qᵉ qᵉ σ) (qᵉ qᵉ δ) f) (sym (⟦-⟧ᵛ-extensional f (qᵛ⟦ _ ∷ _ ∷ [] ⟧-distrib-∘ᵛ σ δ))))

instance
  ExtAppSubCompositionalSub : VarSubAppCompositional ⦃ ExtVarSub ⦄ ⦃ SubVarSub ⦄ ⦃ SubVarSub ⦄
  ExtAppSubCompositionalSub = record { ⟦-⟧ᵛ-compositional = forEx }
    module ExtAppSubCompositionalSub where
      forEx  : ∀ (δ : Ext Ψ Δ) (σ : Sub Δ Γ) (e : Ex Γ A) →
               ⟦ δ ⟧ᵛ (⟦ σ ⟧ᵛ e) ≡ ⟦ δ ∘ᵛ σ ⟧ᵛ e
      forExE : ∀ (δ : Ext Ψ Δ) (σ : Sub Δ Γ) (ee : ExE Γ A B) →
               RawAppSub.forExE δ (RawAppSub.forExE σ ee) ≡ RawAppSub.forExE (δ ∘ᵛ σ) ee

      forEx δ σ (`# x)     = refl
      forEx δ σ (`λ e)     = cong `λ_ (trans (forEx (qᵉ δ) (qᵉ σ) e) (sym (⟦-⟧ᵛ-extensional e (qᵛ-distrib-∘ᵛ δ σ))))
      forEx δ σ (e `, f)   = cong₂ _`,_ (forEx δ σ e) (forEx δ σ f)
      forEx δ σ (e `∷ᵉ ee) = cong₂ _`∷ᵉ_ (forEx δ σ e) (forExE δ σ ee)

      forExE δ σ (-`$ f)      = cong -`$_ (forEx δ σ f)
      forExE δ σ (`let-`in f) = cong `let-`in_ (trans (forEx (qᵉ qᵉ δ) (qᵉ qᵉ σ) f) (sym (⟦-⟧ᵛ-extensional f (qᵛ⟦ _ ∷ _ ∷ [] ⟧-distrib-∘ᵛ δ σ))))

instance
  SubAppSubCompositionalSub : VarSubAppCompositional ⦃ SubVarSub ⦄ ⦃ SubVarSub ⦄ ⦃ SubVarSub ⦄
  SubAppSubCompositionalSub = record { ⟦-⟧ᵛ-compositional = forEx }
    module SubAppSubCompositionalSub where
      forEx  : ∀ (σ : Sub Ψ Δ) (τ : Sub Δ Γ) (e : Ex Γ A) →
               ⟦ σ ⟧ᵛ (⟦ τ ⟧ᵛ e) ≡ ⟦ σ ∘ᵛ τ ⟧ᵛ e
      forExE : ∀ (σ : Sub Ψ Δ) (τ : Sub Δ Γ) (ee : ExE Γ A B) →
               RawAppSub.forExE σ (RawAppSub.forExE τ ee) ≡ RawAppSub.forExE (σ ∘ᵛ τ) ee

      forEx σ τ (`# x)     = refl
      forEx σ τ (`λ e)     = cong `λ_ (trans (forEx (qᵉ σ) (qᵉ τ) e) (sym (⟦-⟧ᵛ-extensional e (qᵛ-distrib-∘ᵛ σ τ))))
      forEx σ τ (e `, f)   = cong₂ _`,_ (forEx σ τ e) (forEx σ τ f)
      forEx σ τ (e `∷ᵉ ee) = cong₂ _`∷ᵉ_ (forEx σ τ e) (forExE σ τ ee)

      forExE σ τ (-`$ f)      = cong -`$_ (forEx σ τ f)
      forExE σ τ (`let-`in f) = cong `let-`in_ (trans (forEx (qᵉ qᵉ σ) (qᵉ qᵉ τ) f) (sym (⟦-⟧ᵛ-extensional f (qᵛ⟦ _ ∷ _ ∷ [] ⟧-distrib-∘ᵛ σ τ))))

----------------------------------------------------------
-- Other Useful Properties for Extensions/Substitutions
----------------------------------------------------------

liftᵛ-preserves-forExE : (δ : Ext Δ Γ) (ee : ExE Γ A B) →
                         -----------------------------------------------------------------------------------
                         RawAppSub.forExE (liftᵛ∘ ⦃ ExtVarSub ⦄ ⦃ SubVarSub ⦄ δ) ee ≡ RawAppSub.forExE δ ee
liftᵛ-preserves-forExE δ (-`$ f)      = cong -`$_ (liftᵛ-preserves-Appᵛ δ f)
liftᵛ-preserves-forExE δ (`let-`in f) = cong `let-`in_ (trans (sym (⟦-⟧ᵛ-extensional f (transᵛ (liftᵛ-preserves-qᵛ (qᵉ δ)) (qᵛ-congᵛ (liftᵛ-preserves-qᵛ δ))))) (liftᵛ-preserves-Appᵛ (qᵉ qᵉ δ) f))

liftᵛ-preserves-Appᵛ* : (δ : Ext Δ Γ) (es : ExEs Γ A B) →
                        -----------------------------------------------------------
                        ⟦ liftᵛ∘ ⦃ ExtVarSub ⦄ ⦃ SubVarSub ⦄ δ ⟧ᵛ* es ≡ ⟦ δ ⟧ᵛ* es
liftᵛ-preserves-Appᵛ* δ = gmap-cong id (RawAppSub.forExE (liftᵛ∘ δ)) (RawAppSub.forExE δ) (liftᵛ-preserves-forExE δ)

forExE-Idᵛ≡id : ∀ {R}
                  ⦃ varSub : VarSubBase {lzero} R ⦄
                  ⦃ _ : RawVarSubId ⦃ varSub ⦄ ⦄
                  ⦃ _ : RawVarSubOutHead ⦃ varSub ⦄ ⦄
                  ⦃ _ : RawVarSubLift ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦄
                  ⦃ _ : RawVarSubLift ⦃ varSub ⦄ ⦃ SubVarSub ⦄ ⦄
                  ⦃ _ : RawVarSubApp ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄
                  ⦃ _ : RawVarSubApp ⦃ varSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄
                  ⦃ _ : VarSubWkSpec ⦃ varSub ⦄ ⦄
                  ⦃ _ : VarSubOutHeadSpec ⦃ varSub ⦄ ⦄
                  ⦃ _ : VarSubIdNoOpˡ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄
                  ⦃ _ : VarSubIdNoOpˡ ⦃ varSub ⦄ ⦃ SubVarSub ⦄ ⦃ SubVarSub ⦄ ⦄
                  ⦃ _ : VarSubIdNoOpʳ ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄
                  ⦃ _ : VarSubIdNoOpʳ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄
                  ⦃ _ : VarSubAppExtensional ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄ →
                (ee : ExE Γ A B) →
                -------------------------------------------------------------
                RawAppSub.forExE (Idᵛ ⦃ varSub ⦄) ee ≡ ee
forExE-Idᵛ≡id            (-`$ f)      = cong -`$_ (⟦Idᵛ⟧ᵛ≡liftᵛ f)
forExE-Idᵛ≡id ⦃ varSub ⦄ (`let-`in f) = cong `let-`in_ (trans (⟦-⟧ᵛ-extensional f (transᵛ (qᵛ-congᵛ qᵛ-preserves-Idᵛ) qᵛ-preserves-Idᵛ)) (⟦Idᵛ⟧ᵛ≡liftᵛ f))

⟦Idᵛ⟧ᵛ*≡id : ∀ {R}
               ⦃ varSub : VarSubBase {lzero} R ⦄
               ⦃ _ : RawVarSubId ⦃ varSub ⦄ ⦄
               ⦃ _ : RawVarSubOutHead ⦃ varSub ⦄ ⦄
               ⦃ _ : RawVarSubLift ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦄
               ⦃ _ : RawVarSubLift ⦃ varSub ⦄ ⦃ SubVarSub ⦄ ⦄
               ⦃ _ : RawVarSubApp ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄
               ⦃ _ : RawVarSubApp ⦃ varSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄
               ⦃ _ : VarSubWkSpec ⦃ varSub ⦄ ⦄
               ⦃ _ : VarSubOutHeadSpec ⦃ varSub ⦄ ⦄
               ⦃ _ : VarSubIdNoOpˡ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄
               ⦃ _ : VarSubIdNoOpˡ ⦃ varSub ⦄ ⦃ SubVarSub ⦄ ⦃ SubVarSub ⦄ ⦄
               ⦃ _ : VarSubIdNoOpʳ ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄
               ⦃ _ : VarSubIdNoOpʳ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄
               ⦃ _ : VarSubAppExtensional ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄ →
             (es : ExEs Γ A B) →
             -------------------------------------------------------------
             ⟦ Idᵛ ⦃ varSub ⦄ ⟧ᵛ* es ≡ es
⟦Idᵛ⟧ᵛ*≡id es = trans (gmap-cong id (RawAppSub.forExE Idᵛ) id forExE-Idᵛ≡id es) (gmap-id es)

⟦qᵉ-⟧ᵛ⟦Wkᵛ⟧ᵛ≡⟦Wkᵛ⟧ᵛ⟦-⟧ᵛ : ∀ {R}
                            ⦃ varSub : VarSubBase {lzero} R ⦄
                            ⦃ _ : RawVarSubOutHead ⦃ varSub ⦄ ⦄
                            ⦃ _ : RawVarSubLift ⦃ varSub ⦄ ⦃ SubVarSub ⦄ ⦄
                            ⦃ _ : RawVarSubApp ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄
                            ⦃ _ : VarSubAppCompositional ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ SubVarSub ⦄ ⦄
                            ⦃ _ : VarSubAppCompositional ⦃ varSub ⦄ ⦃ ExtVarSub ⦄ ⦃ SubVarSub ⦄ ⦄
                            (δ : VarSub ⦃ varSub ⦄ Γ Δ) (e : Ex Δ B) →
                          ⟦ qᵉ δ ⟧ᵛ ⟦ Wkᵛ {A = A} ⟧ᵛ e ≡ ⟦ Wkᵛ ⟧ᵛ ⟦ δ ⟧ᵛ e
⟦qᵉ-⟧ᵛ⟦Wkᵛ⟧ᵛ≡⟦Wkᵛ⟧ᵛ⟦-⟧ᵛ δ e =
  begin _ ≡⟨ ⟦-⟧ᵛ-compositional _ (Wkᵛ ⦃ ExtVarSub ⦄) e ⟩
        _ ≡˘⟨ ⟦-⟧ᵛ-compositional _ δ e ⟩
        _ ∎
  where
    open ≡-Reasoning

⟦qᵉ²-⟧ᵛ⟦Wkᵛ²⟧ᵛ≡⟦Wkᵛ²⟧ᵛ⟦-⟧ᵛ : ∀ {R}
                               ⦃ varSub : VarSubBase {lzero} R ⦄
                               ⦃ _ : RawVarSubOutHead ⦃ varSub ⦄ ⦄
                               ⦃ _ : RawVarSubLift ⦃ varSub ⦄ ⦃ SubVarSub ⦄ ⦄
                               ⦃ _ : RawVarSubApp ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄
                               ⦃ _ : VarSubAppExtensional ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄
                               ⦃ _ : VarSubAppCompositional ⦃ ExtVarSub ⦄ ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦄
                               ⦃ _ : VarSubAppCompositional ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ SubVarSub ⦄ ⦄
                               ⦃ _ : VarSubAppCompositional ⦃ varSub ⦄ ⦃ ExtVarSub ⦄ ⦃ SubVarSub ⦄ ⦄
                               (δ : VarSub ⦃ varSub ⦄ Γ Δ) (e : Ex Δ C) →
                             ⟦ qᵉ qᵉ δ ⟧ᵛ ⟦ Wkᵛ {A = B} ∘ᵛ Wkᵛ {A = A} ⟧ᵛ e ≡ ⟦ Wkᵛ {A = B} ∘ᵛ Wkᵛ {A = A} ⟧ᵛ ⟦ δ ⟧ᵛ e
⟦qᵉ²-⟧ᵛ⟦Wkᵛ²⟧ᵛ≡⟦Wkᵛ²⟧ᵛ⟦-⟧ᵛ δ e =
  begin _ ≡⟨ ⟦-⟧ᵛ-compositional (qᵉ qᵉ δ) (Wkᵛ ∘ᵛ Wkᵛ) e ⟩
        _ ≡⟨ ⟦-⟧ᵛ-extensional e (⟦-⟧ᵛ-compositional Wkᵛ Wkᵛ ∘ δ) ⟩
        _ ≡˘⟨ ⟦-⟧ᵛ-compositional (Wkᵛ ∘ᵛ Wkᵛ) δ e ⟩
        _ ∎
  where
    open ≡-Reasoning

⟦qᵉ³-⟧ᵛ⟦qᵉ²Wkᵛ⟧ᵛ≡⟦qᵉ²Wkᵛ⟧ᵛ⟦qᵉ²-⟧ᵛ : ∀ {R}
                                      ⦃ varSub : VarSubBase {lzero} R ⦄
                                      ⦃ _ : RawVarSubId ⦃ varSub ⦄ ⦄
                                      ⦃ _ : RawVarSubOutHead ⦃ varSub ⦄ ⦄
                                      ⦃ _ : RawVarSubLift ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦄
                                      ⦃ _ : RawVarSubLift ⦃ varSub ⦄ ⦃ SubVarSub ⦄ ⦄
                                      ⦃ _ : RawVarSubApp ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄
                                      ⦃ _ : VarSubOutHeadSpec ⦃ varSub ⦄ ⦄
                                      ⦃ _ : VarSubLiftId ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦄
                                      ⦃ _ : VarSubIdNoOpʳ ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄
                                      ⦃ _ : VarSubAppExtensional ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄
                                      ⦃ _ : VarSubAppCompositional ⦃ ExtVarSub ⦄ ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦄
                                      ⦃ _ : VarSubAppCompositional ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ ExtVarSub ⦄ ⦄
                                      ⦃ _ : VarSubAppCompositional ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ SubVarSub ⦄ ⦄
                                      ⦃ _ : VarSubAppCompositional ⦃ varSub ⦄ ⦃ ExtVarSub ⦄ ⦃ SubVarSub ⦄ ⦄
                                      (δ : VarSub ⦃ varSub ⦄ Γ Δ) (e : Ex (B ∷ A ∷ Δ) D) →
                                    ⟦ qᵉ qᵉ qᵉ δ ⟧ᵛ ⟦ qᵉᵉ qᵉᵉ (Wkᵛ {A = C}) ⟧ᵛ e ≡ ⟦ qᵉᵉ qᵉᵉ Wkᵛ ⟧ᵛ ⟦ qᵉ qᵉ δ ⟧ᵛ e
⟦qᵉ³-⟧ᵛ⟦qᵉ²Wkᵛ⟧ᵛ≡⟦qᵉ²Wkᵛ⟧ᵛ⟦qᵉ²-⟧ᵛ δ e =
  begin _ ≡⟨ ⟦-⟧ᵛ-compositional _ (qᵉ qᵉ Wkᵛ) e ⟩
        _ ≡˘⟨ ⟦-⟧ᵛ-extensional e (qᵛ⟦ _ ∷ _ ∷ [] ⟧-distrib-∘ᵛ (qᵉ δ) Wkᵛ) ⟩
        _ ≡⟨ ⟦-⟧ᵛ-extensional e (qᵛ⟦ _ ∷ _ ∷ [] ⟧-distrib-∘ᵛ Wkᵛ δ) ⟩
        _ ≡˘⟨ ⟦-⟧ᵛ-compositional _ (qᵉ qᵉ δ) e ⟩
        _ ∎
  where
    open ≡-Reasoning

⟦qᵉ⁴-⟧ᵛ⟦qᵉ²Wkᵛ²⟧ᵛ≡⟦qᵉ²Wkᵛ²⟧ᵛ⟦qᵉ²-⟧ᵛ : ∀ {R}
                                        ⦃ varSub : VarSubBase {lzero} R ⦄
                                        ⦃ _ : RawVarSubId ⦃ varSub ⦄ ⦄
                                        ⦃ _ : RawVarSubOutHead ⦃ varSub ⦄ ⦄
                                        ⦃ _ : RawVarSubLift ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦄
                                        ⦃ _ : RawVarSubLift ⦃ varSub ⦄ ⦃ SubVarSub ⦄ ⦄
                                        ⦃ _ : RawVarSubApp ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄
                                        ⦃ _ : VarSubOutHeadSpec ⦃ varSub ⦄ ⦄
                                        ⦃ _ : VarSubLiftId ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦄
                                        ⦃ _ : VarSubIdNoOpʳ ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄
                                        ⦃ _ : VarSubAppExtensional ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄
                                        ⦃ _ : VarSubAppCompositional ⦃ ExtVarSub ⦄ ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦄
                                        ⦃ _ : VarSubAppCompositional ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ ExtVarSub ⦄ ⦄
                                        ⦃ _ : VarSubAppCompositional ⦃ varSub ⦄ ⦃ ExtVarSub ⦄ ⦃ SubVarSub ⦄ ⦄
                                        ⦃ _ : VarSubAppCompositional ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ SubVarSub ⦄ ⦄
                                        (δ : VarSub ⦃ varSub ⦄ Γ Δ) (e : Ex (B ∷ A ∷ Δ) E) →
                                      ⟦ qᵉ qᵉ qᵉ qᵉ δ ⟧ᵛ ⟦ qᵉ qᵉ (Wkᵛ {A = D} ∘ᵛ Wkᵛ {A = C}) ⟧ᵛ e
                                        ≡ ⟦ qᵉ qᵉ (Wkᵛ {A = D} ∘ᵛ Wkᵛ {A = C}) ⟧ᵛ ⟦ qᵉ qᵉ δ ⟧ᵛ e
⟦qᵉ⁴-⟧ᵛ⟦qᵉ²Wkᵛ²⟧ᵛ≡⟦qᵉ²Wkᵛ²⟧ᵛ⟦qᵉ²-⟧ᵛ δ e =
  begin _ ≡⟨ ⟦-⟧ᵛ-compositional (qᵉ qᵉ qᵉ qᵉ δ) (qᵉ qᵉ (Wkᵛ ∘ᵛ Wkᵛ)) e ⟩
        _ ≡˘⟨ ⟦-⟧ᵛ-extensional e (qᵛ⟦ _ ∷ _ ∷ [] ⟧-distrib-∘ᵛ (qᵉ qᵉ δ) (Wkᵛ ∘ᵛ Wkᵛ)) ⟩
        _ ≡⟨ ⟦-⟧ᵛ-extensional e (qᵛ⟦ _ ∷ _ ∷ [] ⟧-congᵛ (⟦-⟧ᵛ-compositional Wkᵛ Wkᵛ ∘ δ)) ⟩
        _ ≡⟨ ⟦-⟧ᵛ-extensional e (qᵛ⟦ _ ∷ _ ∷ [] ⟧-distrib-∘ᵛ(Wkᵛ ∘ᵛ Wkᵛ) δ) ⟩
        _ ≡˘⟨ ⟦-⟧ᵛ-compositional (qᵉ qᵉ (Wkᵛ ∘ᵛ Wkᵛ)) (qᵉ qᵉ δ) e ⟩
        _ ∎
  where
    open ≡-Reasoning

forExE-qᵉ-forExE-Wkᵛ≡forExE-Wkᵛ-forExE : ∀ {R}
                                           ⦃ varSub : VarSubBase {lzero} R ⦄
                                           ⦃ _ : RawVarSubId ⦃ varSub ⦄ ⦄
                                           ⦃ _ : RawVarSubOutHead ⦃ varSub ⦄ ⦄
                                           ⦃ _ : RawVarSubLift ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦄
                                           ⦃ _ : RawVarSubLift ⦃ varSub ⦄ ⦃ SubVarSub ⦄ ⦄
                                           ⦃ _ : RawVarSubApp ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄
                                           ⦃ _ : VarSubOutHeadSpec ⦃ varSub ⦄ ⦄
                                           ⦃ _ : VarSubLiftId ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦄
                                           ⦃ _ : VarSubIdNoOpʳ ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄
                                           ⦃ _ : VarSubAppExtensional ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄
                                           ⦃ _ : VarSubAppCompositional ⦃ ExtVarSub ⦄ ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦄
                                           ⦃ _ : VarSubAppCompositional ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ ExtVarSub ⦄ ⦄
                                           ⦃ _ : VarSubAppCompositional ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ SubVarSub ⦄ ⦄
                                           ⦃ _ : VarSubAppCompositional ⦃ varSub ⦄ ⦃ ExtVarSub ⦄ ⦃ SubVarSub ⦄ ⦄
                                           (δ : VarSub ⦃ varSub ⦄ Γ Δ) (ee : ExE Δ B C) →
                                         RawAppSub.forExE (qᵉ δ) (RawAppSub.forExE (Wkᵛ {A = A}) ee) ≡ RawAppSub.forExE Wkᵛ (RawAppSub.forExE δ ee)
forExE-qᵉ-forExE-Wkᵛ≡forExE-Wkᵛ-forExE δ (-`$ e)      = cong -`$_ (⟦qᵉ-⟧ᵛ⟦Wkᵛ⟧ᵛ≡⟦Wkᵛ⟧ᵛ⟦-⟧ᵛ δ e)
forExE-qᵉ-forExE-Wkᵛ≡forExE-Wkᵛ-forExE δ (`let-`in e) = cong `let-`in_ (⟦qᵉ³-⟧ᵛ⟦qᵉ²Wkᵛ⟧ᵛ≡⟦qᵉ²Wkᵛ⟧ᵛ⟦qᵉ²-⟧ᵛ δ e)

forExE-qᵉ²-forExE-Wkᵛ²≡forExE-Wkᵛ²-forExE : ∀ {R}
                                              ⦃ varSub : VarSubBase {lzero} R ⦄
                                              ⦃ _ : RawVarSubId ⦃ varSub ⦄ ⦄
                                              ⦃ _ : RawVarSubOutHead ⦃ varSub ⦄ ⦄
                                              ⦃ _ : RawVarSubLift ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦄
                                              ⦃ _ : RawVarSubLift ⦃ varSub ⦄ ⦃ SubVarSub ⦄ ⦄
                                              ⦃ _ : RawVarSubApp ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄
                                              ⦃ _ : VarSubOutHeadSpec ⦃ varSub ⦄ ⦄
                                              ⦃ _ : VarSubLiftId ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦄
                                              ⦃ _ : VarSubIdNoOpʳ ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄
                                              ⦃ _ : VarSubAppExtensional ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄
                                              ⦃ _ : VarSubAppCompositional ⦃ ExtVarSub ⦄ ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦄
                                              ⦃ _ : VarSubAppCompositional ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ ExtVarSub ⦄ ⦄
                                              ⦃ _ : VarSubAppCompositional ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ SubVarSub ⦄ ⦄
                                              ⦃ _ : VarSubAppCompositional ⦃ varSub ⦄ ⦃ ExtVarSub ⦄ ⦃ SubVarSub ⦄ ⦄
                                              (δ : VarSub ⦃ varSub ⦄ Γ Δ) (ee : ExE Δ C D) →
                                            RawAppSub.forExE (qᵉ qᵉ δ) (RawAppSub.forExE (Wkᵛ {A = B} ∘ᵛ Wkᵛ {A = A}) ee) ≡ RawAppSub.forExE (Wkᵛ ∘ᵛ Wkᵛ) (RawAppSub.forExE δ ee)
forExE-qᵉ²-forExE-Wkᵛ²≡forExE-Wkᵛ²-forExE δ (-`$ e)      = cong -`$_ (⟦qᵉ²-⟧ᵛ⟦Wkᵛ²⟧ᵛ≡⟦Wkᵛ²⟧ᵛ⟦-⟧ᵛ δ e)
forExE-qᵉ²-forExE-Wkᵛ²≡forExE-Wkᵛ²-forExE δ (`let-`in e) = cong `let-`in_ (⟦qᵉ⁴-⟧ᵛ⟦qᵉ²Wkᵛ²⟧ᵛ≡⟦qᵉ²Wkᵛ²⟧ᵛ⟦qᵉ²-⟧ᵛ δ e)

⟦qᵉ-⟧ᵛ*⟦Wkᵛ⟧ᵛ*≡⟦Wkᵛ⟧ᵛ*⟦-⟧ᵛ* : ∀ {R}
                                ⦃ varSub : VarSubBase {lzero} R ⦄
                                ⦃ _ : RawVarSubId ⦃ varSub ⦄ ⦄
                                ⦃ _ : RawVarSubOutHead ⦃ varSub ⦄ ⦄
                                ⦃ _ : RawVarSubLift ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦄
                                ⦃ _ : RawVarSubLift ⦃ varSub ⦄ ⦃ SubVarSub ⦄ ⦄
                                ⦃ _ : RawVarSubApp ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄
                                ⦃ _ : VarSubOutHeadSpec ⦃ varSub ⦄ ⦄
                                ⦃ _ : VarSubLiftId ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦄
                                ⦃ _ : VarSubIdNoOpʳ ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄
                                ⦃ _ : VarSubAppExtensional ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄
                                ⦃ _ : VarSubAppCompositional ⦃ ExtVarSub ⦄ ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦄
                                ⦃ _ : VarSubAppCompositional ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ ExtVarSub ⦄ ⦄
                                ⦃ _ : VarSubAppCompositional ⦃ varSub ⦄ ⦃ ExtVarSub ⦄ ⦃ SubVarSub ⦄ ⦄
                                ⦃ _ : VarSubAppCompositional ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ SubVarSub ⦄ ⦄
                                (δ : VarSub ⦃ varSub ⦄ Γ Δ) (es : ExEs Δ B C) →
                              ⟦ qᵉ δ ⟧ᵛ* ⟦ Wkᵛ {A = A} ⟧ᵛ* es ≡ ⟦ Wkᵛ ⟧ᵛ* ⟦ δ ⟧ᵛ* es
⟦qᵉ-⟧ᵛ*⟦Wkᵛ⟧ᵛ*≡⟦Wkᵛ⟧ᵛ*⟦-⟧ᵛ* δ ε         = refl
⟦qᵉ-⟧ᵛ*⟦Wkᵛ⟧ᵛ*≡⟦Wkᵛ⟧ᵛ*⟦-⟧ᵛ* δ (ee ◅ es) = cong₂ _◅_ (forExE-qᵉ-forExE-Wkᵛ≡forExE-Wkᵛ-forExE δ ee) (⟦qᵉ-⟧ᵛ*⟦Wkᵛ⟧ᵛ*≡⟦Wkᵛ⟧ᵛ*⟦-⟧ᵛ* δ es)

⟦!ˢ-⟧ᵛ⟦Wkᵛ⟧ᵛ≡id : ∀ (e : Ex Γ A) (f : Ex Γ B) →
                  ⟦ !ˢ e ⟧ᵛ ⟦ Wkᵛ ⟧ᵛ f ≡ f
⟦!ˢ-⟧ᵛ⟦Wkᵛ⟧ᵛ≡id e f =
  begin _ ≡⟨ ⟦-⟧ᵛ-compositional _ Wkᵛ f ⟩
        _ ≡⟨ ⟦Idᵛ⟧ᵛ≡liftᵛ f ⟩
        _ ∎
  where
    open ≡-Reasoning

⟦!ˢ-,ᵛ-⟧ᵛ⟦Wkᵛ²⟧ᵛ≡id : ∀ (e : Ex Γ A) (f : Ex Γ B) (g : Ex Γ C) →
                      ⟦ !ˢ e ,ᵛ f ⟧ᵛ ⟦ Wkᵛ ∘ᵛ Wkᵛ ⟧ᵛ g ≡ g
⟦!ˢ-,ᵛ-⟧ᵛ⟦Wkᵛ²⟧ᵛ≡id e f g =
  begin _ ≡⟨ ⟦-⟧ᵛ-compositional _ (Wkᵛ ∘ᵛ Wkᵛ) g ⟩
        _ ≡⟨ ⟦Idᵛ⟧ᵛ≡liftᵛ g ⟩
        _ ∎
  where
    open ≡-Reasoning

-- ⟦qᵉ!ˢ-⟧ᵛ⟦qᵉWkᵛ⟧ᵛ≡id : ∀ (e : Ex Γ A) (f : Ex (B ∷ Γ) C) →
--                       ⟦ qᵉ !ˢ e ⟧ᵛ ⟦ qᵉᵉ Wkᵛ ⟧ᵛ f ≡ f
-- ⟦qᵉ!ˢ-⟧ᵛ⟦qᵉWkᵛ⟧ᵛ≡id e f =
--   begin _ ≡⟨ ⟦-⟧ᵛ-compositional _ (qᵉᵉ Wkᵛ) f ⟩
--         _ ≡˘⟨ ⟦-⟧ᵛ-extensional f (qᵛ-distrib-∘ᵛ (!ˢ e) Wkᵛ) ⟩
--         _ ≡⟨ ⟦-⟧ᵛ-extensional f qᵛ-preserves-Idᵛ ⟩
--         _ ≡⟨ ⟦Idᵛ⟧ᵛ≡liftᵛ f ⟩
--         _ ∎
--   where
--     open ≡-Reasoning

⟦qᵉ²!ˢ-⟧ᵛ⟦qᵉ²Wkᵛ⟧ᵛ≡id : ∀ (e : Ex Γ A) (f : Ex (C ∷ B ∷ Γ) D) →
                          ⟦ qᵉ qᵉ !ˢ e ⟧ᵛ ⟦ qᵉᵉ qᵉᵉ Wkᵛ ⟧ᵛ f ≡ f
⟦qᵉ²!ˢ-⟧ᵛ⟦qᵉ²Wkᵛ⟧ᵛ≡id e f =
  begin _ ≡⟨ ⟦-⟧ᵛ-compositional _ (qᵉᵉ qᵉᵉ Wkᵛ) f ⟩
        _ ≡˘⟨ ⟦-⟧ᵛ-extensional f (qᵛ⟦ _ ∷ _ ∷ [] ⟧-distrib-∘ᵛ (!ˢ e) Wkᵛ) ⟩
        _ ≡⟨ ⟦-⟧ᵛ-extensional f qᵛ⟦ _ ∷ _ ∷ [] ⟧-preserves-Idᵛ ⟩
        _ ≡⟨ ⟦Idᵛ⟧ᵛ≡liftᵛ f ⟩
        _ ∎
  where
    open ≡-Reasoning

⟦qᵉ²!ˢ-,ᵛ-⟧ᵛ⟦qᵉ²Wkᵛ²⟧ᵛ≡id : ∀ (e : Ex Γ A) (f : Ex Γ B) (g : Ex (D ∷ C ∷ Γ) E) →
                            ⟦ qᵉ qᵉ (!ˢ e ,ᵛ f) ⟧ᵛ ⟦ qᵉᵉ qᵉᵉ (Wkᵛ ∘ᵛ Wkᵛ) ⟧ᵛ g ≡ g
⟦qᵉ²!ˢ-,ᵛ-⟧ᵛ⟦qᵉ²Wkᵛ²⟧ᵛ≡id e f g =
  begin _ ≡⟨ ⟦-⟧ᵛ-compositional _ (qᵉᵉ qᵉᵉ (Wkᵛ ∘ᵛ Wkᵛ)) g ⟩
        _ ≡˘⟨ ⟦-⟧ᵛ-extensional g (qᵛ⟦ _ ∷ _ ∷ [] ⟧-distrib-∘ᵛ (!ˢ e ,ᵛ f) (Wkᵛ ∘ᵛ Wkᵛ)) ⟩
        _ ≡⟨ ⟦-⟧ᵛ-extensional g qᵛ⟦ _ ∷ _ ∷ [] ⟧-preserves-Idᵛ ⟩
        _ ≡⟨ ⟦Idᵛ⟧ᵛ≡liftᵛ g ⟩
        _ ∎
  where
    open ≡-Reasoning

forExE-!ˢ-forExE-Wkᵛ≡id : ∀ (e : Ex Γ A) (ee : ExE Γ B C) →
                          RawAppSub.forExE (!ˢ e) (RawAppSub.forExE Wkᵛ ee) ≡ ee
forExE-!ˢ-forExE-Wkᵛ≡id e (-`$ f)      = cong -`$_ (⟦!ˢ-⟧ᵛ⟦Wkᵛ⟧ᵛ≡id e f)
forExE-!ˢ-forExE-Wkᵛ≡id e (`let-`in f) = cong `let-`in_ (⟦qᵉ²!ˢ-⟧ᵛ⟦qᵉ²Wkᵛ⟧ᵛ≡id e f)

forExE-!ˢ-,ᵛ-forExE-Wkᵛ²≡id : ∀ (e : Ex Γ A) (f : Ex Γ B) (ee : ExE Γ C D) →
                              RawAppSub.forExE (!ˢ e ,ᵛ f) (RawAppSub.forExE (Wkᵛ ∘ᵛ Wkᵛ) ee) ≡ ee
forExE-!ˢ-,ᵛ-forExE-Wkᵛ²≡id e f (-`$ g)      = cong -`$_ (⟦!ˢ-,ᵛ-⟧ᵛ⟦Wkᵛ²⟧ᵛ≡id e f g)
forExE-!ˢ-,ᵛ-forExE-Wkᵛ²≡id e f (`let-`in g) = cong `let-`in_ (⟦qᵉ²!ˢ-,ᵛ-⟧ᵛ⟦qᵉ²Wkᵛ²⟧ᵛ≡id e f g)
