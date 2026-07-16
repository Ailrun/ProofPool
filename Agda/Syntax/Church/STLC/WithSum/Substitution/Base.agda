{-# OPTIONS --safe #-}
module Syntax.Church.STLC.WithSum.Substitution.Base where

open import Agda.Primitive                        using (lzero)
open import Data.List                             using (_∷_)
open import Data.List.Membership.Propositional    using (_∈_)
open import Data.List.Relation.Unary.Any          using (here; there)
open import Function                              using (flip; id)
open import Relation.Binary.PropositionalEquality hiding (J)

open import Syntax.Church.STLC.WithSum.Base renaming (module Variables to BVariables)

----------------------------------------------------------
-- Substitutions
----------------------------------------------------------

instance
  SubVarSub : VarSubBase Tm
  SubVarSub .tag = 1

Sub = VarSub ⦃ SubVarSub ⦄

instance
  RawExtLiftSub : RawVarSubLift ⦃ ExtVarSub ⦄ ⦃ SubVarSub ⦄
  RawExtLiftSub .liftᵛ = `#_

infixr 30 !ˢ_
!ˢ_ = !ᵛ_ ⦃ SubVarSub ⦄

module Variables where
  open BVariables public

  variable
    σ σ₀ σ₁ σ₂ σ₃ σₗ σᵣ σ′ σ′₀ σ′₁ σ′₂ σ′ₗ σ′ᵣ σ″ σ″₀ σ″₁ σ″₂ σ″₃ σ″ₗ σ″ᵣ σ‴ σ‴₀ σ‴₁ σ‴₂ σ‴₃ σ‴ₗ σ‴ᵣ : Sub Γ Δ
    τ τ₀ τ₁ τ₂ τ₃ τₗ τᵣ τ′ τ′₀ τ′₁ τ′₂ τ′ₗ τ′ᵣ τ″ τ″₀ τ″₁ τ″₂ τ″₃ τ″ₗ τ″ᵣ τ‴ τ‴₀ τ‴₁ τ‴₂ τ‴₃ τ‴ₗ τ‴ᵣ : Sub Γ Δ
    υ υ₀ υ₁ υ₂ υ₃ υₗ υᵣ υ′ υ′₀ υ′₁ υ′₂ υ′ₗ υ′ᵣ υ″ υ″₀ υ″₁ υ″₂ υ″₃ υ″ₗ υ″ᵣ υ‴ υ‴₀ υ‴₁ υ‴₂ υ‴₃ υ‴ₗ υ‴ᵣ : Sub Γ Δ

open Variables

----------------------------------------------------------
-- Application on Substitution
----------------------------------------------------------

instance
  RawAppSub : ∀ {R}
                ⦃ varSub : VarSubBase {lzero} R ⦄
                ⦃ _ : RawVarSubOutHead ⦃ varSub ⦄ ⦄
                ⦃ _ : RawVarSubLift ⦃ varSub ⦄ ⦃ SubVarSub ⦄ ⦄
                ⦃ _ : RawVarSubApp ⦃ ExtVarSub ⦄ ⦃ varSub ⦄ ⦃ varSub ⦄ ⦄ →
              RawVarSubApp ⦃ varSub ⦄ ⦃ SubVarSub ⦄ ⦃ SubVarSub ⦄
  RawAppSub .Appᵛ δ (`# x)                 = liftᵛ (δ x)
  RawAppSub .Appᵛ δ (`λ M)                 = `λ ⟦ qᵉ δ ⟧ᵛ M
  RawAppSub .Appᵛ δ (M `$ N)               = ⟦ δ ⟧ᵛ M `$ ⟦ δ ⟧ᵛ N
  RawAppSub .Appᵛ δ (`injₗ M)              = `injₗ (⟦ δ ⟧ᵛ M)
  RawAppSub .Appᵛ δ (`injᵣ M)              = `injᵣ (⟦ δ ⟧ᵛ M)
  RawAppSub .Appᵛ δ (`case M `of Nₗ `/ Nᵣ) = `case ⟦ δ ⟧ᵛ M `of ⟦ qᵉ δ ⟧ᵛ Nₗ `/ ⟦ qᵉ δ ⟧ᵛ Nᵣ

infixr 7 qᵉˢ_
qᵉˢ_ : Sub Δ Γ → Sub (A ∷ Δ) (A ∷ Γ)
qᵉˢ_ = qᵉ_ ⦃ SubVarSub ⦄
