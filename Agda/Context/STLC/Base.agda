{-# OPTIONS --safe #-}
open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Data.List as List
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.Propositional as List
open import Data.Sum as ⊎
open import Function using (id; _∘_)
open import Relation.Binary using (REL; Rel)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; _≗_)
open import Relation.Unary using (_⊆_)

module Context.STLC.Base {ℓ₀} (Tp : Set ℓ₀) where

Ctx : Set ℓ₀
Ctx = List Tp

private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    A A′ A′₀ A′₁ A′₂ A′₃ A″ A″₀ A″₁ A″₂ A″₃ A‴ A‴₀ A‴₁ A‴₂ A‴₃ A₀ A₁ A₂ A₃ : Tp
    B B′ B′₀ B′₁ B′₂ B′₃ B″ B″₀ B″₁ B″₂ B″₃ B‴ B‴₀ B‴₁ B‴₂ B‴₃ B₀ B₁ B₂ B₃ : Tp
    C C′ C′₀ C′₁ C′₂ C′₃ C″ C″₀ C″₁ C″₂ C″₃ C‴ C‴₀ C‴₁ C‴₂ C‴₃ C₀ C₁ C₂ C₃ : Tp
    Γ Γ′ Γ′₀ Γ′₁ Γ′₂ Γ′₃ Γ″ Γ″₀ Γ″₁ Γ″₂ Γ″₃ Γ‴ Γ‴₀ Γ‴₁ Γ‴₂ Γ‴₃ Γ₀ Γ₁ Γ₂ Γ₃ : Ctx
    Δ Δ′ Δ′₀ Δ′₁ Δ′₂ Δ′₃ Δ″ Δ″₀ Δ″₁ Δ″₂ Δ″₃ Δ‴ Δ‴₀ Δ‴₁ Δ‴₂ Δ‴₃ Δ₀ Δ₁ Δ₂ Δ₃ : Ctx
    Ψ Ψ′ Ψ′₀ Ψ′₁ Ψ′₂ Ψ′₃ Ψ″ Ψ″₀ Ψ″₁ Ψ″₂ Ψ″₃ Ψ‴ Ψ‴₀ Ψ‴₁ Ψ‴₂ Ψ‴₃ Ψ₀ Ψ₁ Ψ₂ Ψ₃ : Ctx
    R R₁ R₂ R₃ : REL Ctx Tp ℓ₁

record VarSubBase (R : REL Ctx Tp ℓ₁) : Set (ℓ₀ ⊔ lsuc ℓ₁) where
  VarSub : Rel Ctx _
  VarSub Δ Γ = (_∈ Γ) ⊆ R Δ

  infix 4 _≈ᵛ_
  _≈ᵛ_ : Rel (VarSub Δ Γ) _
  σ ≈ᵛ σ′ = ∀ {A} → _≗_ {A = A ∈ _} σ σ′

  infixl 6 _,ᵛ_
  _,ᵛ_ : VarSub Δ Γ → R Δ A → VarSub Δ (A ∷ Γ)
  (σ ,ᵛ M) (here eq) = subst (R _) (sym eq) M
  (σ ,ᵛ M) (there y) = σ y

open VarSubBase ⦃...⦄ public

module _ ⦃ _ : VarSubBase {ℓ₁} R ⦄ where
  record RawVarSubId : Set (ℓ₀ ⊔ ℓ₁) where
    field
      Idᵛ : VarSub Γ Γ

    infixr 7 !ᵛ_
    !ᵛ_ : R Γ A → VarSub Γ (A ∷ Γ)
    !ᵛ M = Idᵛ ,ᵛ M

  open RawVarSubId ⦃...⦄ public

  record RawVarSubWk : Set (ℓ₀ ⊔ ℓ₁) where
    field
      Wkᵛ : VarSub (A ∷ Γ) Γ

    Wkᵛof : ∀ A → VarSub (A ∷ Γ) Γ
    Wkᵛof _ = Wkᵛ

  open RawVarSubWk ⦃...⦄ public

  record RawVarSubOutHead : Set (ℓ₀ ⊔ ℓ₁) where
    field
      R-head : R (A ∷ Γ) A

  open RawVarSubOutHead ⦃...⦄ public

module _
  ⦃ varSub₁ : VarSubBase {ℓ₁} R₁ ⦄
  ⦃ varSub₂ : VarSubBase {ℓ₂} R₂ ⦄ where
  open VarSubBase varSub₁ renaming (VarSub to VarSub₁)
  open VarSubBase varSub₂ renaming (VarSub to VarSub₂)

  record RawVarSubLift : Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂) where
    field
      liftᵛ : R₁ Γ A → R₂ Γ A

    liftᵛ∘ : VarSub₁ Δ Γ → VarSub₂ Δ Γ
    liftᵛ∘ = liftᵛ ∘_

  open RawVarSubLift ⦃...⦄ public

module _
  ⦃ varSub₁ : VarSubBase {ℓ₁} R₁ ⦄
  ⦃ varSub₂ : VarSubBase {ℓ₂} R₂ ⦄
  ⦃ varSub₃ : VarSubBase {ℓ₃} R₃ ⦄ where
  open VarSubBase varSub₁ renaming (VarSub to VarSub₁)
  open VarSubBase varSub₂ renaming (VarSub to VarSub₂)
  open VarSubBase varSub₃ renaming (VarSub to VarSub₃)

  record RawVarSubApp : Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
    field
      Appᵛ : VarSub₁ Δ Γ → R₂ Γ A → R₃ Δ A

    infixr 30 Appᵛ
    syntax Appᵛ σ M = ⟦ σ ⟧ᵛ M

    infixr 5 _∘ᵛ_
    _∘ᵛ_ : VarSub₁ Ψ Δ → VarSub₂ Δ Γ → VarSub₃ Ψ Γ
    σ ∘ᵛ σ′ = Appᵛ σ ∘ σ′

  open RawVarSubApp ⦃...⦄ public

module _ ⦃ _ : VarSubBase R₁ ⦄ where
  instance
    RawVarSubLiftSelf : RawVarSubLift
    RawVarSubLiftSelf .liftᵛ = id

module _
  ⦃ varSub₁ : VarSubBase R₁ ⦄
  ⦃ varSub₂ : VarSubBase R₂ ⦄
  ⦃ varSub₃ : VarSubBase R₃ ⦄
  ⦃ _ : RawVarSubId ⦃ varSub₃ ⦄ ⦄
  ⦃ _ : RawVarSubWk ⦃ varSub₁ ⦄ ⦄
  ⦃ _ : RawVarSubLift ⦃ varSub₃ ⦄ ⦃ varSub₂ ⦄ ⦄
  ⦃ _ : RawVarSubApp ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₃ ⦄ ⦄ where
  open VarSubBase varSub₃ using () renaming (VarSub to VarSub₃)

  Wkᵛ⟦_⟧ : ∀ Δ → VarSub₃ (Δ ++ Γ) Γ
  Wkᵛ⟦ []    ⟧ = Idᵛ
  Wkᵛ⟦ _ ∷ Δ ⟧ = _∘ᵛ_ ⦃ _ ⦄ ⦃ varSub₂ ⦄ Wkᵛ (liftᵛ∘ (Wkᵛ⟦ Δ ⟧))

module _
  ⦃ varSub₁ : VarSubBase R₁ ⦄
  ⦃ varSub₂ : VarSubBase R₂ ⦄
  ⦃ varSub₃ : VarSubBase R₃ ⦄ where
  open VarSubBase varSub₂ using () renaming (VarSub to VarSub₂)
  open VarSubBase varSub₃ using () renaming (VarSub to VarSub₃)

  module _
    ⦃ _ : RawVarSubWk ⦃ varSub₁ ⦄ ⦄
    ⦃ _ : RawVarSubOutHead ⦃ varSub₃ ⦄ ⦄
    ⦃ _ : RawVarSubApp ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₃ ⦄ ⦄ where
    infixr 7 qᵛ_
    qᵛ_ : VarSub₂ Δ Γ → VarSub₃ (A ∷ Δ) (A ∷ Γ)
    qᵛ σ = (Wkᵛ ∘ᵛ σ) ,ᵛ R-head

    infixr 7 qᵛ_of_
    qᵛ_of_ : VarSub₂ Δ Γ → ∀ A → VarSub₃ (A ∷ Δ) (A ∷ Γ)
    qᵛ σ of _ = qᵛ σ

  module _
    ⦃ _ : RawVarSubWk ⦃ varSub₁ ⦄ ⦄
    ⦃ _ : RawVarSubOutHead ⦃ varSub₃ ⦄ ⦄
    ⦃ _ : RawVarSubLift ⦃ varSub₃ ⦄ ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : RawVarSubApp ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₃ ⦄ ⦄ where
    infixr 7 qᵛ⟦_⟧_
    qᵛ⟦_⟧_ : ∀ Ψ → VarSub₃ Δ Γ → VarSub₃ (Ψ ++ Δ) (Ψ ++ Γ)
    qᵛ⟦ []    ⟧ σ = σ
    qᵛ⟦ _ ∷ Ψ ⟧ σ = qᵛ (liftᵛ∘ (qᵛ⟦ Ψ ⟧ σ))
