{-# OPTIONS --safe --without-K --instance-search-depth=10 #-}
module PPLib.Context.STLC.Properties {ℓ₀} (Tp : Set ℓ₀) where

open import Agda.Primitive                        using (Level; _⊔_)
open import Data.List                             hiding ([_])
open import Data.List.Membership.Propositional    using (_∈_)
open import Data.List.Relation.Unary.Any          using (here; there)
open import Function                              using (flip; id; it; _∘_)
open import Relation.Binary                       using ( IsEquivalence; Reflexive
                                                        ; REL; Rel; Setoid
                                                        ; Symmetric; Transitive
                                                        ; _Preserves_⟶_; _Preserves₂_⟶_⟶_
                                                        )
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans; module ≡-Reasoning)
import Relation.Binary.Reasoning.Setoid           as SetoidReasoning

open import PPLib.Context.STLC.Base Tp

open Variables

private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ ℓ₆ : Level

    R R₁ R₂ R₃ R₄ R₅ R₆ : REL Ctx Tp ℓ₁

module _ ⦃ _ : VarSubBase {ℓ₁} R ⦄ where
  ----------------------------------------------------------
  -- Equivalence
  ----------------------------------------------------------
  opaque
    reflexiveᵛ : ∀ (σ : VarSub Δ Γ) →
                 ---------------------
                 σ ≈ᵛ σ
    reflexiveᵛ σ x = refl

    reflᵛ : Reflexive (_≈ᵛ_ {Δ = Δ} {Γ})
    reflᵛ {x = σ} = reflexiveᵛ σ

    symᵛ : Symmetric (_≈ᵛ_ {Δ = Δ} {Γ})
    symᵛ = sym ∘_

    transᵛ : Transitive (_≈ᵛ_ {Δ = Δ} {Γ})
    transᵛ equiv equiv′ x = trans (equiv x) (equiv′ x)

    ≈ᵛ-IsEquivalence : ∀ Δ Γ →
                       ---------------------------------
                       IsEquivalence (_≈ᵛ_ {Δ = Δ} {Γ})
    ≈ᵛ-IsEquivalence Δ Γ = record { refl = λ x → refl ; sym = symᵛ ; trans = transᵛ }

  VarSub-Setoid : Ctx → Ctx → Setoid _ _
  VarSub-Setoid Δ Γ = record
    { Carrier = VarSub Δ Γ
    ; _≈_ = _≈ᵛ_
    ; isEquivalence = ≈ᵛ-IsEquivalence Δ Γ
    }

  module VarSub-Reasoning Δ Γ = SetoidReasoning (VarSub-Setoid Δ Γ)

  ----------------------------------------------------------
  -- Simple Congruences
  ----------------------------------------------------------
  opaque
    ,ᵛ-congᵛ : ∀ {A} →
               ----------------------------------------------------------
               _,ᵛ_ Preserves₂ _≈ᵛ_ {Δ = Δ} {Γ} ⟶ _≡_ {A = R _ A} ⟶ _≈ᵛ_
    ,ᵛ-congᵛ equiv refl (here eq) = refl
    ,ᵛ-congᵛ equiv refl (there x) = equiv x

    ,ᵛ-congᵛˡ : ∀ {A} (M : R _ A) →
                ----------------------------------------------
                flip _,ᵛ_ M Preserves _≈ᵛ_ {Δ = Δ} {Γ} ⟶ _≈ᵛ_
    ,ᵛ-congᵛˡ M equiv = ,ᵛ-congᵛ equiv refl

    ,ᵛ-congᵛʳ : ∀ {A} (σ : VarSub Δ Γ) →
                ----------------------------------------
                _,ᵛ_ σ Preserves _≡_ {A = R _ A} ⟶ _≈ᵛ_
    ,ᵛ-congᵛʳ σ refl = ,ᵛ-congᵛ (reflexiveᵛ σ) refl

  record VarSubWkSpec
    ⦃ _ : RawVarSubId ⦄
    ⦃ _ : RawVarSubWk ⦄
    : Set (ℓ₀ ⊔ ℓ₁) where
    field
      Wkᵛ-spec : ∀ (x : A ∈ Γ) →
                 ------------------------------
                 Wkᵛ {A = B} x ≡ Idᵛ (there x)
  open VarSubWkSpec ⦃...⦄ public

  record VarSubOutHeadSpec
    ⦃ _ : RawVarSubId ⦄
    ⦃ _ : RawVarSubOutHead ⦄
    : Set (ℓ₀ ⊔ ℓ₁) where
    field
      R-headᵛ-spec : Idᵛ {Γ = A ∷ Γ} (here refl) ≡ R-headᵛ
  open VarSubOutHeadSpec ⦃...⦄ public

module _
  ⦃ varSub₁ : VarSubBase {ℓ₁} R₁ ⦄
  ⦃ varSub₂ : VarSubBase {ℓ₂} R₂ ⦄ where
  record VarSubLiftId
    ⦃ _ : RawVarSubId ⦃ varSub₁ ⦄ ⦄
    ⦃ _ : RawVarSubId ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : RawVarSubLift ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦄
    : Set (ℓ₀ ⊔ ℓ₂) where
    field
      liftᵛ-preserves-Idᵛ : liftᵛ∘ ⦃ varSub₁ ⦄ Idᵛ ≈ᵛ Idᵛ ⦃ varSub₂ ⦄ {Γ = Γ}

  open VarSubLiftId ⦃...⦄ public

instance
  VarSubLiftIdLift : ∀ ⦃ varSub₁ : VarSubBase R₁ ⦄
                       ⦃ varSub₂ : VarSubBase R₂ ⦄
                       ⦃ _ : RawVarSubId ⦃ varSub₁ ⦄ ⦄
                       ⦃ _ : RawVarSubLift ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦄ →
                     ----------------------------------------------------------
                     VarSubLiftId ⦃ _ ⦄ ⦃ varSub₂ ⦄ ⦃ it ⦄ ⦃ RawVarSubLiftId ⦄
  VarSubLiftIdLift .liftᵛ-preserves-Idᵛ = reflexiveᵛ (liftᵛ∘ Idᵛ)
  {-# OVERLAPPABLE VarSubLiftIdLift #-}

  VarSubWkSpecLift : ∀ ⦃ varSub₁ : VarSubBase R₁ ⦄
                       ⦃ varSub₂ : VarSubBase R₂ ⦄
                       ⦃ _ : RawVarSubId ⦃ varSub₁ ⦄ ⦄
                       ⦃ _ : RawVarSubWk ⦃ varSub₁ ⦄ ⦄
                       ⦃ _ : RawVarSubLift ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦄
                       ⦃ varSubWkSpec₁ : VarSubWkSpec ⦃ varSub₁ ⦄ ⦄ →
                     -----------------------------------------------------------------
                     VarSubWkSpec ⦃ varSub₂ ⦄ ⦃ RawVarSubLiftId ⦄ ⦃ RawVarSubLiftWk ⦄
  VarSubWkSpecLift ⦃ varSubWkSpec₁ = varSubWkSpec₁ ⦄ .Wkᵛ-spec x = cong liftᵛ (Wkᵛ-spec ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ varSubWkSpec₁ ⦄ x)
  {-# OVERLAPPABLE VarSubWkSpecLift #-}

  VarSubOutHeadSpecLift : ∀ ⦃ varSub₁ : VarSubBase R₁ ⦄
                            ⦃ varSub₂ : VarSubBase R₂ ⦄
                            ⦃ _ : RawVarSubId ⦃ varSub₁ ⦄ ⦄
                            ⦃ _ : RawVarSubOutHead ⦃ varSub₁ ⦄ ⦄
                            ⦃ _ : RawVarSubLift ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦄
                            ⦃ varSubOutHeadSpec₁ : VarSubOutHeadSpec ⦃ varSub₁ ⦄ ⦄ →
                          ---------------------------------------------------------------------------
                          VarSubOutHeadSpec ⦃ varSub₂ ⦄ ⦃ RawVarSubLiftId ⦄ ⦃ RawVarSubLiftOutHead ⦄
  VarSubOutHeadSpecLift ⦃ varSubOutHeadSpec₁ = varSubOutHeadSpec₁ ⦄ .R-headᵛ-spec = cong liftᵛ (R-headᵛ-spec ⦃ _ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ varSubOutHeadSpec₁ ⦄)
  {-# OVERLAPPABLE VarSubOutHeadSpecLift #-}

module _
  ⦃ varSub₁ : VarSubBase {ℓ₁} R₁ ⦄
  ⦃ varSub₂ : VarSubBase {ℓ₂} R₂ ⦄
  ⦃ varSub₃ : VarSubBase {ℓ₃} R₃ ⦄ where
  open VarSubBase varSub₁ using () renaming (VarSub to VarSub₁; _≈ᵛ_ to _≈ᵛ₁_)
  open VarSubBase varSub₂ using () renaming (VarSub to VarSub₂; _≈ᵛ_ to _≈ᵛ₂_)
  open VarSubBase varSub₃ using () renaming (_≈ᵛ_ to _≈ᵛ₃_)

  record VarSubIdNoOpˡ
    ⦃ _ : RawVarSubId ⦃ varSub₁ ⦄ ⦄
    ⦃ _ : RawVarSubLift ⦃ varSub₂ ⦄ ⦃ varSub₃ ⦄ ⦄
    ⦃ _ : RawVarSubApp ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₃ ⦄ ⦄
    : Set (ℓ₀ ⊔ ℓ₂ ⊔ ℓ₃) where
    field
      Idᵛ-idˡ : ∀ (σ : VarSub₂ Δ Γ) →
                ---------------------------------
                Idᵛ ⦃ varSub₁ ⦄ ∘ᵛ σ ≈ᵛ liftᵛ∘ σ

    opaque
      ⟦Idᵛ⟧ᵛ≡liftᵛ : ∀ ⦃ _ : RawVarSubId ⦃ varSub₂ ⦄ ⦄
                       (M : R₂ Γ A) →
                     ----------------------------------
                     ⟦ Idᵛ ⟧ᵛ M ≡ liftᵛ M
      ⟦Idᵛ⟧ᵛ≡liftᵛ M = Idᵛ-idˡ (!ᵛ M) (here refl)

  open VarSubIdNoOpˡ ⦃...⦄ public

  record VarSubIdNoOpʳ
    ⦃ _ : RawVarSubId ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : RawVarSubLift ⦃ varSub₁ ⦄ ⦃ varSub₃ ⦄ ⦄
    ⦃ _ : RawVarSubApp ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₃ ⦄ ⦄
    : Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₃) where
    field
      Idᵛ-idʳ : ∀ (σ : VarSub₁ Δ Γ) →
                ---------------------------------
                σ ∘ᵛ Idᵛ ⦃ varSub₂ ⦄ ≈ᵛ liftᵛ∘ σ

  open VarSubIdNoOpʳ ⦃...⦄ public

  record VarSubAppExtensional
    ⦃ _ : RawVarSubApp ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₃ ⦄ ⦄
    : Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃) where
    field
      ⟦-⟧ᵛ-extensional : ∀ (M : R₂ Γ A) →
                         ---------------------------------------------------------------
                         (λ (δ : VarSub₁ _ _) → ⟦ δ ⟧ᵛ M) Preserves _≈ᵛ₁_ {Δ = Δ} ⟶ _≡_

    opaque
      ∘ᵛ-congᵛ : _∘ᵛ_ Preserves₂ _≈ᵛ₁_ {Δ = Ψ} ⟶ _≈ᵛ₂_ {Δ = Δ} {Γ} ⟶ _≈ᵛ₃_
      ∘ᵛ-congᵛ equivσ equivτ x
        rewrite equivτ x = ⟦-⟧ᵛ-extensional _ equivσ

      ∘ᵛ-congᵛˡ : (τ : VarSub₂ _ Γ) →
                  ------------------------------------------------
                  flip _∘ᵛ_ τ Preserves _≈ᵛ₁_ {Δ = Ψ} {Δ} ⟶ _≈ᵛ₃_
      ∘ᵛ-congᵛˡ τ equivσ = ∘ᵛ-congᵛ equivσ (reflexiveᵛ τ)

  open VarSubAppExtensional ⦃...⦄ public

module _
  ⦃ varSub₁ : VarSubBase {ℓ₁} R₁ ⦄
  ⦃ varSub₂ : VarSubBase {ℓ₂} R₂ ⦄
  ⦃ varSub₃ : VarSubBase {ℓ₃} R₃ ⦄
  ⦃ varSub₄ : VarSubBase {ℓ₄} R₄ ⦄ where
  open VarSubBase varSub₁ using () renaming (VarSub to VarSub₁)

  record VarSubLiftApp
    ⦃ _ : RawVarSubLift ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : RawVarSubApp ⦃ varSub₁ ⦄ ⦃ varSub₃ ⦄ ⦃ varSub₄ ⦄ ⦄
    ⦃ _ : RawVarSubApp ⦃ varSub₂ ⦄ ⦃ varSub₃ ⦄ ⦃ varSub₄ ⦄ ⦄
    : Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₃ ⊔ ℓ₄) where
    field
      liftᵛ-preserves-Appᵛ : ∀ (σ : VarSub₁ Δ Γ) (M : R₃ _ A) →
                             ---------------------------------------------
                             ⟦ liftᵛ∘ ⦃ _ ⦄ ⦃ varSub₂ ⦄ σ ⟧ᵛ M ≡ ⟦ σ ⟧ᵛ M

  open VarSubLiftApp ⦃...⦄ public

instance
  VarSubLiftAppLiftSelf : ∀ ⦃ varSub₁ : VarSubBase R₁ ⦄
                            ⦃ varSub₂ : VarSubBase R₂ ⦄
                            ⦃ varSub₃ : VarSubBase R₃ ⦄
                            ⦃ _ : RawVarSubApp ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₃ ⦄ ⦄ →
                          ------------------------------------------------------------------------
                          VarSubLiftApp ⦃ _ ⦄ ⦃ varSub₁ ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ RawVarSubLiftSelf ⦄
  VarSubLiftAppLiftSelf .VarSubLiftApp.liftᵛ-preserves-Appᵛ σ M = refl
  {-# OVERLAPPABLE VarSubLiftAppLiftSelf #-}

module _
  ⦃ varSub₁ : VarSubBase {ℓ₁} R₁ ⦄
  ⦃ varSub₂ : VarSubBase {ℓ₂} R₂ ⦄
  ⦃ varSub₃ : VarSubBase {ℓ₃} R₃ ⦄
  ⦃ varSub₄ : VarSubBase {ℓ₄} R₄ ⦄
  ⦃ varSub₅ : VarSubBase {ℓ₅} R₅ ⦄
  ⦃ varSub₆ : VarSubBase {ℓ₆} R₆ ⦄ where
  open VarSubBase varSub₁ using () renaming (VarSub to VarSub₁)
  open VarSubBase varSub₂ using () renaming (VarSub to VarSub₂)
  open VarSubBase varSub₃ using () renaming (VarSub to VarSub₃)

  record VarSubAppCompositional
    ⦃ _ : RawVarSubApp ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₄ ⦄ ⦄
    ⦃ _ : RawVarSubApp ⦃ varSub₁ ⦄ ⦃ varSub₅ ⦄ ⦃ varSub₆ ⦄ ⦄
    ⦃ _ : RawVarSubApp ⦃ varSub₂ ⦄ ⦃ varSub₃ ⦄ ⦃ varSub₅ ⦄ ⦄
    ⦃ _ : RawVarSubApp ⦃ varSub₄ ⦄ ⦃ varSub₃ ⦄ ⦃ varSub₆ ⦄ ⦄
    : Set (ℓ₀ ⊔ ℓ₁ ⊔ ℓ₂ ⊔ ℓ₃ ⊔ ℓ₆) where
    field
      ⟦-⟧ᵛ-compositional : ∀ (σ : VarSub₁ Ψ Δ) (τ : VarSub₂ Δ Γ) (M : R₃ Γ A) →
                           -----------------------------------------------------
                           ⟦ σ ⟧ᵛ ⟦ τ ⟧ᵛ M ≡ ⟦ σ ∘ᵛ τ ⟧ᵛ M

    opaque
      ∘ᵛ-assocᵛ : ∀ (σ : VarSub₁ Φ Ψ) (τ : VarSub₂ Ψ Δ) (υ : VarSub₃ Δ Γ) →
                  ----------------------------------------------------------
                  σ ∘ᵛ (τ ∘ᵛ υ) ≈ᵛ (σ ∘ᵛ τ) ∘ᵛ υ
      ∘ᵛ-assocᵛ _ _ υ x = ⟦-⟧ᵛ-compositional _ _ (υ x)

  open VarSubAppCompositional ⦃...⦄ public

module _
  ⦃ varSub₁ : VarSubBase {ℓ₁} R₁ ⦄
  ⦃ varSub₂ : VarSubBase {ℓ₂} R₂ ⦄ where
  open VarSubBase varSub₁ using () renaming (VarSub to VarSub₁)
  open VarSubBase varSub₂ using () renaming (_≈ᵛ_ to _≈ᵛ₂_)

  module _ ⦃ _ : RawVarSubLift ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦄ where
    opaque
      liftᵛ-congᵛ : liftᵛ∘ ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ Preserves _≈ᵛ_ {Δ = Δ} {Γ} ⟶ _≈ᵛ_
      liftᵛ-congᵛ equiv x = cong liftᵛ (equiv x)

  module _
    ⦃ _ : RawVarSubId ⦃ varSub₁ ⦄ ⦄
    ⦃ _ : RawVarSubId ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : RawVarSubWk ⦃ varSub₁ ⦄ ⦄
    ⦃ _ : RawVarSubWk ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : RawVarSubLift ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : VarSubWkSpec ⦃ varSub₁ ⦄ ⦄
    ⦃ _ : VarSubWkSpec ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : VarSubLiftId ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦄ where
    opaque
      liftᵛ-preserves-Wkᵛ : liftᵛ∘ ⦃ varSub₁ ⦄ Wkᵛ ≈ᵛ Wkᵛ ⦃ varSub₂ ⦄ {A = A} {Γ}
      liftᵛ-preserves-Wkᵛ x = trans (cong (liftᵛ ⦃ varSub₁ ⦄) (Wkᵛ-spec x)) (trans (liftᵛ-preserves-Idᵛ (there x)) (sym (Wkᵛ-spec x)))

  module _
    ⦃ _ : RawVarSubId ⦃ varSub₁ ⦄ ⦄
    ⦃ _ : RawVarSubId ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : RawVarSubOutHead ⦃ varSub₁ ⦄ ⦄
    ⦃ _ : RawVarSubOutHead ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : RawVarSubLift ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : VarSubOutHeadSpec ⦃ varSub₁ ⦄ ⦄
    ⦃ _ : VarSubOutHeadSpec ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : VarSubLiftId ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦄ where
    opaque
      liftᵛ-preserves-R-headᵛ : liftᵛ ⦃ varSub₁ ⦄ R-headᵛ ≡ R-headᵛ ⦃ varSub₂ ⦄ {A = A} {Γ}
      liftᵛ-preserves-R-headᵛ = trans (cong (liftᵛ ⦃ varSub₁ ⦄) (sym R-headᵛ-spec)) (trans (liftᵛ-preserves-Idᵛ (here refl)) R-headᵛ-spec)

  module _ ⦃ _ : RawVarSubLift ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦄ where
    opaque
      liftᵛ-preserves-,ᵛ : ∀ (σ : VarSub₁ Δ Γ) (M : R₁ _ A) →
                           ----------------------------------------
                           liftᵛ∘ (σ ,ᵛ M) ≈ᵛ₂ liftᵛ∘ σ ,ᵛ liftᵛ M
      liftᵛ-preserves-,ᵛ σ M (here refl) = refl
      liftᵛ-preserves-,ᵛ σ M (there x)   = refl

module _
  ⦃ varSub₁ : VarSubBase {ℓ₁} R₁ ⦄
  ⦃ varSub₂ : VarSubBase {ℓ₂} R₂ ⦄
  ⦃ varSub₃ : VarSubBase {ℓ₃} R₃ ⦄ where
  open VarSubBase varSub₁ using () renaming (VarSub to VarSub₁)
  open VarSubBase varSub₂ using () renaming (_≈ᵛ_ to _≈ᵛ₂_)
  open VarSubBase varSub₃ using () renaming (_≈ᵛ_ to _≈ᵛ₃_)

  module _
    ⦃ _ : RawVarSubId ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : RawVarSubWk ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : RawVarSubLift ⦃ varSub₁ ⦄ ⦃ varSub₃ ⦄ ⦄
    ⦃ _ : RawVarSubApp ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₃ ⦄ ⦄
    ⦃ _ : VarSubWkSpec ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : VarSubIdNoOpʳ ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₃ ⦄ ⦄ where
    opaque
      ∘ᵛWkᵛ-cancel-,ᵛ : ∀ (σ : VarSub₁ Δ Γ) (M : R₁ _ A) →
                        ----------------------------------------
                        (σ ,ᵛ M) ∘ᵛ Wkᵛ ⦃ varSub₂ ⦄ ≈ᵛ liftᵛ∘ σ
      ∘ᵛWkᵛ-cancel-,ᵛ σ M x = trans (cong (λ x → Appᵛ (σ ,ᵛ M) x) (Wkᵛ-spec x)) (Idᵛ-idʳ (σ ,ᵛ M) (there x))

  module _
    ⦃ _ : RawVarSubId ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : RawVarSubOutHead ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : RawVarSubLift ⦃ varSub₁ ⦄ ⦃ varSub₃ ⦄ ⦄
    ⦃ _ : RawVarSubApp ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₃ ⦄ ⦄
    ⦃ _ : VarSubOutHeadSpec ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : VarSubIdNoOpʳ ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₃ ⦄ ⦄ where
    opaque
      Appᵛ-R-headᵛ : ∀ (σ : VarSub₁ Δ (A ∷ Γ)) →
                     -----------------------------------------------------
                     ⟦ σ ⟧ᵛ (R-headᵛ ⦃ varSub₂ ⦄) ≡ liftᵛ (σ (here refl))
      Appᵛ-R-headᵛ σ = trans (cong (λ x → ⟦ σ ⟧ᵛ x) (sym R-headᵛ-spec)) (Idᵛ-idʳ σ (here refl))

  module _
    ⦃ _ : RawVarSubApp ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₃ ⦄ ⦄ where
    opaque
      ∘ᵛ-congᵛʳ : ∀ (σ : VarSub₁ Ψ _) →
                  -------------------------------------------
                  _∘ᵛ_ σ Preserves _≈ᵛ₂_ {Δ = Δ} {Γ} ⟶ _≈ᵛ₃_
      ∘ᵛ-congᵛʳ σ equivτ x = cong (λ x → ⟦ σ ⟧ᵛ x) (equivτ x)

module _
  ⦃ varSub₁ : VarSubBase {ℓ₁} R₁ ⦄
  ⦃ varSub₂ : VarSubBase {ℓ₂} R₂ ⦄ where
  open VarSubBase varSub₂ using () renaming (_≈ᵛ_ to _≈ᵛ₂_)

  module _
    ⦃ _ : RawVarSubWk ⦃ varSub₁ ⦄ ⦄
    ⦃ _ : RawVarSubOutHead ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : RawVarSubApp ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₂ ⦄ ⦄ where
    opaque
      qᵛ-congᵛ : qᵛ_ Preserves _≈ᵛ₂_ {Δ = Δ} {Γ} ⟶ _≈ᵛ₂_ {Δ = A ∷ Δ}
      qᵛ-congᵛ equiv = ,ᵛ-congᵛˡ R-headᵛ (∘ᵛ-congᵛʳ Wkᵛ equiv)

  module _ ⦃ _ : RawVarSubId ⦃ varSub₁ ⦄ ⦄
           ⦃ _ : RawVarSubId ⦃ varSub₂ ⦄ ⦄
           ⦃ _ : RawVarSubWk ⦃ varSub₁ ⦄ ⦄
           ⦃ _ : RawVarSubOutHead ⦃ varSub₂ ⦄ ⦄
           ⦃ _ : RawVarSubLift ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦄
           ⦃ _ : RawVarSubApp ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₂ ⦄ ⦄
           ⦃ _ : RawVarSubApp ⦃ varSub₂ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₂ ⦄ ⦄
           ⦃ _ : VarSubWkSpec ⦃ varSub₂ ⦄ ⦄
           ⦃ _ : VarSubOutHeadSpec ⦃ varSub₂ ⦄ ⦄
           ⦃ _ : VarSubIdNoOpˡ ⦃ varSub₂ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₂ ⦄ ⦄
           ⦃ _ : VarSubIdNoOpʳ ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₂ ⦄ ⦄
           ⦃ _ : VarSubIdNoOpʳ ⦃ varSub₂ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₂ ⦄ ⦄ where
    opaque
      qᵛ-preserves-Idᵛ : qᵛ Idᵛ ≈ᵛ₂ Idᵛ {Γ = A ∷ Γ}
      qᵛ-preserves-Idᵛ (here refl) = trans (sym (⟦Idᵛ⟧ᵛ≡liftᵛ ⦃ varSub₂ ⦄ (R-headᵛ ⦃ varSub₂ ⦄))) (Appᵛ-R-headᵛ ⦃ varSub₂ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₂ ⦄ (Idᵛ ⦃ varSub₂ ⦄))
      qᵛ-preserves-Idᵛ (there x)   = trans (Idᵛ-idʳ ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ (Wkᵛ ⦃ varSub₁ ⦄) x) (Wkᵛ-spec x)

module _
  ⦃ varSub₁ : VarSubBase R₁ ⦄
  ⦃ varSub₂ : VarSubBase R₂ ⦄
  ⦃ varSub₃ : VarSubBase R₃ ⦄ where
  open VarSubBase varSub₁ using () renaming (VarSub to VarSub₁)
  open VarSubBase varSub₂ using () renaming (VarSub to VarSub₂)
  open VarSubBase varSub₃ using () renaming (_≈ᵛ_ to _≈ᵛ₃_)

  module _ ⦃ _ : RawVarSubApp ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₃ ⦄ ⦄ where
    opaque
      ∘ᵛ-distrib-,ᵛ : ∀ {σ : VarSub₁ Ψ Δ} {τ : VarSub₂ _ Γ} (M : R₂ _ A) →
                      -----------------------------------------------------
                      σ ∘ᵛ τ ,ᵛ M ≈ᵛ₃ (σ ∘ᵛ τ) ,ᵛ ⟦ σ ⟧ᵛ M
      ∘ᵛ-distrib-,ᵛ _ (here refl) = refl
      ∘ᵛ-distrib-,ᵛ _ (there x)   = refl

module _
  ⦃ varSub₁ : VarSubBase R₁ ⦄
  ⦃ varSub₂ : VarSubBase R₂ ⦄
  ⦃ varSub₃ : VarSubBase R₃ ⦄ where
  open VarSubBase varSub₂ using () renaming (VarSub to VarSub₂)
  open VarSubBase varSub₃ using () renaming (_≈ᵛ_ to _≈ᵛ₃_)

  module _
    ⦃ _ : RawVarSubId ⦃ varSub₁ ⦄ ⦄
    ⦃ _ : RawVarSubId ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : RawVarSubId ⦃ varSub₃ ⦄ ⦄
    ⦃ _ : RawVarSubWk ⦃ varSub₁ ⦄ ⦄
    ⦃ _ : RawVarSubOutHead ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : RawVarSubLift ⦃ varSub₂ ⦄ ⦃ varSub₃ ⦄ ⦄
    ⦃ _ : RawVarSubApp ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : RawVarSubApp ⦃ varSub₃ ⦄ ⦃ varSub₁ ⦄ ⦃ varSub₃ ⦄ ⦄
    ⦃ _ : RawVarSubApp ⦃ varSub₃ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₃ ⦄ ⦄
    ⦃ _ : VarSubWkSpec ⦃ varSub₁ ⦄ ⦄
    ⦃ _ : VarSubOutHeadSpec ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : VarSubIdNoOpˡ ⦃ varSub₃ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₃ ⦄ ⦄
    ⦃ _ : VarSubIdNoOpʳ ⦃ varSub₃ ⦄ ⦃ varSub₁ ⦄ ⦃ varSub₃ ⦄ ⦄
    ⦃ _ : VarSubIdNoOpʳ ⦃ varSub₃ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₃ ⦄ ⦄
    ⦃ _ : VarSubAppExtensional ⦃ varSub₃ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₃ ⦄ ⦄
    ⦃ _ : VarSubAppCompositional ⦃ varSub₃ ⦄ ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦄ where
    opaque
      !ᵛ-∘ᵛ-qᵛ : ∀ (σ : VarSub₂ Γ Δ) (M : R₃ Γ A) →
                 !ᵛ M ∘ᵛ qᵛ σ ≈ᵛ₃ liftᵛ∘ σ ,ᵛ M
      !ᵛ-∘ᵛ-qᵛ σ M =
        begin !ᵛ M ∘ᵛ qᵛ σ                              ≈⟨ ∘ᵛ-distrib-,ᵛ R-headᵛ ⟩
              (!ᵛ M ∘ᵛ (Wkᵛ ∘ᵛ σ)) ,ᵛ ⟦ !ᵛ M ⟧ᵛ R-headᵛ ≈⟨ ,ᵛ-congᵛ (∘ᵛ-assocᵛ (!ᵛ M) _ σ) (Appᵛ-R-headᵛ (!ᵛ M)) ⟩
              ((!ᵛ M ∘ᵛ Wkᵛ) ∘ᵛ σ) ,ᵛ M                 ≈⟨ ,ᵛ-congᵛˡ M (∘ᵛ-congᵛˡ σ (∘ᵛWkᵛ-cancel-,ᵛ Idᵛ M)) ⟩
              (Idᵛ ∘ᵛ σ) ,ᵛ M                           ≈⟨ ,ᵛ-congᵛˡ M (Idᵛ-idˡ σ) ⟩
              liftᵛ∘ σ ,ᵛ M                             ∎
        where
          open VarSub-Reasoning ⦃ varSub₃ ⦄ _ _

module _
  ⦃ varSub₁ : VarSubBase R₁ ⦄
  ⦃ varSub₂ : VarSubBase R₂ ⦄
  ⦃ varSub₃ : VarSubBase R₃ ⦄
  ⦃ varSub₄ : VarSubBase R₄ ⦄ where
  open VarSubBase varSub₂ using () renaming (VarSub to VarSub₂)
  open VarSubBase varSub₃ using () renaming (VarSub to VarSub₃)
  open VarSubBase varSub₄ using () renaming (_≈ᵛ_ to _≈ᵛ₄_)

  module _
    ⦃ _ : RawVarSubId ⦃ varSub₁ ⦄ ⦄
    ⦃ _ : RawVarSubId ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : RawVarSubId ⦃ varSub₃ ⦄ ⦄
    ⦃ _ : RawVarSubId ⦃ varSub₄ ⦄ ⦄
    ⦃ _ : RawVarSubWk ⦃ varSub₁ ⦄ ⦄
    ⦃ _ : RawVarSubOutHead ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : RawVarSubOutHead ⦃ varSub₃ ⦄ ⦄
    ⦃ _ : RawVarSubOutHead ⦃ varSub₄ ⦄ ⦄
    ⦃ _ : RawVarSubLift ⦃ varSub₂ ⦄ ⦃ varSub₄ ⦄ ⦄
    ⦃ _ : RawVarSubApp ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : RawVarSubApp ⦃ varSub₁ ⦄ ⦃ varSub₃ ⦄ ⦃ varSub₃ ⦄ ⦄
    ⦃ _ : RawVarSubApp ⦃ varSub₁ ⦄ ⦃ varSub₄ ⦄ ⦃ varSub₄ ⦄ ⦄
    ⦃ _ : RawVarSubApp ⦃ varSub₂ ⦄ ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : RawVarSubApp ⦃ varSub₂ ⦄ ⦃ varSub₃ ⦄ ⦃ varSub₄ ⦄ ⦄
    ⦃ _ : VarSubWkSpec ⦃ varSub₁ ⦄ ⦄
    ⦃ _ : VarSubOutHeadSpec ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : VarSubOutHeadSpec ⦃ varSub₃ ⦄ ⦄
    ⦃ _ : VarSubOutHeadSpec ⦃ varSub₄ ⦄ ⦄
    ⦃ _ : VarSubLiftId ⦃ varSub₂ ⦄ ⦃ varSub₄ ⦄ ⦄
    ⦃ _ : VarSubIdNoOpʳ ⦃ varSub₂ ⦄ ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : VarSubIdNoOpʳ ⦃ varSub₂ ⦄ ⦃ varSub₃ ⦄ ⦃ varSub₄ ⦄ ⦄
    ⦃ _ : VarSubAppExtensional ⦃ varSub₂ ⦄ ⦃ varSub₃ ⦄ ⦃ varSub₄ ⦄ ⦄
    ⦃ _ : VarSubAppCompositional ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₃ ⦄ ⦄
    ⦃ _ : VarSubAppCompositional ⦃ varSub₂ ⦄ ⦃ varSub₁ ⦄ ⦃ varSub₃ ⦄ ⦄ where

    opaque
      qᵛ-distrib-∘ᵛ : ∀ (σ : VarSub₂ Ψ Δ) (τ : VarSub₃ Δ Γ) →
                      qᵛ_ {A = A} (σ ∘ᵛ τ) ≈ᵛ₄ qᵛ σ ∘ᵛ qᵛ τ
      qᵛ-distrib-∘ᵛ {Ψ = Ψ} {Δ = Δ} {A = A} σ τ =
        begin qᵛ (σ ∘ᵛ τ)                              ≈⟨ ,ᵛ-congᵛˡ R-headᵛ (∘ᵛ-assocᵛ Wkᵛ σ τ) ⟩
              ((Wkᵛ ∘ᵛ σ) ∘ᵛ τ) ,ᵛ R-headᵛ             ≈˘⟨ ,ᵛ-congᵛˡ R-headᵛ (∘ᵛ-congᵛˡ τ (∘ᵛWkᵛ-cancel-,ᵛ (Wkᵛ ∘ᵛ σ) R-headᵛ₂)) ⟩
              ((qᵛ σ ∘ᵛ Wkᵛ) ∘ᵛ τ) ,ᵛ R-headᵛ          ≈˘⟨ ,ᵛ-congᵛˡ R-headᵛ (∘ᵛ-assocᵛ (qᵛ σ) Wkᵛ τ) ⟩
              (qᵛ σ ∘ᵛ Wkᵛ ∘ᵛ τ) ,ᵛ R-headᵛ            ≈˘⟨ ,ᵛ-congᵛʳ (qᵛ σ ∘ᵛ Wkᵛ ∘ᵛ τ) liftᵛ-preserves-R-headᵛ ⟩
              (qᵛ σ ∘ᵛ Wkᵛ ∘ᵛ τ) ,ᵛ liftᵛ R-headᵛ₂     ≈˘⟨ ,ᵛ-congᵛʳ (qᵛ σ ∘ᵛ Wkᵛ ∘ᵛ τ) (Appᵛ-R-headᵛ (qᵛ σ)) ⟩
              (qᵛ σ ∘ᵛ Wkᵛ ∘ᵛ τ) ,ᵛ ⟦ qᵛ σ ⟧ᵛ R-headᵛ₃ ≈˘⟨ ∘ᵛ-distrib-,ᵛ {σ = qᵛ σ} R-headᵛ₃ ⟩
              qᵛ σ ∘ᵛ qᵛ τ                             ∎
        where
          R-headᵛ₂ : R₂ (A ∷ Ψ) A
          R-headᵛ₂ = R-headᵛ ⦃ varSub₂ ⦄
          R-headᵛ₃ : R₃ (A ∷ Δ) A
          R-headᵛ₃ = R-headᵛ ⦃ varSub₃ ⦄
          open VarSub-Reasoning ⦃ varSub₄ ⦄ _ _

  module _
    ⦃ _ : RawVarSubId ⦃ varSub₁ ⦄ ⦄
    ⦃ _ : RawVarSubId ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : RawVarSubId ⦃ varSub₃ ⦄ ⦄
    ⦃ _ : RawVarSubId ⦃ varSub₄ ⦄ ⦄
    ⦃ _ : RawVarSubWk ⦃ varSub₁ ⦄ ⦄
    ⦃ _ : RawVarSubOutHead ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : RawVarSubLift ⦃ varSub₂ ⦄ ⦃ varSub₄ ⦄ ⦄
    ⦃ _ : RawVarSubApp ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : RawVarSubApp ⦃ varSub₂ ⦄ ⦃ varSub₃ ⦄ ⦃ varSub₄ ⦄ ⦄
    ⦃ _ : RawVarSubApp ⦃ varSub₄ ⦄ ⦃ varSub₁ ⦄ ⦃ varSub₄ ⦄ ⦄
    ⦃ _ : RawVarSubApp ⦃ varSub₄ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₄ ⦄ ⦄
    ⦃ _ : VarSubWkSpec ⦃ varSub₁ ⦄ ⦄
    ⦃ _ : VarSubOutHeadSpec ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : VarSubIdNoOpˡ ⦃ varSub₄ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₄ ⦄ ⦄
    ⦃ _ : VarSubIdNoOpʳ ⦃ varSub₂ ⦄ ⦃ varSub₃ ⦄ ⦃ varSub₄ ⦄ ⦄
    ⦃ _ : VarSubIdNoOpʳ ⦃ varSub₄ ⦄ ⦃ varSub₁ ⦄ ⦃ varSub₄ ⦄ ⦄
    ⦃ _ : VarSubIdNoOpʳ ⦃ varSub₄ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₄ ⦄ ⦄
    ⦃ _ : VarSubAppExtensional ⦃ varSub₄ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₄ ⦄ ⦄
    ⦃ _ : VarSubAppCompositional ⦃ varSub₄ ⦄ ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦄ where
    opaque
      !ᵛ⟦-⟧-∘ᵛ-qᵛ : ∀ (σ : VarSub₂ Γ Δ) (M : R₃ Δ A) →
                    !ᵛ ⟦ σ ⟧ᵛ M ∘ᵛ qᵛ σ ≈ᵛ₄ σ ∘ᵛ !ᵛ M
      !ᵛ⟦-⟧-∘ᵛ-qᵛ σ M =
        begin !ᵛ ⟦ σ ⟧ᵛ M ∘ᵛ qᵛ σ    ≈⟨ !ᵛ-∘ᵛ-qᵛ σ (⟦ σ ⟧ᵛ M) ⟩
              liftᵛ∘ σ ,ᵛ ⟦ σ ⟧ᵛ M   ≈˘⟨ ,ᵛ-congᵛˡ (⟦ σ ⟧ᵛ M) (Idᵛ-idʳ σ) ⟩
              (σ ∘ᵛ Idᵛ) ,ᵛ ⟦ σ ⟧ᵛ M ≈˘⟨ ∘ᵛ-distrib-,ᵛ M ⟩
              σ ∘ᵛ !ᵛ M              ∎
        where
          open VarSub-Reasoning ⦃ varSub₄ ⦄ _ _

  module _
    ⦃ _ : RawVarSubId ⦃ varSub₁ ⦄ ⦄
    ⦃ _ : RawVarSubId ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : RawVarSubId ⦃ varSub₃ ⦄ ⦄
    ⦃ _ : RawVarSubId ⦃ varSub₄ ⦄ ⦄
    ⦃ _ : RawVarSubWk ⦃ varSub₁ ⦄ ⦄
    ⦃ _ : RawVarSubOutHead ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : RawVarSubLift ⦃ varSub₂ ⦄ ⦃ varSub₄ ⦄ ⦄
    ⦃ _ : RawVarSubApp ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : RawVarSubApp ⦃ varSub₂ ⦄ ⦃ varSub₃ ⦄ ⦃ varSub₄ ⦄ ⦄
    ⦃ _ : RawVarSubApp ⦃ varSub₃ ⦄ ⦃ varSub₃ ⦄ ⦃ varSub₃ ⦄ ⦄
    ⦃ _ : RawVarSubApp ⦃ varSub₄ ⦄ ⦃ varSub₁ ⦄ ⦃ varSub₄ ⦄ ⦄
    ⦃ _ : RawVarSubApp ⦃ varSub₄ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₄ ⦄ ⦄
    ⦃ _ : RawVarSubApp ⦃ varSub₄ ⦄ ⦃ varSub₃ ⦄ ⦃ varSub₄ ⦄ ⦄
    ⦃ _ : RawVarSubApp ⦃ varSub₄ ⦄ ⦃ varSub₄ ⦄ ⦃ varSub₄ ⦄ ⦄
    ⦃ _ : VarSubWkSpec ⦃ varSub₁ ⦄ ⦄
    ⦃ _ : VarSubOutHeadSpec ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : VarSubIdNoOpˡ ⦃ varSub₄ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₄ ⦄ ⦄
    ⦃ _ : VarSubIdNoOpʳ ⦃ varSub₂ ⦄ ⦃ varSub₃ ⦄ ⦃ varSub₄ ⦄ ⦄
    ⦃ _ : VarSubIdNoOpʳ ⦃ varSub₄ ⦄ ⦃ varSub₁ ⦄ ⦃ varSub₄ ⦄ ⦄
    ⦃ _ : VarSubIdNoOpʳ ⦃ varSub₄ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₄ ⦄ ⦄
    ⦃ _ : VarSubAppExtensional ⦃ varSub₄ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₄ ⦄ ⦄
    ⦃ _ : VarSubAppExtensional ⦃ varSub₄ ⦄ ⦃ varSub₃ ⦄ ⦃ varSub₄ ⦄ ⦄
    ⦃ _ : VarSubAppCompositional ⦃ varSub₂ ⦄ ⦃ varSub₃ ⦄ ⦃ varSub₃ ⦄ ⦄
    ⦃ _ : VarSubAppCompositional ⦃ varSub₄ ⦄ ⦃ varSub₁ ⦄ ⦃ varSub₂ ⦄ ⦄
    ⦃ _ : VarSubAppCompositional ⦃ varSub₄ ⦄ ⦃ varSub₂ ⦄ ⦃ varSub₃ ⦄ ⦄ where
    opaque
      ⟦!ᵛ⟦-⟧ᵛ-⟧ᵛ⟦qᵛ-⟧ᵛ≡⟦-⟧ᵛ⟦!ᵛ-⟧ᵛ : ∀ (δ : VarSub₂ Γ Δ) (N : R₃ Δ A) (M : R₃ (A ∷ Δ) B) →
                                    ⟦ !ᵛ ⟦ δ ⟧ᵛ N ⟧ᵛ ⟦ qᵛ δ ⟧ᵛ M ≡ ⟦ δ ⟧ᵛ ⟦ !ᵛ N ⟧ᵛ M
      ⟦!ᵛ⟦-⟧ᵛ-⟧ᵛ⟦qᵛ-⟧ᵛ≡⟦-⟧ᵛ⟦!ᵛ-⟧ᵛ δ f e =
        begin _ ≡⟨ ⟦-⟧ᵛ-compositional (!ᵛ ⟦ δ ⟧ᵛ f) (qᵛ δ) e ⟩
              _ ≡⟨ ⟦-⟧ᵛ-extensional e (!ᵛ⟦-⟧-∘ᵛ-qᵛ δ f) ⟩
              _ ≡˘⟨ ⟦-⟧ᵛ-compositional _ (!ᵛ f) e ⟩
              _ ∎
        where
          open ≡-Reasoning
