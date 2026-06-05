{-# OPTIONS --safe #-}
module SN.LogRel.STLC where

open import Agda.Primitive using (Level; lzero)
open import Data.Empty as ⊥
open import Data.List as List hiding ([_])
open import Data.List.Membership.Propositional as List
import Data.List.Properties as List
open import Data.List.Relation.Unary.Any as Any using (here; there)
import Data.List.Relation.Unary.Any.Properties as Any
open import Data.Nat as ℕ
import Data.Nat.Properties as ℕ
open import Data.Product as Σ
open import Data.Sum as ⊎
open import Data.Unit as ⊤
open import Function.Base
open import Function.Core using (Morphism)
open import Induction.WellFounded using (WellFounded; Acc; acc; acc-inverse)
open import Relation.Binary using (IsEquivalence; REL; Rel; Setoid; Symmetric; Trans; Transitive; _Preserves_⟶_; _Preserves₂_⟶_⟶_; _=[_]⇒_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_)
import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties as Star
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure; [_]; _∷_)
import Relation.Binary.Construct.Closure.Transitive as TransClosure
open import Relation.Binary.Construct.Union using (_∪_)
open import Relation.Binary.PropositionalEquality hiding (J)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Relation.Unary using (Pred)

variable
  ℓ ℓ′ ℓ″ : Level

module Syntax where
  data Tp : Set where
    base : Tp
    _`→_ : Tp → Tp → Tp

  Ctx : Set
  Ctx = List Tp

  variable
    A A′ A′₀ A′₁ A′₂ A′₃ A″ A″₀ A″₁ A″₂ A″₃ A‴ A‴₀ A‴₁ A‴₂ A‴₃ A₀ A₁ A₂ A₃ : Tp
    B B′ B′₀ B′₁ B′₂ B′₃ B″ B″₀ B″₁ B″₂ B″₃ B‴ B‴₀ B‴₁ B‴₂ B‴₃ B₀ B₁ B₂ B₃ : Tp
    C C′ C′₀ C′₁ C′₂ C′₃ C″ C″₀ C″₁ C″₂ C″₃ C‴ C‴₀ C‴₁ C‴₂ C‴₃ C₀ C₁ C₂ C₃ : Tp
    Γ Γ′ Γ′₀ Γ′₁ Γ′₂ Γ′₃ Γ″ Γ″₀ Γ″₁ Γ″₂ Γ″₃ Γ‴ Γ‴₀ Γ‴₁ Γ‴₂ Γ‴₃ Γ₀ Γ₁ Γ₂ Γ₃ : Ctx
    Δ Δ′ Δ′₀ Δ′₁ Δ′₂ Δ′₃ Δ″ Δ″₀ Δ″₁ Δ″₂ Δ″₃ Δ‴ Δ‴₀ Δ‴₁ Δ‴₂ Δ‴₃ Δ₀ Δ₁ Δ₂ Δ₃ : Ctx
    Ψ Ψ′ Ψ′₀ Ψ′₁ Ψ′₂ Ψ′₃ Ψ″ Ψ″₀ Ψ″₁ Ψ″₂ Ψ″₃ Ψ‴ Ψ‴₀ Ψ‴₁ Ψ‴₂ Ψ‴₃ Ψ₀ Ψ₁ Ψ₂ Ψ₃ : Ctx

  data Tm : REL Ctx Tp lzero where
    `#_       : (x : A ∈ Γ) →
                --------------
                Tm Γ A

    `λ_       : Tm (A ∷ Γ) B →
                ---------------
                Tm Γ (A `→ B)

    _`$_      : (M : Tm Γ (A `→ B)) →
                (N : Tm Γ A) →
                ----------------------
                Tm Γ B

  pattern `#zero  = `# (here refl)
  pattern `#suc x = `# (there x)

  pattern `#0 = `#zero
  pattern `#1 = `#suc (here refl)
  pattern `#2 = `#suc (there (here refl))
  pattern `#3 = `#suc (there (there (here refl)))

  variable
    x x′ x′₀ x′₁ x′₂ x′₃ x″ x″₀ x″₁ x″₂ x″₃ x‴ x‴₀ x‴₁ x‴₂ x‴₃ x₀ x₁ x₂ x₃ : A ∈ Γ
    y y′ y′₀ y′₁ y′₂ y′₃ y″ y″₀ y″₁ y″₂ y″₃ y‴ y‴₀ y‴₁ y‴₂ y‴₃ y₀ y₁ y₂ y₃ : A ∈ Γ
    z z′ z′₀ z′₁ z′₂ z′₃ z″ z″₀ z″₁ z″₂ z″₃ z‴ z‴₀ z‴₁ z‴₂ z‴₃ z₀ z₁ z₂ z₃ : A ∈ Γ
    M M′ M′₀ M′₁ M′₂ M′₃ M″ M″₀ M″₁ M″₂ M″₃ M‴ M‴₀ M‴₁ M‴₂ M‴₃ M₀ M₁ M₂ M₃ : Tm Γ A
    N N′ N′₀ N′₁ N′₂ N′₃ N″ N″₀ N″₁ N″₂ N″₃ N‴ N‴₀ N‴₁ N‴₂ N‴₃ N₀ N₁ N₂ N₃ : Tm Γ A
    L L′ L′₀ L′₁ L′₂ L′₃ L″ L″₀ L″₁ L″₂ L″₃ L‴ L‴₀ L‴₁ L‴₂ L‴₃ L₀ L₁ L₂ L₃ : Tm Γ A

  ----------------------------------------------------------
  -- Extensions (i.e. Renamings)
  ----------------------------------------------------------

  Ext : Rel Ctx _
  Ext Γ Δ = ∀ {A} → A ∈ Δ → A ∈ Γ

  variable
    γ γ′ γ′₀ γ′₁ γ′₂ γ′₃ γ″ γ″₀ γ″₁ γ″₂ γ″₃ γ‴ γ‴₀ γ‴₁ γ‴₂ γ‴₃ γ₀ γ₁ γ₂ γ₃ : Ext Γ Δ
    δ δ′ δ′₀ δ′₁ δ′₂ δ′₃ δ″ δ″₀ δ″₁ δ″₂ δ″₃ δ‴ δ‴₀ δ‴₁ δ‴₂ δ‴₃ δ₀ δ₁ δ₂ δ₃ : Ext Γ Δ
    ρ ρ′ ρ′₀ ρ′₁ ρ′₂ ρ′₃ ρ″ ρ″₀ ρ″₁ ρ″₂ ρ″₃ ρ‴ ρ‴₀ ρ‴₁ ρ‴₂ ρ‴₃ ρ₀ ρ₁ ρ₂ ρ₃ : Ext Γ Δ

  ----------------------------------------------------------
  -- Useful Constructions for Extensions
  ----------------------------------------------------------

  infix 4 _≈ᵉ_
  _≈ᵉ_ : Rel (Ext Δ Γ) _
  δ ≈ᵉ δ′ = ∀ {A} (x : A ∈ _) → δ x ≡ δ′ x

  Wkᵉ : ∀ Δ → Ext (Δ ++ Γ) Γ
  Wkᵉ []      = id
  Wkᵉ (_ ∷ Δ) = there ∘ Wkᵉ Δ

  Wk1ᵉ : Ext (A ∷ Γ) Γ
  Wk1ᵉ = Wkᵉ (_ ∷ [])

  Idᵉ : Ext Γ Γ
  Idᵉ = Wkᵉ []

  infixl 6 _,ᵉ_
  _,ᵉ_ : Ext Δ Γ → A ∈ Δ → Ext Δ (A ∷ Γ)
  (δ ,ᵉ x) (here eq) = subst (_∈ _) (sym eq) x
  (δ ,ᵉ x) (there y) = δ y

  infixr 5 _∘ᵉ_
  _∘ᵉ_ : Ext Ψ Δ → Ext Δ Γ → Ext Ψ Γ
  δ ∘ᵉ δ′ = δ ∘ δ′

  infixr 7 qᵉ_
  qᵉ_ : Ext Δ Γ → Ext (A ∷ Δ) (A ∷ Γ)
  qᵉ_ δ = (Wk1ᵉ ∘ᵉ δ) ,ᵉ here refl

  infixr 7 qᵉ[_]_
  qᵉ[_]_ : ∀ Ψ → Ext Δ Γ → Ext (Ψ ++ Δ) (Ψ ++ Γ)
  qᵉ[ []    ] δ = δ
  qᵉ[ _ ∷ Ψ ] δ = qᵉ qᵉ[ Ψ ] δ

  ----------------------------------------------------------
  -- Extension Application
  ----------------------------------------------------------

  infixr 30 ext[_]_
  ext[_]_ : Ext Γ Δ → Tm Δ A → Tm Γ A
  ext[ δ ] (`# x)   = `# δ x
  ext[ δ ] (`λ M)   = `λ ext[ qᵉ δ ] M
  ext[ δ ] (M `$ N) = ext[ δ ] M `$ ext[ δ ] N

  infixr 30 ext_
  ext_ : Tm Γ A → Tm (B ∷ Γ) A
  ext_ = ext[ Wk1ᵉ ]_

  ----------------------------------------------------------
  -- (Simultaneous) Substitutions
  ----------------------------------------------------------

  Sub : Rel Ctx _
  Sub Γ Δ = ∀ {A} → A ∈ Δ → Tm Γ A

  variable
    σ σ′ σ′₀ σ′₁ σ′₂ σ′₃ σ″ σ″₀ σ″₁ σ″₂ σ″₃ σ‴ σ‴₀ σ‴₁ σ‴₂ σ‴₃ σ₀ σ₁ σ₂ σ₃ : Sub Γ Δ
    τ τ′ τ′₀ τ′₁ τ′₂ τ′₃ τ″ τ″₀ τ″₁ τ″₂ τ″₃ τ‴ τ‴₀ τ‴₁ τ‴₂ τ‴₃ τ₀ τ₁ τ₂ τ₃ : Sub Γ Δ

  ----------------------------------------------------------
  -- Useful Constructions for Substitutions
  ----------------------------------------------------------

  infix 4 _≈ˢ_
  _≈ˢ_ : Rel (Sub Δ Γ) _
  σ ≈ˢ σ′ = ∀ {A} (x : A ∈ _) → σ x ≡ σ′ x

  forgetˢ : Ext Δ Γ → Sub Δ Γ
  forgetˢ δ = `#_ ∘ δ

  Idˢ : Sub Γ Γ
  Idˢ = forgetˢ Idᵉ

  infixl 6 _,ˢ_
  _,ˢ_ : Sub Δ Γ → Tm Δ A → Sub Δ (A ∷ Γ)
  (σ ,ˢ M) (here eq) = subst (Tm _) (sym eq) M
  (σ ,ˢ M) (there x) = σ x

  infixr 5 _ˢ∘ᵉ_
  _ˢ∘ᵉ_ : Sub Ψ Δ → Ext Δ Γ → Sub Ψ Γ
  σ ˢ∘ᵉ δ = σ ∘ δ

  infixr 5 _ᵉ∘ˢ_
  _ᵉ∘ˢ_ : Ext Ψ Δ → Sub Δ Γ → Sub Ψ Γ
  δ ᵉ∘ˢ σ = ext[ δ ]_ ∘ σ

  infixr 7 qˢ_
  qˢ_ : Sub Δ Γ → Sub (A ∷ Δ) (A ∷ Γ)
  qˢ σ = (Wk1ᵉ ᵉ∘ˢ σ) ,ˢ `#zero

  infixr 7 qˢ[_]_
  qˢ[_]_ : ∀ Ψ → Sub Δ Γ → Sub (Ψ ++ Δ) (Ψ ++ Γ)
  qˢ[ []    ] σ = σ
  qˢ[ _ ∷ Ψ ] σ = qˢ qˢ[ Ψ ] σ

  infixr 7 !ˢ_
  !ˢ_ : Tm Γ A → Sub Γ (A ∷ Γ)
  !ˢ M = Idˢ ,ˢ M

  ----------------------------------------------------------
  -- Substitution Application
  ----------------------------------------------------------

  infixr 30 [|_|]_
  [|_|]_ : Sub Γ Δ → Tm Δ A → Tm Γ A
  [| σ |] (`# x)   = σ x
  [| σ |] (`λ M)   = `λ [| qˢ σ |] M
  [| σ |] (M `$ N) = [| σ |] M `$ [| σ |] N

  infixr 5 _∘ˢ_
  _∘ˢ_ : Sub Ψ Δ → Sub Δ Γ → Sub Ψ Γ
  σ ∘ˢ σ′ = [| σ |]_ ∘ σ′

  module Properties where
    ----------------------------------------------------------
    -- Equivalence of Extensions
    ----------------------------------------------------------
    reflexiveᵉ : (δ : Ext Δ Γ) → δ ≈ᵉ δ
    reflexiveᵉ δ x = refl

    symᵉ : Symmetric (_≈ᵉ_ {Δ} {Γ})
    symᵉ = sym ∘_

    transᵉ : Transitive (_≈ᵉ_ {Δ} {Γ})
    transᵉ equiv equiv′ x = trans (equiv x) (equiv′ x)

    ≈ᵉ-IsEquivalence : ∀ Δ Γ → IsEquivalence (_≈ᵉ_ {Δ} {Γ})
    ≈ᵉ-IsEquivalence Δ Γ = record { refl = λ x → refl ; sym = symᵉ ; trans = transᵉ }

    Ext-Setoid : Ctx → Ctx → Setoid lzero lzero
    Ext-Setoid Δ Γ = record
      { Carrier = Ext Δ Γ
      ; _≈_ = _≈ᵉ_
      ; isEquivalence = ≈ᵉ-IsEquivalence Δ Γ
      }

    module Ext-Reasoning Δ Γ = SetoidReasoning (Ext-Setoid Δ Γ)

    ----------------------------------------------------------
    -- Useful Properties for Equivalence of Extensions
    ----------------------------------------------------------

    ,ᵉ-congᵉ : flip _,ᵉ_ x Preserves _≈ᵉ_ {Δ} {Γ} ⟶ _≈ᵉ_
    ,ᵉ-congᵉ equiv (here _)  = refl
    ,ᵉ-congᵉ equiv (there y) = equiv y

    ∘ᵉ-congᵉ : _∘ᵉ_ Preserves₂ _≈ᵉ_ {Ψ} ⟶ _≈ᵉ_ {Δ} {Γ} ⟶ _≈ᵉ_
    ∘ᵉ-congᵉ equivδ equivγ x
      rewrite equivγ x = equivδ _

    ∘ᵉ-congᵉˡ : (γ : Ext Δ Γ) → flip _∘ᵉ_ γ Preserves _≈ᵉ_ {Ψ} ⟶ _≈ᵉ_
    ∘ᵉ-congᵉˡ γ equivδ = ∘ᵉ-congᵉ equivδ (reflexiveᵉ γ)

    ∘ᵉ-congᵉʳ : (δ : Ext Ψ _) → _∘ᵉ_ δ Preserves _≈ᵉ_ {Δ} {Γ} ⟶ _≈ᵉ_
    ∘ᵉ-congᵉʳ δ equivγ = ∘ᵉ-congᵉ (reflexiveᵉ δ) equivγ

    qᵉ-congᵉ : qᵉ_ {Δ} {Γ} {A} Preserves _≈ᵉ_ ⟶ _≈ᵉ_
    qᵉ-congᵉ equiv = ,ᵉ-congᵉ (∘ᵉ-congᵉʳ Wk1ᵉ equiv)

    ∘ᵉ-distrib-,ᵉ : δ ∘ᵉ γ ,ᵉ x ≈ᵉ (δ ∘ᵉ γ) ,ᵉ δ x
    ∘ᵉ-distrib-,ᵉ (here refl) = refl
    ∘ᵉ-distrib-,ᵉ (there _)   = refl

    qᵉ-distrib-∘ᵉ : qᵉ_ {A = A} (δ ∘ᵉ γ) ≈ᵉ qᵉ δ ∘ᵉ qᵉ γ
    qᵉ-distrib-∘ᵉ {δ = δ} = symᵉ (∘ᵉ-distrib-,ᵉ {δ = qᵉ δ})

    qᵉ-Idᵉ-id : qᵉ Idᵉ ≈ᵉ Idᵉ {A ∷ Γ}
    qᵉ-Idᵉ-id (here refl) = refl
    qᵉ-Idᵉ-id (there _)   = refl

    ----------------------------------------------------------
    -- Extensional Applications of Extensions
    ext[-]-extensional : δ ≈ᵉ δ′ →
                         ∀ (M : Tm Δ B) →
                         ext[ δ ] M ≡ ext[ δ′ ] M
    ext[-]-extensional equiv (`# x)   = cong `#_ (equiv x)
    ext[-]-extensional equiv (`λ M)   = cong `λ_ (ext[-]-extensional (qᵉ-congᵉ equiv) M)
    ext[-]-extensional equiv (M `$ N) = cong₂ _`$_ (ext[-]-extensional equiv M) (ext[-]-extensional equiv N)

    ext[Idᵉ]-id : ∀ (M : Tm Γ A) →
                  ext[ Idᵉ ] M ≡ M
    ext[Idᵉ]-id (`# x)   = refl
    ext[Idᵉ]-id (`λ M)   = cong `λ_ (trans (ext[-]-extensional qᵉ-Idᵉ-id M) (ext[Idᵉ]-id M))
    ext[Idᵉ]-id (M `$ N) = cong₂ _`$_ (ext[Idᵉ]-id M) (ext[Idᵉ]-id N)

    ----------------------------------------------------------
    -- Compositional Applications of Extensions
    ext[-]-ext[-]≡ext[-∘ᵉ-] : ∀ (M : Tm Ψ A) →
                              ext[ δ ] ext[ γ ] M ≡ ext[ δ ∘ᵉ γ ] M
    ext[-]-ext[-]≡ext[-∘ᵉ-] (`# x)   = refl
    ext[-]-ext[-]≡ext[-∘ᵉ-] (`λ M)   = cong `λ_ (trans (ext[-]-ext[-]≡ext[-∘ᵉ-] M) (ext[-]-extensional (symᵉ qᵉ-distrib-∘ᵉ) M))
    ext[-]-ext[-]≡ext[-∘ᵉ-] (M `$ N) = cong₂ _`$_ (ext[-]-ext[-]≡ext[-∘ᵉ-] M) (ext[-]-ext[-]≡ext[-∘ᵉ-] N)

    ----------------------------------------------------------
    -- Equivalence of Substitutions
    ----------------------------------------------------------
    reflexiveˢ : ∀ (σ : Sub Δ Γ) → σ ≈ˢ σ
    reflexiveˢ σ x = refl

    symˢ : Symmetric (_≈ˢ_ {Δ} {Γ})
    symˢ = sym ∘_

    transˢ : Transitive (_≈ˢ_ {Δ} {Γ})
    transˢ equiv equiv′ x = trans (equiv x) (equiv′ x)

    ≈ˢ-IsEquivalence : ∀ Δ Γ → IsEquivalence (_≈ˢ_ {Δ} {Γ})
    ≈ˢ-IsEquivalence Δ Γ = record { refl = λ x → refl ; sym = symˢ ; trans = transˢ }

    Sub-Setoid : Ctx → Ctx → Setoid lzero lzero
    Sub-Setoid Δ Γ = record
      { Carrier = Sub Δ Γ
      ; _≈_ = _≈ˢ_
      ; isEquivalence = ≈ˢ-IsEquivalence Δ Γ
      }

    module Sub-Reasoning Δ Γ = SetoidReasoning (Sub-Setoid Δ Γ)

    ----------------------------------------------------------
    -- Useful Properties for Equivalence of Substitutions
    ----------------------------------------------------------

    ,ˢ-congˢ : ∀ {M : Tm _ A} →
               flip _,ˢ_ M Preserves _≈ˢ_ {Δ} {Γ} ⟶ _≈ˢ_
    ,ˢ-congˢ equiv (here _)  = refl
    ,ˢ-congˢ equiv (there y) = equiv y

    ᵉ∘ˢ-congˢ : _ᵉ∘ˢ_ Preserves₂ _≈ᵉ_ {Ψ} ⟶ _≈ˢ_ {Δ} {Γ} ⟶ _≈ˢ_
    ᵉ∘ˢ-congˢ equivδ equivσ x
      rewrite equivσ x = ext[-]-extensional equivδ _

    ᵉ∘ˢ-congˢˡ : (σ : Sub Δ Γ) → flip _ᵉ∘ˢ_ σ Preserves _≈ᵉ_ {Ψ} ⟶ _≈ˢ_
    ᵉ∘ˢ-congˢˡ σ equivδ = ᵉ∘ˢ-congˢ equivδ (reflexiveˢ σ)

    ᵉ∘ˢ-congˢʳ : (δ : Ext Ψ _) → _ᵉ∘ˢ_ δ Preserves _≈ˢ_ {Δ} {Γ} ⟶ _≈ˢ_
    ᵉ∘ˢ-congˢʳ δ equivσ = ᵉ∘ˢ-congˢ (reflexiveᵉ δ) equivσ

    qˢ-congˢ : qˢ_ {Δ} {Γ} {A} Preserves _≈ˢ_ ⟶ _≈ˢ_
    qˢ-congˢ equiv = ,ˢ-congˢ (ᵉ∘ˢ-congˢʳ Wk1ᵉ equiv)

    ᵉ∘ˢ-assoc : ∀ (τ : Sub Δ Γ) →
                δ ᵉ∘ˢ (γ ᵉ∘ˢ τ) ≈ˢ (δ ∘ᵉ γ) ᵉ∘ˢ τ
    ᵉ∘ˢ-assoc = ext[-]-ext[-]≡ext[-∘ᵉ-] ∘_

    forgetˢ-distrib-,ᵉ : ∀ (δ : Ext Γ Δ) (x : A ∈ Γ) →
                         forgetˢ (δ ,ᵉ x) ≈ˢ forgetˢ δ ,ˢ `# x
    forgetˢ-distrib-,ᵉ _ _ (here refl) = refl
    forgetˢ-distrib-,ᵉ _ _ (there _)   = refl

    qˢ-forgetˢ≈ˢforgetˢ-qᵉ : ∀ (δ : Ext Γ Δ) →
                             qˢ_ {A = A} (forgetˢ δ) ≈ˢ forgetˢ (qᵉ δ)
    qˢ-forgetˢ≈ˢforgetˢ-qᵉ δ = symˢ (forgetˢ-distrib-,ᵉ (Wk1ᵉ ∘ᵉ δ) (here refl))

    ----------------------------------------------------------
    -- Extensional Applications of Substitutions
    [|-|]-extensional : σ ≈ˢ σ′ →
                        ∀ (M : Tm Δ A) →
                        [| σ |] M ≡ [| σ′ |] M
    [|-|]-extensional equiv (`# x)   = equiv x
    [|-|]-extensional equiv (`λ M)   = cong `λ_ ([|-|]-extensional (qˢ-congˢ equiv) M)
    [|-|]-extensional equiv (M `$ N) = cong₂ _`$_ ([|-|]-extensional equiv M) ([|-|]-extensional equiv N)

    [|forgetˢ-|]≡ext[-] : ∀ (δ : Ext Γ Δ) (M : Tm Δ A) →
                          [| forgetˢ δ |] M ≡ ext[ δ ] M
    [|forgetˢ-|]≡ext[-] δ (`# x)   = refl
    [|forgetˢ-|]≡ext[-] δ (`λ M)   = cong `λ_ (trans ([|-|]-extensional (qˢ-forgetˢ≈ˢforgetˢ-qᵉ δ) M) ([|forgetˢ-|]≡ext[-] (qᵉ δ) M))
    [|forgetˢ-|]≡ext[-] δ (M `$ N) = cong₂ _`$_ ([|forgetˢ-|]≡ext[-] δ M) ([|forgetˢ-|]≡ext[-] δ N)

    [|Idˢ|]-id : ∀ (M : Tm Γ A) →
                 [| Idˢ |] M ≡ M
    [|Idˢ|]-id M = trans ([|forgetˢ-|]≡ext[-] Idᵉ M) (ext[Idᵉ]-id M)

    ∘ˢ-congˢ : _∘ˢ_ Preserves₂ _≈ˢ_ {Ψ} ⟶ _≈ˢ_ {Δ} {Γ} ⟶ _≈ˢ_
    ∘ˢ-congˢ {v = τ′} equivσ equivτ x
      rewrite equivτ x = [|-|]-extensional equivσ (τ′ x)

    ∘ˢ-congˢˡ : (τ : Sub Δ Γ) → flip _∘ˢ_ τ Preserves _≈ˢ_ {Ψ} ⟶ _≈ˢ_
    ∘ˢ-congˢˡ τ equivσ = ∘ˢ-congˢ equivσ (reflexiveˢ τ)

    ∘ˢ-congˢʳ : (σ : Sub Ψ _) → _∘ˢ_ σ Preserves _≈ˢ_ {Δ} {Γ} ⟶ _≈ˢ_
    ∘ˢ-congˢʳ σ equivτ = ∘ˢ-congˢ (reflexiveˢ σ) equivτ

    ˢ∘ᵉ-∘ᵉ-assoc : ∀ (γ : Ext Δ Γ) →
                   σ ˢ∘ᵉ (δ ∘ᵉ γ) ≈ˢ (σ ˢ∘ᵉ δ) ˢ∘ᵉ γ
    ˢ∘ᵉ-∘ᵉ-assoc _ _ = refl

    ˢ∘ᵉ-distrib-,ᵉ : σ ˢ∘ᵉ δ ,ᵉ x ≈ˢ (σ ˢ∘ᵉ δ) ,ˢ σ x
    ˢ∘ᵉ-distrib-,ᵉ (here refl) = refl
    ˢ∘ᵉ-distrib-,ᵉ (there _)   = refl

    qˢ-distrib-ˢ∘ᵉ : qˢ_ {A = A} (σ ˢ∘ᵉ δ) ≈ˢ qˢ σ ˢ∘ᵉ qᵉ δ
    qˢ-distrib-ˢ∘ᵉ {σ = σ} = symˢ (ˢ∘ᵉ-distrib-,ᵉ {σ = qˢ σ})

    ----------------------------------------------------------
    -- Compositional Applications of a Substitution and Extension
    [|-|]-ext[-]≡[|-ˢ∘ᵉ-|] : ∀ (M : Tm Ψ B) →
                             [| σ |] ext[ δ ] M ≡ [| σ ˢ∘ᵉ δ |] M
    [|-|]-ext[-]≡[|-ˢ∘ᵉ-|] (`# x)   = refl
    [|-|]-ext[-]≡[|-ˢ∘ᵉ-|] (`λ M)   = cong `λ_ (trans ([|-|]-ext[-]≡[|-ˢ∘ᵉ-|] M) ([|-|]-extensional (symˢ qˢ-distrib-ˢ∘ᵉ) M))
    [|-|]-ext[-]≡[|-ˢ∘ᵉ-|] (M `$ N) = cong₂ _`$_ ([|-|]-ext[-]≡[|-ˢ∘ᵉ-|] M) ([|-|]-ext[-]≡[|-ˢ∘ᵉ-|] N)

    ∘ˢ-ᵉ∘ˢ-assoc : ∀ (τ : Sub Δ Γ) →
                   σ ∘ˢ (δ ᵉ∘ˢ τ) ≈ˢ (σ ˢ∘ᵉ δ) ∘ˢ τ
    ∘ˢ-ᵉ∘ˢ-assoc = [|-|]-ext[-]≡[|-ˢ∘ᵉ-|] ∘_

    ᵉ∘ˢ-distrib-,ˢ : δ ᵉ∘ˢ σ ,ˢ M ≈ˢ (δ ᵉ∘ˢ σ) ,ˢ ext[ δ ] M
    ᵉ∘ˢ-distrib-,ˢ (here refl) = refl
    ᵉ∘ˢ-distrib-,ˢ (there _)   = refl

    qˢ-distrib-ᵉ∘ˢ : qˢ_ {A = A} (δ ᵉ∘ˢ σ) ≈ˢ qᵉ δ ᵉ∘ˢ qˢ σ
    qˢ-distrib-ᵉ∘ˢ {δ = δ} {σ = σ} =
      begin qˢ (δ ᵉ∘ˢ σ)                     ≈⟨ ,ˢ-congˢ (ᵉ∘ˢ-assoc σ) ⟩
            ((qᵉ δ ∘ᵉ Wk1ᵉ) ᵉ∘ˢ σ) ,ˢ `#zero ≈˘⟨ ,ˢ-congˢ (ᵉ∘ˢ-assoc σ) ⟩
            (qᵉ δ ᵉ∘ˢ Wk1ᵉ ᵉ∘ˢ σ) ,ˢ `#zero  ≈˘⟨ ᵉ∘ˢ-distrib-,ˢ ⟩
            qᵉ δ ᵉ∘ˢ qˢ σ                    ∎
      where
        open Sub-Reasoning _ _

    ----------------------------------------------------------
    -- Compositional Applications of an Extension and Substitution
    ext[-]-[|-|]≡[|-ᵉ∘ˢ-|] : ∀ (M : Tm Ψ B) →
                             ext[ δ ] [| σ |] M ≡ [| δ ᵉ∘ˢ σ |] M
    ext[-]-[|-|]≡[|-ᵉ∘ˢ-|] (`# x)   = refl
    ext[-]-[|-|]≡[|-ᵉ∘ˢ-|] (`λ M)   = cong `λ_ (trans (ext[-]-[|-|]≡[|-ᵉ∘ˢ-|] M) ([|-|]-extensional (symˢ qˢ-distrib-ᵉ∘ˢ) M))
    ext[-]-[|-|]≡[|-ᵉ∘ˢ-|] (M `$ N) = cong₂ _`$_ (ext[-]-[|-|]≡[|-ᵉ∘ˢ-|] M) (ext[-]-[|-|]≡[|-ᵉ∘ˢ-|] N)

    ᵉ∘ˢ-∘ˢ-assoc : ∀ (τ : Sub Δ Γ) →
                   δ ᵉ∘ˢ (σ ∘ˢ τ) ≈ˢ (δ ᵉ∘ˢ σ) ∘ˢ τ
    ᵉ∘ˢ-∘ˢ-assoc = ext[-]-[|-|]≡[|-ᵉ∘ˢ-|] ∘_

    ∘ˢ-distrib-,ˢ : σ ∘ˢ τ ,ˢ M ≈ˢ (σ ∘ˢ τ) ,ˢ [| σ |] M
    ∘ˢ-distrib-,ˢ (here refl) = refl
    ∘ˢ-distrib-,ˢ (there _)   = refl

    qˢ-distrib-∘ˢ : qˢ_ {A = A} (σ ∘ˢ τ) ≈ˢ qˢ σ ∘ˢ qˢ τ
    qˢ-distrib-∘ˢ {σ = σ} {τ = τ} =
      begin qˢ (σ ∘ˢ τ)                      ≈⟨ ,ˢ-congˢ (ᵉ∘ˢ-∘ˢ-assoc τ) ⟩
            ((qˢ σ ˢ∘ᵉ Wk1ᵉ) ∘ˢ τ) ,ˢ `#zero ≈˘⟨ ,ˢ-congˢ (∘ˢ-ᵉ∘ˢ-assoc τ) ⟩
            (qˢ σ ∘ˢ Wk1ᵉ ᵉ∘ˢ τ) ,ˢ `#zero   ≈˘⟨ ∘ˢ-distrib-,ˢ ⟩
            qˢ σ ∘ˢ qˢ τ                     ∎
      where
        open Sub-Reasoning _ _

    ----------------------------------------------------------
    -- Compositional Applications of Substitutions
    [|-|]-[|-|]≡[|-∘ˢ-|] : ∀ (M : Tm Ψ B) →
                           [| σ |] [| σ′ |] M ≡ [| σ ∘ˢ σ′ |] M
    [|-|]-[|-|]≡[|-∘ˢ-|] (`# x)   = refl
    [|-|]-[|-|]≡[|-∘ˢ-|] (`λ M)   = cong `λ_ (trans ([|-|]-[|-|]≡[|-∘ˢ-|] M) ([|-|]-extensional (symˢ qˢ-distrib-∘ˢ) M))
    [|-|]-[|-|]≡[|-∘ˢ-|] (M `$ N) = cong₂ _`$_ ([|-|]-[|-|]≡[|-∘ˢ-|] M) ([|-|]-[|-|]≡[|-∘ˢ-|] N)

    !ˢ-ˢ∘ᵉ-qᵉ : ∀ (δ : Ext Γ Δ) (M : Tm Δ A) →
                !ˢ ext[ δ ] M ˢ∘ᵉ qᵉ δ ≈ˢ δ ᵉ∘ˢ !ˢ M
    !ˢ-ˢ∘ᵉ-qᵉ δ M =
      begin !ˢ ext[ δ ] M ˢ∘ᵉ qᵉ δ                        ≈⟨ ˢ∘ᵉ-distrib-,ᵉ {σ = !ˢ ext[ δ ] M} ⟩
            (!ˢ ext[ δ ] M ˢ∘ᵉ (Wk1ᵉ ∘ᵉ δ)) ,ˢ ext[ δ ] M ≈˘⟨ ᵉ∘ˢ-distrib-,ˢ ⟩
            δ ᵉ∘ˢ !ˢ M                                    ∎
      where
        open Sub-Reasoning _ _

    !ˢ-∘ˢ-qˢ′ : ∀ (σ : Sub Γ Δ) (M : Tm Γ A) →
                !ˢ M ∘ˢ qˢ σ ≈ˢ σ ,ˢ M
    !ˢ-∘ˢ-qˢ′ σ M =
      begin !ˢ M ∘ˢ qˢ σ                ≈⟨ ∘ˢ-distrib-,ˢ {σ = !ˢ M} ⟩
            (!ˢ M ∘ˢ (Wk1ᵉ ᵉ∘ˢ σ)) ,ˢ M ≈⟨ ,ˢ-congˢ (∘ˢ-ᵉ∘ˢ-assoc σ) ⟩
            (Idˢ ∘ˢ σ) ,ˢ M             ≈⟨ ,ˢ-congˢ (λ x → [|Idˢ|]-id (σ x)) ⟩
            σ ,ˢ M                      ∎
      where
        open Sub-Reasoning _ _

    !ˢ-∘ˢ-qˢ : ∀ (σ : Sub Γ Δ) (M : Tm Δ A) →
               !ˢ [| σ |] M ∘ˢ qˢ σ ≈ˢ σ ∘ˢ !ˢ M
    !ˢ-∘ˢ-qˢ σ M =
      begin !ˢ [| σ |] M ∘ˢ qˢ σ ≈⟨ !ˢ-∘ˢ-qˢ′ σ ([| σ |] M) ⟩
            σ ,ˢ [| σ |] M       ≈˘⟨ ∘ˢ-distrib-,ˢ ⟩
            σ ∘ˢ !ˢ M            ∎
      where
        open Sub-Reasoning _ _

open Syntax hiding (module Properties)
open Syntax.Properties

module OpSem where
  ----------------------------------------------------------
  -- Ordinary (Single-step) Reduction
  ----------------------------------------------------------

  infix 4 _⟶_
  data _⟶_ : Rel (Tm Γ A) lzero where
    `λ_       : M ⟶ M′ →
                -------------
                `λ M ⟶ `λ M′

    _`$?      : (M⟶M′ : M ⟶ M′) →
                ------------------
                M `$ N ⟶ M′ `$ N

    ?`$_      : (N⟶N′ : N ⟶ N′) →
                ------------------
                M `$ N ⟶ M `$ N′

    `→β       : ---------------------------
                (`λ M) `$ N ⟶ [| !ˢ N |] M

  ----------------------------------------------------------
  -- Ordinary Multi-step Reduction
  ----------------------------------------------------------

  infix   4 _⟶*_
  _⟶*_ : Rel (Tm Γ A) _
  _⟶*_ = Star _⟶_

  module ⟶*-Reasoning {Γ A} = Star.StarReasoning (_⟶_ {Γ} {A})

  ----------------------------------------------------------
  -- Flipped Reductions
  ----------------------------------------------------------

  infix 4 _⟵_
  _⟵_ : Rel (Tm Γ A) _
  _⟵_ = flip _⟶_

  infix 4 _+⟵_
  _+⟵_ : Rel (Tm Γ A) _
  _+⟵_ = TransClosure _⟵_

  module Properties where
    infixr 30 ext[_]⟶_
    ext[_]⟶_ : (δ : Ext Γ Δ) → M ⟶ M′ → ext[ δ ] M ⟶ ext[ δ ] M′
    ext[ δ ]⟶ (`λ M⟶)           = `λ (ext[ qᵉ δ ]⟶ M⟶)
    ext[ δ ]⟶ (M⟶ `$?)          = (ext[ δ ]⟶ M⟶) `$?
    ext[ δ ]⟶ (?`$ M⟶)          = ?`$ (ext[ δ ]⟶ M⟶)
    ext[ δ ]⟶ (`→β {M = M} {N})
      rewrite ext[-]-[|-|]≡[|-ᵉ∘ˢ-|] {δ = δ} {σ = !ˢ N} M
            | sym ([|-|]-extensional (!ˢ-ˢ∘ᵉ-qᵉ δ N) M)
            | sym ([|-|]-ext[-]≡[|-ˢ∘ᵉ-|] {σ = !ˢ ext[ δ ] N} {δ = qᵉ δ} M) = `→β

    infixr 30 ext[_]⟶*_
    ext[_]⟶*_ : (δ : Ext Γ Δ) → M ⟶* M′ → ext[ δ ] M ⟶* ext[ δ ] M′
    ext[_]⟶*_ δ = Star.gmap ext[ δ ]_ ext[ δ ]⟶_

    infixr 30 [|_|]⟶_
    [|_|]⟶_ : (σ : Sub Γ Δ) → M ⟶ M′ → [| σ |] M ⟶ [| σ |] M′
    [| σ |]⟶ (`λ M⟶)           = `λ ([| qˢ σ |]⟶ M⟶)
    [| σ |]⟶ (M⟶ `$?)          = ([| σ |]⟶ M⟶) `$?
    [| σ |]⟶ (?`$ M⟶)          = ?`$ ([| σ |]⟶ M⟶)
    [| σ |]⟶ (`→β {M = M} {N})
      rewrite [|-|]-[|-|]≡[|-∘ˢ-|] {σ = σ} {σ′ = !ˢ N} M
            | sym ([|-|]-extensional (!ˢ-∘ˢ-qˢ σ N) M)
            | sym ([|-|]-[|-|]≡[|-∘ˢ-|] {σ = !ˢ [| σ |] N} {σ′ = qˢ σ} M) = `→β

    infixr 30 [|_|]⟶*_
    [|_|]⟶*_ : (σ : Sub Γ Δ) → M ⟶* M′ → [| σ |] M ⟶* [| σ |] M′
    [|_|]⟶*_ σ = Star.gmap [| σ |]_ [| σ |]⟶_

    ------------------------------------------------------------
    -- Helpers for multi-step parallel reduction
    ------------------------------------------------------------

    ξ-of-⟶* : ∀ {R : Rel (Tm Γ A) ℓ″} (f : Tm Γ A → Tm Δ B) → R =[ f ]⇒ _⟶_ → Star R =[ f ]⇒ _⟶*_
    ξ-of-⟶* = Star.gmap

    ξ-of-⟶*′ : ∀ (f : Tm Γ A → Tm Δ B) → _⟶_ =[ f ]⇒ _⟶_ → _⟶*_ =[ f ]⇒ _⟶*_
    ξ-of-⟶*′ = ξ-of-⟶*

    [!ˢ⟶_]_ : L ⟶ L′ → (x : A ∈ _) → (!ˢ L) x ⟶* (!ˢ L′) x
    [!ˢ⟶ L⟶ ] here refl = L⟶ ◅ ε
    [!ˢ⟶ L⟶ ] there x   = ε

    [qˢ[_]!ˢ⟶_]_ : ∀ Ψ → L ⟶ L′ → (x : A ∈ _) → (qˢ[ Ψ ] !ˢ L) x ⟶* (qˢ[ Ψ ] !ˢ L′) x
    [qˢ[ []    ]!ˢ⟶ L⟶ ] x         = [!ˢ⟶ L⟶ ] x
    [qˢ[ _ ∷ Ψ ]!ˢ⟶ L⟶ ] here refl = ε
    [qˢ[ _ ∷ Ψ ]!ˢ⟶ L⟶ ] there x   = ext[ Wk1ᵉ ]⟶* ([qˢ[ Ψ ]!ˢ⟶ L⟶ ] x) 

    [|qˢ[_]!ˢ⟶_|]_ : ∀ Ψ → L ⟶ L′ → (M : Tm _ A) → [| qˢ[ Ψ ] !ˢ L |] M ⟶* [| qˢ[ Ψ ] !ˢ L′ |] M
    [|qˢ[ Ψ ]!ˢ⟶ L⟶ |] `# x     = [qˢ[ Ψ ]!ˢ⟶ L⟶ ] x
    [|qˢ[ Ψ ]!ˢ⟶ L⟶ |] (`λ M)   = ξ-of-⟶*′ _ `λ_ ([|qˢ[ _ ∷ Ψ ]!ˢ⟶ L⟶ |] M)
    [|qˢ[ Ψ ]!ˢ⟶ L⟶ |] (M `$ N) = ξ-of-⟶*′ _ _`$? ([|qˢ[ Ψ ]!ˢ⟶ L⟶ |] M) ◅◅ ξ-of-⟶*′ _ ?`$_ ([|qˢ[ Ψ ]!ˢ⟶ L⟶ |] N)

    [|!ˢ⟶_|]_ : L ⟶ L′ → (M : Tm _ A) → [| !ˢ L |] M ⟶* [| !ˢ L′ |] M
    [|!ˢ⟶_|]_ = [|qˢ[ [] ]!ˢ⟶_|]_

    ⟶*-cases : M ⟶* M′ → M ≡ M′ ⊎ M′ +⟵ M
    ⟶*-cases =
      flip (Star.foldl (_≡_ ∪ flip _+⟵_)) (inj₁ refl) λ where
        (inj₁ refl) M⟶ → inj₂ [ M⟶ ]
        (inj₂ M″⟶+) M⟶ → inj₂ (M⟶ ∷ M″⟶+)

open OpSem hiding (module Properties)
open OpSem.Properties

module AccessibilitySN where
  infix 4 _∈sn
  _∈sn : Pred (Tm Γ A) _
  _∈sn = Acc _⟵_

  infix 4 _∈sn+
  _∈sn+ : Pred (Tm Γ A) _
  _∈sn+ = Acc _+⟵_

  infix 4 _∈ne
  data _∈ne : Pred (Tm Γ A) lzero where
    `#_  : (x : A ∈ Γ) →
           --------------
           `# x ∈ne

    _`$- : M ∈ne →
           -----------
           M `$ N ∈ne

  infix 4 _⟶sn_
  data _⟶sn_ : Rel (Tm Γ A) lzero where
    _`$- : M ⟶sn M′ →
           -------------------
           M `$ N ⟶sn M′ `$ N

    `→β  : N ∈sn →
           -----------------------------
           (`λ M) `$ N ⟶sn [| !ˢ N |] M

  module Properties where
    ⟶*∧∈sn⇒∈sn : M ⟶* M′ → M ∈sn → M′ ∈sn
    ⟶*∧∈sn⇒∈sn = flip (Star.fold (Morphism on _∈sn)) id λ M⟶ f Msn → f (acc-inverse Msn M⟶)

    `#∈sn : (x : A ∈ Γ) → `# x ∈sn
    `#∈sn x∈ = acc λ ()

    `λ∈sn : M ∈sn → `λ M ∈sn
    `λ∈sn (acc Mrec) =
      acc λ where
        (`λ x) → `λ∈sn (Mrec x)

    [|_|]∈sn : ∀ (σ : Sub Δ Γ) → [| σ |] M ∈sn → M ∈sn
    [| σ |]∈sn (acc [|σ|]Mrec) = acc λ M⟶ → [| σ |]∈sn ([|σ|]Mrec ([| σ |]⟶ M⟶))

    `$∈sn-invˡ : M `$ N ∈sn → M ∈sn
    `$∈sn-invˡ (acc MNrec) = acc λ M⟶ → `$∈sn-invˡ (MNrec (M⟶ `$?))

    `$∈sn-invʳ : M `$ N ∈sn → N ∈sn
    `$∈sn-invʳ (acc MNrec) = acc λ N⟶ → `$∈sn-invʳ (MNrec (?`$ N⟶))

    ∈sn-weak-head-expansion : N ∈sn → [| !ˢ N |] M ∈sn → (`λ M) `$ N ∈sn
    ∈sn-weak-head-expansion = flip helper
      where
        go : [| !ˢ N |] M ≡ L → L ∈sn+ → N ∈sn → (`λ M) `$ N ∈sn
        go {N = N} {M = M} eq Lsn@(acc Lrec) Nsn@(acc Nrec) =
          acc λ where
            ((`λ M⟶) `$?)   → go refl (Lrec (subst (_ +⟵_) eq [ [| !ˢ _ |]⟶ M⟶ ])) Nsn
            (       ?`$ N⟶) →
              case ⟶*-cases ([|!ˢ⟶ N⟶ |] M) of λ where
                (inj₁ eq′) → go (trans (sym eq′) eq) Lsn (Nrec N⟶)
                (inj₂ M⟶+) → go refl (Lrec (subst (_ +⟵_) eq M⟶+)) (Nrec N⟶)
            `→β             → subst _∈sn (sym eq) (TransClosure.accessible⁻ _⟵_ Lsn)

        helper : [| !ˢ N |] M ∈sn → N ∈sn → (`λ M) `$ N ∈sn
        helper [|N|]Msn = go refl (TransClosure.accessible _⟵_ [|N|]Msn)

    ∈ne-closed-wrt-⟶ : M ∈ne → M ⟶ M′ → M′ ∈ne
    ∈ne-closed-wrt-⟶ (Mne `$-) (M⟶ `$?)   = ∈ne-closed-wrt-⟶ Mne M⟶ `$-
    ∈ne-closed-wrt-⟶ (Mne `$-) (  ?`$ M⟶) = Mne `$-

    `$∈sn : M ∈ne → M ∈sn → N ∈sn → M `$ N ∈sn
    `$∈sn Mne Msn@(acc Mrec) Nsn@(acc Nrec) = acc λ where
      (M⟶ `$?) → `$∈sn (∈ne-closed-wrt-⟶ Mne M⟶) (Mrec M⟶) Nsn
      (?`$ N⟶) → `$∈sn Mne Msn (Nrec N⟶)

    ⟶sn-⟶-confluence : M ⟶sn M₀ →
                       M ⟶ M₁ →
                       M₀ ≡ M₁ ⊎ ∃[ M′ ] M₀ ⟶* M′ × M₁ ⟶sn M′
    ⟶sn-⟶-confluence                   (M⟶sn `$-) (M⟶ `$?)        = ⊎.map
                                                                      (λ{ refl → refl })
                                                                      (λ{ (_ , M₀⟶* , M₁⟶sn) → -, ξ-of-⟶*′ _ _`$? M₀⟶* , M₁⟶sn `$- })
                                                                      (⟶sn-⟶-confluence M⟶sn M⟶)
    ⟶sn-⟶-confluence                   (M⟶sn `$-) (?`$ N⟶)        = inj₂ (_ , ?`$ N⟶ ◅ ε , M⟶sn `$-)
    ⟶sn-⟶-confluence                   (`→β Nsn)  ((`λ M⟶) `$?)   = inj₂ (_ , [| !ˢ _ |]⟶ M⟶ ◅ ε , `→β Nsn)
    ⟶sn-⟶-confluence {M = (`λ M) `$ _} (`→β Nsn)  (       ?`$ N⟶) = inj₂ (_ , [|!ˢ⟶ N⟶ |] M , `→β (acc-inverse Nsn N⟶))
    ⟶sn-⟶-confluence                   (`→β Nsn)  `→β             = inj₁ refl

    `$∈sn-closed⁻¹ : M ∈sn → N ∈sn → M ⟶sn M′ → M′ `$ N ∈sn → M `$ N ∈sn
    `$∈sn-closed⁻¹ {M = M} {N = N} Msn@(acc Mrec) Nsn@(acc Nrec) M⟶sn M′Nsn =
      acc λ where
        (M⟶ `$?)   → ⊎.[ (λ{ refl → M′Nsn })
                       , (λ{ (_ , M₀⟶* , M₁⟶sn) →
                             `$∈sn-closed⁻¹ (Mrec M⟶) Nsn M₁⟶sn (⟶*∧∈sn⇒∈sn (ξ-of-⟶*′ _ _`$? M₀⟶*) M′Nsn)
                           })
                       ]′
                       (⟶sn-⟶-confluence M⟶sn M⟶)
        (  ?`$ N⟶) → `$∈sn-closed⁻¹ Msn (Nrec N⟶) M⟶sn (acc-inverse M′Nsn (?`$ N⟶))

    ∈sn-closed⁻¹ : M ⟶sn M′ → M′ ∈sn → M ∈sn
    ∈sn-closed⁻¹ (M⟶sn `$-) M′sn = `$∈sn-closed⁻¹ (∈sn-closed⁻¹ M⟶sn (`$∈sn-invˡ M′sn)) (`$∈sn-invʳ M′sn) M⟶sn M′sn
    ∈sn-closed⁻¹ (`→β Nsn)  M′sn = ∈sn-weak-head-expansion Nsn M′sn

open AccessibilitySN hiding (module Properties) public
open AccessibilitySN.Properties public

module InductiveSN where
  infix 4 _∈SNe
  infix 4 _∈SN
  infix 4 _⟶SN_
  data _∈SNe : Pred (Tm Γ A) lzero
  data _∈SN  : Pred (Tm Γ A) lzero
  data _⟶SN_ : Rel (Tm Γ A) lzero

  data _∈SNe where
    `#_  : (x : A ∈ Γ) →
           --------------
           `# x ∈SNe

    _`$_ : M ∈SNe →
           N ∈SN →
           ------------
           M `$ N ∈SNe

  data _∈SN where
    `λ_   : M ∈SN →
            ---------
            `λ M ∈SN

    `Ne   : M ∈SNe →
            ---------
            M ∈SN

    `bclo : M ⟶SN M′ →
            M′ ∈SN →
            -----------
            M ∈SN

  data _⟶SN_ where
    _`$- : M ⟶SN M′ →
           -------------------
           M `$ N ⟶SN M′ `$ N

    `→β  : N ∈SN →
           -----------------------------
           (`λ M) `$ N ⟶SN [| !ˢ N |] M

  module Properties where
    infixr 30 ext[_]∈SN_
    infixr 30 ext[_]∈SNe_
    infixr 30 ext[_]⟶SN_
    ext[_]∈SN_  : (δ : Ext Δ Γ) → M ∈SN → ext[ δ ] M ∈SN
    ext[_]∈SNe_ : (δ : Ext Δ Γ) → M ∈SNe → ext[ δ ] M ∈SNe
    ext[_]⟶SN_  : (δ : Ext Δ Γ) → M ⟶SN M′ → ext[ δ ] M ⟶SN ext[ δ ] M′

    ext[ δ ]∈SN (`λ MSN)        = `λ (ext[ qᵉ δ ]∈SN MSN)
    ext[ δ ]∈SN `Ne MSNe        = `Ne (ext[ δ ]∈SNe MSNe)
    ext[ δ ]∈SN `bclo M⟶SN M′SN = `bclo (ext[ δ ]⟶SN M⟶SN) (ext[ δ ]∈SN M′SN)

    ext[ δ ]∈SNe (`# x)        = `# δ x
    ext[ δ ]∈SNe (MSNe `$ NSN) = (ext[ δ ]∈SNe MSNe) `$ (ext[ δ ]∈SN NSN)

    ext[ δ ]⟶SN (M⟶SN `$-)              = (ext[ δ ]⟶SN M⟶SN) `$-
    ext[ δ ]⟶SN `→β {N = N} {M = M} NSN
      rewrite ext[-]-[|-|]≡[|-ᵉ∘ˢ-|] {δ = δ} {σ = !ˢ N} M
            | sym ([|-|]-extensional (!ˢ-ˢ∘ᵉ-qᵉ δ N) M)
            | sym ([|-|]-ext[-]≡[|-ˢ∘ᵉ-|] {σ = !ˢ ext[ δ ] N} {δ = qᵉ δ} M) = `→β (ext[ δ ]∈SN NSN)

    infixr 30 ext[_]⁻¹∈SN_of_by_
    infixr 30 ext[_]⁻¹∈SNe_of_by_
    infixr 30 ext[_]⁻¹⟶SN_of_by_
    ext[_]⁻¹∈SN_of_by_  : (δ : Ext Δ Γ) → M₀ ∈SN → ∀ M → M₀ ≡ ext[ δ ] M → M ∈SN
    ext[_]⁻¹∈SNe_of_by_ : (δ : Ext Δ Γ) → M₀ ∈SNe → ∀ M → M₀ ≡ ext[ δ ] M → M ∈SNe
    ext[_]⁻¹⟶SN_of_by_  : (δ : Ext Δ Γ) → M₀ ⟶SN M′₀ → ∀ M → M₀ ≡ ext[ δ ] M → ∃[ M′ ] M ⟶SN M′ × ext[ δ ] M′ ≡ M′₀

    ext[ δ ]⁻¹∈SN `λ M₀SN           of `λ M by refl = `λ (ext[ qᵉ δ ]⁻¹∈SN M₀SN of M by refl)
    ext[ δ ]⁻¹∈SN `Ne M₀SNe         of M    by eq   = `Ne (ext[ δ ]⁻¹∈SNe M₀SNe of M by eq)
    ext[ δ ]⁻¹∈SN `bclo M₀⟶SN M′₀SN of M    by eq
      with _ , M⟶SN , refl ← ext[ δ ]⁻¹⟶SN M₀⟶SN of M by eq = `bclo M⟶SN (ext[ δ ]⁻¹∈SN M′₀SN of _ by refl)

    ext[ δ ]⁻¹∈SNe `# y          of `# x   by eq = `# x
    ext[ δ ]⁻¹∈SNe M₀SNe `$ N₀SN of M `$ N by refl = (ext[ δ ]⁻¹∈SNe M₀SNe of M by refl) `$ (ext[ δ ]⁻¹∈SN N₀SN of N by refl)

    ext[ δ ]⁻¹⟶SN M₀⟶SN `$- of M `$ N      by refl
      with _ , M⟶SN , refl ← ext[ δ ]⁻¹⟶SN M₀⟶SN of M by refl = _ , M⟶SN `$- , refl
    ext[ δ ]⁻¹⟶SN `→β N₀SN  of (`λ M) `$ N by refl = _ , `→β (ext[ δ ]⁻¹∈SN N₀SN of N by refl)
                                                   , (begin _ ≡⟨ ext[-]-[|-|]≡[|-ᵉ∘ˢ-|] {δ = δ} {σ = !ˢ N} M ⟩
                                                            _ ≡˘⟨ [|-|]-extensional (!ˢ-ˢ∘ᵉ-qᵉ δ N) M ⟩
                                                            _ ≡˘⟨ [|-|]-ext[-]≡[|-ˢ∘ᵉ-|] {σ = !ˢ ext[ δ ] N} {δ = qᵉ δ} M ⟩
                                                            _ ∎)
      where
        open ≡-Reasoning

    infixr 30 ext[_]⁻¹∈SN_
    ext[_]⁻¹∈SN_ : (δ : Ext Δ Γ) → ext[ δ ] M ∈SN → M ∈SN
    ext[ δ ]⁻¹∈SN [δ]MSN = ext[ δ ]⁻¹∈SN [δ]MSN of _ by refl

    infixr 30 ext[_]⁻¹∈SNe_
    ext[_]⁻¹∈SNe_ : (δ : Ext Δ Γ) → ext[ δ ] M ∈SNe → M ∈SNe
    ext[ δ ]⁻¹∈SNe [δ]MSNe = ext[ δ ]⁻¹∈SNe [δ]MSNe of _ by refl

    infixr 30 ext[_]⁻¹⟶SN_
    ext[_]⁻¹⟶SN_ : (δ : Ext Δ Γ) → ext[ δ ] M ⟶SN M′ → ∃[ M″ ] M ⟶SN M″ × ext[ δ ] M″ ≡ M′
    ext[ δ ]⁻¹⟶SN [δ]M⟶SN = ext[ δ ]⁻¹⟶SN [δ]M⟶SN of _ by refl

    ∈SN-extensionality : M `$ (`# x) ∈SN → M ∈SN
    ∈SN-extensionality (`Ne (MSNe `$ xSN))                                = `Ne MSNe
    ∈SN-extensionality (`bclo                   (Mx⟶SN `$-)        M′xSN) = `bclo Mx⟶SN (∈SN-extensionality M′xSN)
    ∈SN-extensionality (`bclo {M = (`λ M) `$ _} (`→β (`Ne (`# x))) M′xSN)
      rewrite sym ([|-|]-extensional (forgetˢ-distrib-,ᵉ Idᵉ x) M)
            | [|forgetˢ-|]≡ext[-] (Idᵉ ,ᵉ x) M                            = `λ (ext[ Idᵉ ,ᵉ x ]⁻¹∈SN M′xSN)

open InductiveSN hiding (module Properties) public
open InductiveSN.Properties public

module Soundness where
  SNe-ne-sound : M ∈SNe → M ∈ne
  SNe-ne-sound (`# x)      = `# x
  SNe-ne-sound (MSNe `$ _) = SNe-ne-sound MSNe `$-

  SN-sound  : M ∈SN → M ∈sn
  SNe-sound : M ∈SNe → M ∈sn
  ⟶SN-sound : M ⟶SN M′ → M ⟶sn M′

  SN-sound (`λ MSN)          = `λ∈sn (SN-sound MSN)
  SN-sound (`Ne MSNe)        = SNe-sound MSNe
  SN-sound (`bclo M⟶SN M′SN) = ∈sn-closed⁻¹ (⟶SN-sound M⟶SN) (SN-sound M′SN)

  SNe-sound (`# x)        = `#∈sn x
  SNe-sound (MSNe `$ NSN) = `$∈sn (SNe-ne-sound MSNe) (SNe-sound MSNe) (SN-sound NSN)

  ⟶SN-sound (M⟶SN `$-) = ⟶SN-sound M⟶SN `$-
  ⟶SN-sound (`→β NSN)  = `→β (SN-sound NSN)

open Soundness public

module LogicalRelation where
  LogicalRelation : Pred (Tm Γ A) lzero

  infix 4 LogicalRelationSyntax
  LogicalRelationSyntax = LogicalRelation
  syntax LogicalRelationSyntax {A = A} M = M ∈ℜ[ A ]

  LogicalRelation {A = base}     = _∈SN
  LogicalRelation {A = _ `→ _} M = ∀ {Δ} (δ : Ext Δ _) {N} → N ∈ℜ[ _ ] → ext[ δ ] M `$ N ∈ℜ[ _ ]

  SubstLogicalRelation : Pred (Sub Γ Δ) lzero

  infix 4 SubstLogicalRelationSyntax
  SubstLogicalRelationSyntax = SubstLogicalRelation
  syntax SubstLogicalRelationSyntax {Δ = Δ} σ = σ ∈ℜs[ Δ ]

  SubstLogicalRelation {Δ = []}    σ = ⊤
  SubstLogicalRelation {Δ = _ ∷ _} σ = σ ∘ there ∈ℜs[ _ ] × σ (here refl) ∈ℜ[ _ ]

  module Properties where
    reify   : M ∈ℜ[ A ] → M ∈SN
    bclosed : M ⟶SN M′ → M′ ∈ℜ[ A ] → M ∈ℜ[ A ]
    reflect : M ∈SNe → M ∈ℜ[ A ]

    reify {A = base}   Mℜ = Mℜ
    reify {A = _ `→ _} Mℜ = ext[ Wk1ᵉ ]⁻¹∈SN ∈SN-extensionality (reify (Mℜ Wk1ᵉ (reflect (`# here refl))))

    bclosed {A = base}   M⟶SN M′ℜ      = `bclo M⟶SN M′ℜ
    bclosed {A = _ `→ _} M⟶SN M′ℜ δ Nℜ = bclosed ((ext[ δ ]⟶SN M⟶SN) `$-) (M′ℜ δ Nℜ)

    reflect {A = base}   MSNe      = `Ne MSNe
    reflect {A = _ `→ _} MSNe δ Nℜ = reflect ((ext[ δ ]∈SNe MSNe) `$ (reify Nℜ))

    forgetˢ∈ℜs : ∀ Δ (δ : Ext Γ Δ) → forgetˢ δ ∈ℜs[ Δ ]
    forgetˢ∈ℜs []      δ = tt
    forgetˢ∈ℜs (_ ∷ Δ) δ = forgetˢ∈ℜs Δ (δ ∘ there) , reflect (`# δ (here refl))

    Idˢ∈ℜs : ∀ Γ → Idˢ ∈ℜs[ Γ ]
    Idˢ∈ℜs Γ = forgetˢ∈ℜs Γ Idᵉ

    infixr 30 ext[_]∈ℜ_
    ext[_]∈ℜ_ : ∀ (δ : Ext Γ Δ) → M ∈ℜ[ A ] → ext[ δ ] M ∈ℜ[ A ]
    ext[_]∈ℜ_ {A = base}           δ Mℜ      = ext[ δ ]∈SN Mℜ
    ext[_]∈ℜ_ {A = _ `→ _} {M = M} δ Mℜ ρ Nℜ
      rewrite ext[-]-ext[-]≡ext[-∘ᵉ-] {δ = ρ} {γ = δ} M = Mℜ (ρ ∘ᵉ δ) Nℜ

    infixr 30 ext[_]∈ℜs_
    ext[_]∈ℜs_ : ∀ (δ : Ext Γ Δ) → σ ∈ℜs[ Ψ ] → δ ᵉ∘ˢ σ ∈ℜs[ Ψ ]
    ext[_]∈ℜs_ {Ψ = []}    δ σℜ = tt
    ext[_]∈ℜs_ {Ψ = _ ∷ _} δ σℜ = ext[ δ ]∈ℜs σℜ .proj₁ , ext[ δ ]∈ℜ (σℜ .proj₂)

    fundamental-lemma-∈ : ∀ x → σ ∈ℜs[ Δ ] → σ x ∈ℜ[ A ]
    fundamental-lemma-∈ (here refl) σℜ = σℜ .proj₂
    fundamental-lemma-∈ (there x)   σℜ = fundamental-lemma-∈ x (σℜ .proj₁)

    fundamental-lemma : ∀ M → σ ∈ℜs[ Δ ] → [| σ |] M ∈ℜ[ A ]
    fundamental-lemma         (`# x)   σℜ          = fundamental-lemma-∈ x σℜ
    fundamental-lemma {σ = σ} (`λ M)   σℜ δ {N} Nℜ
      with Mℜ ← fundamental-lemma {σ = (δ ᵉ∘ˢ σ) ,ˢ _} M ((ext[ δ ]∈ℜs σℜ) , Nℜ)
        rewrite sym ([|-|]-extensional (!ˢ-∘ˢ-qˢ′ (δ ᵉ∘ˢ σ) N) M)
              | sym ([|-|]-[|-|]≡[|-∘ˢ-|] {σ = !ˢ N} {σ′ = qˢ (δ ᵉ∘ˢ σ)} M)
              | [|-|]-extensional (qˢ-distrib-ᵉ∘ˢ {δ = δ} {σ = σ}) M
              | sym (ext[-]-[|-|]≡[|-ᵉ∘ˢ-|] {δ = qᵉ δ} {σ = qˢ σ} M) = bclosed (`→β (reify Nℜ)) Mℜ
    fundamental-lemma {σ = σ} (M `$ N) σℜ
      rewrite sym (ext[Idᵉ]-id ([| σ |] M))        = fundamental-lemma M σℜ Idᵉ (fundamental-lemma N σℜ)

open LogicalRelation hiding (module Properties) public
open LogicalRelation.Properties public

strong-normalization : ∀ (M : Tm Γ A) →
                       M ∈sn
strong-normalization M
  rewrite sym ([|Idˢ|]-id M) = SN-sound (reify (fundamental-lemma M (Idˢ∈ℜs _)))

strong-normalization′ : ∀ {Γ A} →
                        WellFounded (_⟵_ {Γ} {A})
strong-normalization′ = strong-normalization
