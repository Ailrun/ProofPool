{-# OPTIONS --safe #-}

module Reducibility.EtaCC where

open import Agda.Primitive using (lzero)
open import Data.Empty as ⊥
open import Data.List as List
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
open import Relation.Binary using (IsEquivalence; Rel; Setoid)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_)
import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
open import Relation.Binary.PropositionalEquality hiding (J)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning

module Syntax where
  data Tp : Set where
    base : Tp
    _`→_ : Tp → Tp → Tp
    _`∧_ : Tp → Tp → Tp

  Ctx : Set
  Ctx = List Tp

  variable
    A A′ A′₀ A′₁ A′₂ A′₃ A″ A″₀ A″₁ A″₂ A″₃ A‴ A‴₀ A‴₁ A‴₂ A‴₃ A₀ A₁ A₂ A₃ : Tp
    B B′ B′₀ B′₁ B′₂ B′₃ B″ B″₀ B″₁ B″₂ B″₃ B‴ B‴₀ B‴₁ B‴₂ B‴₃ B₀ B₁ B₂ B₃ : Tp
    C C′ C′₀ C′₁ C′₂ C′₃ C″ C″₀ C″₁ C″₂ C″₃ C‴ C‴₀ C‴₁ C‴₂ C‴₃ C₀ C₁ C₂ C₃ : Tp
    D D′ D′₀ D′₁ D′₂ D′₃ D″ D″₀ D″₁ D″₂ D″₃ D‴ D‴₀ D‴₁ D‴₂ D‴₃ D₀ D₁ D₂ D₃ : Tp
    E E′ E′₀ E′₁ E′₂ E′₃ E″ E″₀ E″₁ E″₂ E″₃ E‴ E‴₀ E‴₁ E‴₂ E‴₃ E₀ E₁ E₂ E₃ : Tp
    F F′ F′₀ F′₁ F′₂ F′₃ F″ F″₀ F″₁ F″₂ F″₃ F‴ F‴₀ F‴₁ F‴₂ F‴₃ F₀ F₁ F₂ F₃ : Tp
    Γ Γ′ Γ′₀ Γ′₁ Γ′₂ Γ′₃ Γ″ Γ″₀ Γ″₁ Γ″₂ Γ″₃ Γ‴ Γ‴₀ Γ‴₁ Γ‴₂ Γ‴₃ Γ₀ Γ₁ Γ₂ Γ₃ : Ctx
    Δ Δ′ Δ′₀ Δ′₁ Δ′₂ Δ′₃ Δ″ Δ″₀ Δ″₁ Δ″₂ Δ″₃ Δ‴ Δ‴₀ Δ‴₁ Δ‴₂ Δ‴₃ Δ₀ Δ₁ Δ₂ Δ₃ : Ctx
    Ψ Ψ′ Ψ′₀ Ψ′₁ Ψ′₂ Ψ′₃ Ψ″ Ψ″₀ Ψ″₁ Ψ″₂ Ψ″₃ Ψ‴ Ψ‴₀ Ψ‴₁ Ψ‴₂ Ψ‴₃ Ψ₀ Ψ₁ Ψ₂ Ψ₃ : Ctx

  data Tm : Ctx → Tp → Set where
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

    _`,_      : (M₁ : Tm Γ A₁) →
                (M₂ : Tm Γ A₂) →
                -----------------
                Tm Γ (A₁ `∧ A₂)

    `let_`in_ : (M : Tm Γ (A₁ `∧ A₂)) →
                (N : Tm (A₁ ∷ A₂ ∷ Γ) B) →
                ---------------------------
                Tm Γ B

  pattern `#0 = `# (here refl)
  pattern `#1 = `# (there (here refl))
  pattern `#2 = `# (there (there (here refl)))
  pattern `#3 = `# (there (there (there (here refl))))

  Ext : Rel Ctx lzero
  Ext Γ Δ = ∀ {A} → A ∈ Δ → A ∈ Γ

  Sub : Rel Ctx lzero
  Sub Γ Δ = ∀ {A} → A ∈ Δ → Tm Γ A

  variable
    x x′ x′₀ x′₁ x′₂ x′₃ x″ x″₀ x″₁ x″₂ x″₃ x‴ x‴₀ x‴₁ x‴₂ x‴₃ x₀ x₁ x₂ x₃ : A ∈ Γ
    y y′ y′₀ y′₁ y′₂ y′₃ y″ y″₀ y″₁ y″₂ y″₃ y‴ y‴₀ y‴₁ y‴₂ y‴₃ y₀ y₁ y₂ y₃ : A ∈ Γ
    z z′ z′₀ z′₁ z′₂ z′₃ z″ z″₀ z″₁ z″₂ z″₃ z‴ z‴₀ z‴₁ z‴₂ z‴₃ z₀ z₁ z₂ z₃ : A ∈ Γ
    M M′ M′₀ M′₁ M′₂ M′₃ M″ M″₀ M″₁ M″₂ M″₃ M‴ M‴₀ M‴₁ M‴₂ M‴₃ M₀ M₁ M₂ M₃ : Tm Γ A
    N N′ N′₀ N′₁ N′₂ N′₃ N″ N″₀ N″₁ N″₂ N″₃ N‴ N‴₀ N‴₁ N‴₂ N‴₃ N₀ N₁ N₂ N₃ : Tm Γ A
    L L′ L′₀ L′₁ L′₂ L′₃ L″ L″₀ L″₁ L″₂ L″₃ L‴ L‴₀ L‴₁ L‴₂ L‴₃ L₀ L₁ L₂ L₃ : Tm Γ A
    σ σ′ σ′₀ σ′₁ σ′₂ σ′₃ σ″ σ″₀ σ″₁ σ″₂ σ″₃ σ‴ σ‴₀ σ‴₁ σ‴₂ σ‴₃ σ₀ σ₁ σ₂ σ₃ : Sub Γ Δ
    τ τ′ τ′₀ τ′₁ τ′₂ τ′₃ τ″ τ″₀ τ″₁ τ″₂ τ″₃ τ‴ τ‴₀ τ‴₁ τ‴₂ τ‴₃ τ₀ τ₁ τ₂ τ₃ : Sub Γ Δ
    γ γ′ γ′₀ γ′₁ γ′₂ γ′₃ γ″ γ″₀ γ″₁ γ″₂ γ″₃ γ‴ γ‴₀ γ‴₁ γ‴₂ γ‴₃ γ₀ γ₁ γ₂ γ₃ : Ext Γ Δ
    δ δ′ δ′₀ δ′₁ δ′₂ δ′₃ δ″ δ″₀ δ″₁ δ″₂ δ″₃ δ‴ δ‴₀ δ‴₁ δ‴₂ δ‴₃ δ₀ δ₁ δ₂ δ₃ : Ext Γ Δ
    ρ ρ′ ρ′₀ ρ′₁ ρ′₂ ρ′₃ ρ″ ρ″₀ ρ″₁ ρ″₂ ρ″₃ ρ‴ ρ‴₀ ρ‴₁ ρ‴₂ ρ‴₃ ρ₀ ρ₁ ρ₂ ρ₃ : Ext Γ Δ

open Syntax

module NormalForm where
  mutual
    data Nf : Tm Γ A → Set where
      `λ_       : Nf M →
                  ----------
                  Nf (`λ M)

      _`,_      : (VM₁ : Nf M₁) →
                  (VM₂ : Nf M₂) →
                  ----------------
                  Nf (M₁ `, M₂)

      `let_`in_ : (RM : Ne M) →
                  (VN : Nf N) →
                  ------------------
                  Nf (`let M `in N)

      `↑_       : (RM : Ne M) →
                  --------------
                  Nf M

    data Ne : Tm Γ A → Set where
      `#_  : (x : A ∈ Γ) →
             --------------
             Ne (`# x)

      _`$_ : (RM : Ne M) →
             (VN : Nf N) →
             --------------
             Ne (M `$ N)

open NormalForm

module OpSem where
  ----------------------------------------------------------
  -- Useful constructions for extension
  ----------------------------------------------------------

  Wkᵉ : ∀ Δ → Ext (Δ ++ Γ) Γ
  Wkᵉ []      = id
  Wkᵉ (_ ∷ Δ) = there ∘ Wkᵉ Δ

  Wk1ᵉ : Ext (A ∷ Γ) Γ
  Wk1ᵉ = Wkᵉ (_ ∷ [])

  Idᵉ : Ext Γ Γ
  Idᵉ = Wkᵉ []

  infixl 6 _,ᵉ_
  _,ᵉ_ : Ext Δ Γ → A ∈ Δ → Ext Δ (A ∷ Γ)
  (δ ,ᵉ x) (here eq) = subst (λ A → A ∈ _) (sym eq) x
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
  -- Application of extension
  infixr 30 ext[_]_
  ext[_]_ : Ext Γ Δ → Tm Δ A → Tm Γ A
  ext[ δ ] (`# x)         = `# δ x
  ext[ δ ] (`λ M)         = `λ ext[ qᵉ δ ] M
  ext[ δ ] (M `$ N)       = ext[ δ ] M `$ ext[ δ ] N
  ext[ δ ] (M₁ `, M₂)     = ext[ δ ] M₁ `, ext[ δ ] M₂
  ext[ δ ] (`let M `in N) = `let ext[ δ ] M `in ext[ qᵉ qᵉ δ ] N

  infixr 30 ext_
  ext_ : Tm Γ A → Tm (B ∷ Γ) A
  ext_ = ext[ Wk1ᵉ ]_

  ----------------------------------------------------------
  -- Useful constructions for substitution
  ----------------------------------------------------------

  forgetˢ : Ext Δ Γ → Sub Δ Γ
  forgetˢ δ = `#_ ∘ δ

  Idˢ : Sub Γ Γ
  Idˢ = forgetˢ Idᵉ

  infixl 6 _,ˢ_
  _,ˢ_ : Sub Δ Γ → Tm Δ A → Sub Δ (A ∷ Γ)
  (σ ,ˢ M) (here eq) = subst (λ A → Tm _ A) (sym eq) M
  (σ ,ˢ M) (there x) = σ x

  infixr 5 _ˢ∘ᵉ_
  _ˢ∘ᵉ_ : Sub Ψ Δ → Ext Δ Γ → Sub Ψ Γ
  σ ˢ∘ᵉ δ = σ ∘ δ

  infixr 5 _ᵉ∘ˢ_
  _ᵉ∘ˢ_ : Ext Ψ Δ → Sub Δ Γ → Sub Ψ Γ
  δ ᵉ∘ˢ σ = ext[ δ ]_ ∘ σ

  infixr 7 qˢ_
  qˢ_ : Sub Δ Γ → Sub (A ∷ Δ) (A ∷ Γ)
  qˢ σ = (Wk1ᵉ ᵉ∘ˢ σ) ,ˢ `#0

  infixr 7 qˢ[_]_
  qˢ[_]_ : ∀ Ψ → Sub Δ Γ → Sub (Ψ ++ Δ) (Ψ ++ Γ)
  qˢ[ []    ] σ = σ
  qˢ[ _ ∷ Ψ ] σ = qˢ qˢ[ Ψ ] σ

  infixr 7 !ˢ_
  !ˢ_ : Tm Γ A → Sub Γ (A ∷ Γ)
  !ˢ M = Idˢ ,ˢ M

  ----------------------------------------------------------
  -- Substitution Application
  infixr 30 [|_|]_
  [|_|]_ : Sub Γ Δ → Tm Δ A → Tm Γ A
  [| σ |] (`# x)         = σ x
  [| σ |] (`λ M)         = `λ [| qˢ σ |] M
  [| σ |] (M `$ N)       = [| σ |] M `$ [| σ |] N
  [| σ |] (M₁ `, M₂)     = [| σ |] M₁ `, [| σ |] M₂
  [| σ |] (`let M `in N) = `let [| σ |] M `in [| qˢ qˢ σ |] N

  infixr 5 _∘ˢ_
  _∘ˢ_ : Sub Ψ Δ → Sub Δ Γ → Sub Ψ Γ
  σ ∘ˢ σ′ = [| σ |]_ ∘ σ′

  ----------------------------------------------------------
  -- Parallel Reduction
  ----------------------------------------------------------

  infix 4 _↠_
  data _↠_ : Tm Γ A → Tm Γ A → Set where
    `#_       : (x : A ∈ Γ) →
                --------------
                `# x ↠ `# x

    `λ_       : M ↠ M′ →
                -------------
                `λ M ↠ `λ M′

    _`$_      : (M↠M′ : M ↠ M′) →
                (N↠N′ : N ↠ N′) →
                ------------------
                M `$ N ↠ M′ `$ N′

    `→β       : (M↠M′ : M ↠ M′) →
                (N↠N′ : N ↠ N′) →
                -----------------------------
                (`λ M) `$ N ↠ [| !ˢ N′ |] M′

    `→η       : M ↠ M′ →
                -----------------------
                M ↠ `λ (ext M′ `$ `#0)

    _`,_      : (M₁↠M′₁ : M₁ ↠ M′₁) →
                (M₂↠M′₂ : M₂ ↠ M′₂) →
                ----------------------
                M₁ `, M₂ ↠ M′₁ `, M′₂

    `let_`in_ : (M↠M′ : M ↠ M′) →
                (N↠N′ : N ↠ N′) →
                ------------------------------
                `let M `in N ↠ `let M′ `in N′

    `∧β       : (M₁↠M′₁ : M₁ ↠ M′₁) →
                (M₂↠M′₂ : M₂ ↠ M′₂) →
                (N↠N′ : N ↠ N′) →
                -----------------------------------------------
                `let (M₁ `, M₂) `in N ↠ [| !ˢ M′₂ ,ˢ M′₁ |] N′

    `∧η       : (M↠M′ : M ↠ M′) →
                -----------------------------
                M ↠ `let M′ `in (`#0 `, `#1)

    `→c       : ------------------------------------------------------------------
                (`let M `in N) `$ L ↠ `let M `in (N `$ ext[ Wkᵉ (_ ∷ _ ∷ []) ] L)

    `∧c       : ----------------------------------------------------------------------------------
                `let (`let M `in N) `in L ↠ `let M `in `let N `in ext[ qᵉ qᵉ Wkᵉ (_ ∷ _ ∷ []) ] L

  infix   4 _↠*_
  _↠*_ : Rel (Tm Γ A) _
  _↠*_ = Star _↠_

  infix 4 _halts
  _halts : Tm Γ A → Set
  M halts = ∃[ M′ ] M ↠* M′ × Nf M′

open OpSem

module OpSemProp where
  ----------------------------------------------------------
  -- Equivalence of Extension
  ----------------------------------------------------------

  infix 4 _≈ᵉ_
  _≈ᵉ_ : Ext Δ Γ → Ext Δ Γ → Set
  δ ≈ᵉ δ′ = ∀ {A} (x : A ∈ _) → δ x ≡ δ′ x

  reflᵉ : δ ≈ᵉ δ
  reflᵉ = λ x → refl

  reflexiveᵉ : ∀ (δ : Ext Δ Γ) →
               δ ≈ᵉ δ
  reflexiveᵉ δ = reflᵉ {δ = δ}

  symᵉ : δ ≈ᵉ δ′ → δ′ ≈ᵉ δ
  symᵉ = sym ∘_

  transᵉ : δ ≈ᵉ δ′ → δ′ ≈ᵉ δ″ → δ ≈ᵉ δ″
  transᵉ equiv equiv′ = λ x → trans (equiv x) (equiv′ x)

  ≈ᵉ-IsEquivalence : ∀ Δ Γ → IsEquivalence (_≈ᵉ_ {Δ = Δ} {Γ = Γ})
  ≈ᵉ-IsEquivalence Δ Γ = record { refl = λ x → refl ; sym = symᵉ ; trans = transᵉ }

  Ext-Setoid : Ctx → Ctx → Setoid lzero lzero
  Ext-Setoid Δ Γ = record
    { Carrier = Ext Δ Γ
    ; _≈_ = _≈ᵉ_
    ; isEquivalence = ≈ᵉ-IsEquivalence Δ Γ
    }

  module Ext-Reasoning Δ Γ = SetoidReasoning (Ext-Setoid Δ Γ)

  ----------------------------------------------------------
  -- Useful Properties for Equivalence of Extension
  ----------------------------------------------------------

  ,ᵉ-congᵉ : δ ≈ᵉ δ′ →
             δ ,ᵉ x ≈ᵉ δ′ ,ᵉ x
  ,ᵉ-congᵉ equiv (here eq) = refl
  ,ᵉ-congᵉ equiv (there y) = equiv y

  ∘ᵉ-congᵉ : δ ≈ᵉ δ′ →
             γ ≈ᵉ γ′ →
             δ ∘ᵉ γ ≈ᵉ δ′ ∘ᵉ γ′
  ∘ᵉ-congᵉ equivδ equivγ x
    rewrite equivγ x = equivδ _

  qᵉ-congᵉ : δ ≈ᵉ δ′ →
             qᵉ_ {A = A} δ ≈ᵉ qᵉ δ′
  qᵉ-congᵉ equiv = ,ᵉ-congᵉ (∘ᵉ-congᵉ (reflexiveᵉ Wk1ᵉ) equiv)

  qᵉ[-]-Idᵉ-id : ∀ Ψ (x : A ∈ Ψ ++ Γ) →
                 (qᵉ[ Ψ ] Idᵉ) x ≡ x
  qᵉ[-]-Idᵉ-id []      x           = refl
  qᵉ[-]-Idᵉ-id (_ ∷ Ψ) (here refl) = refl
  qᵉ[-]-Idᵉ-id (_ ∷ Ψ) (there x)   = cong there (qᵉ[-]-Idᵉ-id Ψ x)

  ext[qᵉ[-]-Idᵉ]-id : ∀ Ψ (M : Tm (Ψ ++ Γ) A) →
                      ext[ qᵉ[ Ψ ] Idᵉ ] M ≡ M
  ext[qᵉ[-]-Idᵉ]-id Ψ (`# x) = cong `#_ (qᵉ[-]-Idᵉ-id Ψ x)
  ext[qᵉ[-]-Idᵉ]-id Ψ (`λ M) = cong `λ_ (ext[qᵉ[-]-Idᵉ]-id (_ ∷ Ψ) M)
  ext[qᵉ[-]-Idᵉ]-id Ψ (M `$ N) = cong₂ _`$_ (ext[qᵉ[-]-Idᵉ]-id Ψ M) (ext[qᵉ[-]-Idᵉ]-id Ψ N)
  ext[qᵉ[-]-Idᵉ]-id Ψ (M₁ `, M₂) = cong₂ _`,_ (ext[qᵉ[-]-Idᵉ]-id Ψ M₁) (ext[qᵉ[-]-Idᵉ]-id Ψ M₂)
  ext[qᵉ[-]-Idᵉ]-id Ψ (`let M `in N) = cong₂ `let_`in_ (ext[qᵉ[-]-Idᵉ]-id Ψ M) (ext[qᵉ[-]-Idᵉ]-id (_ ∷ _ ∷ Ψ) N)

  ext[Idᵉ]-id : ∀ (M : Tm Γ A) →
                ext[ Idᵉ ] M ≡ M
  ext[Idᵉ]-id = ext[qᵉ[-]-Idᵉ]-id []

  ----------------------------------------------------------
  -- Application of Extension is Extensional
  ext[-]-extensional : δ ≈ᵉ δ′ →
                       ∀ (M : Tm Δ B) →
                       ext[ δ ] M ≡ ext[ δ′ ] M
  ext[-]-extensional equiv (`# x)         = cong `#_ (equiv x)
  ext[-]-extensional equiv (`λ M)         = cong `λ_ (ext[-]-extensional (qᵉ-congᵉ equiv) M)
  ext[-]-extensional equiv (M `$ N)       = cong₂ _`$_ (ext[-]-extensional equiv M) (ext[-]-extensional equiv N)
  ext[-]-extensional equiv (M₁ `, M₂)     = cong₂ _`,_ (ext[-]-extensional equiv M₁) (ext[-]-extensional equiv M₂)
  ext[-]-extensional equiv (`let M `in N) = cong₂ `let_`in_ (ext[-]-extensional equiv M) (ext[-]-extensional (qᵉ-congᵉ (qᵉ-congᵉ equiv)) N)

  ----------------------------------------------------------
  -- Application of Extension preserves normal/neutral forms
  mutual
    ext[-]-preserves-Nf : ∀ (δ : Ext Γ Δ) →
                          Nf M →
                          Nf (ext[ δ ] M)
    ext[-]-preserves-Nf δ (`λ VM) = `λ ext[-]-preserves-Nf (qᵉ δ) VM
    ext[-]-preserves-Nf δ (VM₁ `, VM₂) = ext[-]-preserves-Nf δ VM₁ `, ext[-]-preserves-Nf δ VM₂
    ext[-]-preserves-Nf δ (`let RM `in VN) = `let ext[-]-preserves-Ne δ RM `in ext[-]-preserves-Nf (qᵉ qᵉ δ) VN
    ext[-]-preserves-Nf δ (`↑ RM) = `↑ ext[-]-preserves-Ne δ RM

    ext[-]-preserves-Ne : ∀ (δ : Ext Γ Δ) →
                           Ne M →
                           Ne (ext[ δ ] M)
    ext[-]-preserves-Ne δ (`# x) = `# δ x
    ext[-]-preserves-Ne δ (RM `$ VN) = ext[-]-preserves-Ne δ RM `$ ext[-]-preserves-Nf δ VN

  ∘ᵉ-distrib-,ᵉ : δ ∘ᵉ γ ,ᵉ x ≈ᵉ (δ ∘ᵉ γ) ,ᵉ δ x
  ∘ᵉ-distrib-,ᵉ (here eq)
    rewrite eq            = refl
  ∘ᵉ-distrib-,ᵉ (there x) = refl

  qᵉ-distrib-∘ᵉ : qᵉ_ {A = A} (δ ∘ᵉ γ) ≈ᵉ qᵉ δ ∘ᵉ qᵉ γ
  qᵉ-distrib-∘ᵉ {δ = δ} = symᵉ (∘ᵉ-distrib-,ᵉ {δ = qᵉ δ})

  ext[-]-ext[-]≡ext[-∘ᵉ-] : ∀ (M : Tm Ψ A) →
                            ext[ δ ] ext[ γ ] M ≡ ext[ δ ∘ᵉ γ ] M
  ext[-]-ext[-]≡ext[-∘ᵉ-] (`# x) = refl
  ext[-]-ext[-]≡ext[-∘ᵉ-] (`λ M) = cong `λ_ (trans (ext[-]-ext[-]≡ext[-∘ᵉ-] M) (ext[-]-extensional (symᵉ qᵉ-distrib-∘ᵉ) M))
  ext[-]-ext[-]≡ext[-∘ᵉ-] (M `$ N) = cong₂ _`$_ (ext[-]-ext[-]≡ext[-∘ᵉ-] M) (ext[-]-ext[-]≡ext[-∘ᵉ-] N)
  ext[-]-ext[-]≡ext[-∘ᵉ-] (M₁ `, M₂) = cong₂ _`,_ (ext[-]-ext[-]≡ext[-∘ᵉ-] M₁) (ext[-]-ext[-]≡ext[-∘ᵉ-] M₂)
  ext[-]-ext[-]≡ext[-∘ᵉ-] (`let M `in N) = cong₂ `let_`in_ (ext[-]-ext[-]≡ext[-∘ᵉ-] M) (trans (ext[-]-ext[-]≡ext[-∘ᵉ-] N) (ext[-]-extensional (symᵉ (transᵉ (qᵉ-congᵉ qᵉ-distrib-∘ᵉ) qᵉ-distrib-∘ᵉ)) N))

  ----------------------------------------------------------
  -- Equivalence of Substitution
  ----------------------------------------------------------

  infix 4 _≈ˢ_
  _≈ˢ_ : Sub Δ Γ → Sub Δ Γ → Set
  σ ≈ˢ σ′ = ∀ {A} (x : A ∈ _) → σ x ≡ σ′ x

  reflˢ : σ ≈ˢ σ
  reflˢ = λ x → refl

  symˢ : σ ≈ˢ σ′ → σ′ ≈ˢ σ
  symˢ = sym ∘_

  transˢ : σ ≈ˢ σ′ → σ′ ≈ˢ σ″ → σ ≈ˢ σ″
  transˢ equiv equiv′ = λ x → trans (equiv x) (equiv′ x)

  ≈ˢ-IsEquivalence : ∀ Δ Γ → IsEquivalence (_≈ˢ_ {Δ = Δ} {Γ = Γ})
  ≈ˢ-IsEquivalence Δ Γ = record { refl = λ x → refl ; sym = symˢ ; trans = transˢ }

  Sub-Setoid : Ctx → Ctx → Setoid lzero lzero
  Sub-Setoid Δ Γ = record
    { Carrier = Sub Δ Γ
    ; _≈_ = _≈ˢ_
    ; isEquivalence = ≈ˢ-IsEquivalence Δ Γ
    }

  module Sub-Reasoning Δ Γ = SetoidReasoning (Sub-Setoid Δ Γ)

  ----------------------------------------------------------
  -- Useful Properties for Equivalence of Substitution
  ----------------------------------------------------------

  ,ˢ-congˢ : ∀ {M : Tm _ A} →
             σ ≈ˢ σ′ →
             σ ,ˢ M ≈ˢ σ′ ,ˢ M
  ,ˢ-congˢ equiv (here eq) = refl
  ,ˢ-congˢ equiv (there y) = equiv y

  ᵉ∘ˢ-congˢ : δ ≈ᵉ δ′ →
              σ ≈ˢ σ′ →
              δ ᵉ∘ˢ σ ≈ˢ δ′ ᵉ∘ˢ σ′
  ᵉ∘ˢ-congˢ equivδ equivσ x
    rewrite equivσ x = ext[-]-extensional equivδ _

  qˢ-congˢ : σ ≈ˢ σ′ →
             qˢ_ {A = A} σ ≈ˢ qˢ σ′
  qˢ-congˢ equiv = ,ˢ-congˢ (ᵉ∘ˢ-congˢ (reflexiveᵉ Wk1ᵉ) equiv)

  Wk1ᵉ-cancels-,ˢ : (σ ,ˢ M) ˢ∘ᵉ Wk1ᵉ ≈ˢ σ
  Wk1ᵉ-cancels-,ˢ x = refl

  ᵉ∘ˢ-assoc : ∀ (τ : Sub Δ Γ) →
              δ ᵉ∘ˢ (γ ᵉ∘ˢ τ) ≈ˢ (δ ∘ᵉ γ) ᵉ∘ˢ τ
  ᵉ∘ˢ-assoc τ = ext[-]-ext[-]≡ext[-∘ᵉ-] ∘ τ

  qˢ[-]-forgetˢ≡qˢ[-] : ∀ Ψ (δ : Ext Γ Δ) (x : A ∈ (Ψ ++ Δ)) →
                        (qˢ[ Ψ ] (forgetˢ δ)) x ≡ `# (qᵉ[ Ψ ] δ) x
  qˢ[-]-forgetˢ≡qˢ[-] []      δ x           = refl
  qˢ[-]-forgetˢ≡qˢ[-] (_ ∷ Ψ) δ (here refl) = refl
  qˢ[-]-forgetˢ≡qˢ[-] (_ ∷ Ψ) δ (there x)
    rewrite qˢ[-]-forgetˢ≡qˢ[-] Ψ δ x       = refl

  [|qˢ[-]-forgetˢ-|]≡ext[qᵉ[-]-] : ∀ Ψ (δ : Ext Γ Δ) (M : Tm (Ψ ++ Δ) A) →
                                   [| qˢ[ Ψ ] (forgetˢ δ) |] M ≡ ext[ qᵉ[ Ψ ] δ ] M
  [|qˢ[-]-forgetˢ-|]≡ext[qᵉ[-]-] Ψ δ (`# x)         = qˢ[-]-forgetˢ≡qˢ[-] Ψ δ x
  [|qˢ[-]-forgetˢ-|]≡ext[qᵉ[-]-] Ψ δ (`λ M)         = cong `λ_ ([|qˢ[-]-forgetˢ-|]≡ext[qᵉ[-]-] (_ ∷ Ψ) δ M)
  [|qˢ[-]-forgetˢ-|]≡ext[qᵉ[-]-] Ψ δ (M `$ N)       = cong₂ _`$_ ([|qˢ[-]-forgetˢ-|]≡ext[qᵉ[-]-] Ψ δ M) ([|qˢ[-]-forgetˢ-|]≡ext[qᵉ[-]-] Ψ δ N)
  [|qˢ[-]-forgetˢ-|]≡ext[qᵉ[-]-] Ψ δ (M₁ `, M₂)     = cong₂ _`,_ ([|qˢ[-]-forgetˢ-|]≡ext[qᵉ[-]-] Ψ δ M₁) ([|qˢ[-]-forgetˢ-|]≡ext[qᵉ[-]-] Ψ δ M₂)
  [|qˢ[-]-forgetˢ-|]≡ext[qᵉ[-]-] Ψ δ (`let M `in N) = cong₂ `let_`in_ ([|qˢ[-]-forgetˢ-|]≡ext[qᵉ[-]-] Ψ δ M) ([|qˢ[-]-forgetˢ-|]≡ext[qᵉ[-]-] (_ ∷ _ ∷ Ψ) δ N)

  [|forgetˢ-|]≡ext[-] : ∀ (δ : Ext Γ Δ) (M : Tm Δ A) →
                        [| forgetˢ δ |] M ≡ ext[ δ ] M
  [|forgetˢ-|]≡ext[-] = [|qˢ[-]-forgetˢ-|]≡ext[qᵉ[-]-] []

  [|Idˢ|]-id : ∀ (M : Tm Γ A) →
               [| Idˢ |] M ≡ M
  [|Idˢ|]-id M = trans ([|forgetˢ-|]≡ext[-] Idᵉ M) (ext[Idᵉ]-id M)

  ----------------------------------------------------------
  -- Application of Substitution is Extensional
  [|-|]-extensional : σ ≈ˢ σ′ →
                      ∀ (M : Tm Δ A) →
                      [| σ |] M ≡ [| σ′ |] M
  [|-|]-extensional equiv (`# x)         = equiv x
  [|-|]-extensional equiv (`λ M)         = cong `λ_ ([|-|]-extensional (qˢ-congˢ equiv) M)
  [|-|]-extensional equiv (M `$ N)       = cong₂ _`$_ ([|-|]-extensional equiv M) ([|-|]-extensional equiv N)
  [|-|]-extensional equiv (M₁ `, M₂)     = cong₂ _`,_ ([|-|]-extensional equiv M₁) ([|-|]-extensional equiv M₂)
  [|-|]-extensional equiv (`let M `in N) = cong₂ `let_`in_ ([|-|]-extensional equiv M) ([|-|]-extensional (qˢ-congˢ (qˢ-congˢ equiv)) N)

  ∘ˢ-congˢ : σ ≈ˢ σ′ →
             τ ≈ˢ τ′ →
             σ ∘ˢ τ ≈ˢ σ′ ∘ˢ τ′
  ∘ˢ-congˢ {τ′ = τ′} equivσ equivτ x
    rewrite equivτ x = [|-|]-extensional equivσ (τ′ x)

  ˢ∘ᵉ-∘ᵉ-assoc : ∀ (γ : Ext Δ Γ) →
                 σ ˢ∘ᵉ (δ ∘ᵉ γ) ≈ˢ (σ ˢ∘ᵉ δ) ˢ∘ᵉ γ
  ˢ∘ᵉ-∘ᵉ-assoc γ x = refl

  ˢ∘ᵉ-distrib-,ᵉ : σ ˢ∘ᵉ δ ,ᵉ x ≈ˢ (σ ˢ∘ᵉ δ) ,ˢ σ x
  ˢ∘ᵉ-distrib-,ᵉ (here eq)
    rewrite eq             = refl
  ˢ∘ᵉ-distrib-,ᵉ (there x) = refl

  qˢ-distrib-ˢ∘ᵉ : qˢ_ {A = A} (σ ˢ∘ᵉ δ) ≈ˢ qˢ σ ˢ∘ᵉ qᵉ δ
  qˢ-distrib-ˢ∘ᵉ {σ = σ} = symˢ (ˢ∘ᵉ-distrib-,ᵉ {σ = qˢ σ})

  [|-|]-ext[-]≡[|-ˢ∘ᵉ-|] : ∀ (M : Tm Ψ B) →
                           [| σ |] ext[ δ ] M ≡ [| σ ˢ∘ᵉ δ |] M
  [|-|]-ext[-]≡[|-ˢ∘ᵉ-|] (`# x) = refl
  [|-|]-ext[-]≡[|-ˢ∘ᵉ-|] (`λ M) = cong `λ_ (trans ([|-|]-ext[-]≡[|-ˢ∘ᵉ-|] M) ([|-|]-extensional (symˢ qˢ-distrib-ˢ∘ᵉ) M))
  [|-|]-ext[-]≡[|-ˢ∘ᵉ-|] (M `$ N) = cong₂ _`$_ ([|-|]-ext[-]≡[|-ˢ∘ᵉ-|] M) ([|-|]-ext[-]≡[|-ˢ∘ᵉ-|] N)
  [|-|]-ext[-]≡[|-ˢ∘ᵉ-|] (M₁ `, M₂) = cong₂ _`,_ ([|-|]-ext[-]≡[|-ˢ∘ᵉ-|] M₁) ([|-|]-ext[-]≡[|-ˢ∘ᵉ-|] M₂)
  [|-|]-ext[-]≡[|-ˢ∘ᵉ-|] (`let M `in N) = cong₂ `let_`in_ ([|-|]-ext[-]≡[|-ˢ∘ᵉ-|] M) (trans ([|-|]-ext[-]≡[|-ˢ∘ᵉ-|] N) ([|-|]-extensional (symˢ (transˢ (qˢ-congˢ qˢ-distrib-ˢ∘ᵉ) qˢ-distrib-ˢ∘ᵉ)) N))

  ∘ˢ-ᵉ∘ˢ-assoc : ∀ (τ : Sub Δ Γ) →
                 σ ∘ˢ (δ ᵉ∘ˢ τ) ≈ˢ (σ ˢ∘ᵉ δ) ∘ˢ τ
  ∘ˢ-ᵉ∘ˢ-assoc τ = [|-|]-ext[-]≡[|-ˢ∘ᵉ-|] ∘ τ

  ᵉ∘ˢ-distrib-,ˢ : δ ᵉ∘ˢ σ ,ˢ M ≈ˢ (δ ᵉ∘ˢ σ) ,ˢ ext[ δ ] M
  ᵉ∘ˢ-distrib-,ˢ (here eq)
    rewrite eq             = refl
  ᵉ∘ˢ-distrib-,ˢ (there x) = refl

  qˢ-distrib-ᵉ∘ˢ : qˢ_ {A = A} (δ ᵉ∘ˢ σ) ≈ˢ qᵉ δ ᵉ∘ˢ qˢ σ
  qˢ-distrib-ᵉ∘ˢ {δ = δ} {σ = σ} =
    begin qˢ (δ ᵉ∘ˢ σ) ≈⟨ ,ˢ-congˢ (ᵉ∘ˢ-assoc σ) ⟩
          ((qᵉ δ ∘ᵉ Wk1ᵉ) ᵉ∘ˢ σ) ,ˢ `#0 ≈˘⟨ ,ˢ-congˢ (ᵉ∘ˢ-assoc σ) ⟩
          (qᵉ δ ᵉ∘ˢ Wk1ᵉ ᵉ∘ˢ σ) ,ˢ `#0 ≈˘⟨ ᵉ∘ˢ-distrib-,ˢ {δ = qᵉ δ} ⟩
          qᵉ δ ᵉ∘ˢ qˢ σ ∎
    where
      open Sub-Reasoning _ _

  ext[-]-[|-|]≡[|-ᵉ∘ˢ-|] : ∀ (M : Tm Ψ B) →
                           ext[ δ ] [| σ |] M ≡ [| δ ᵉ∘ˢ σ |] M
  ext[-]-[|-|]≡[|-ᵉ∘ˢ-|] (`# x) = refl
  ext[-]-[|-|]≡[|-ᵉ∘ˢ-|] (`λ M) = cong `λ_ (trans (ext[-]-[|-|]≡[|-ᵉ∘ˢ-|] M) ([|-|]-extensional (symˢ qˢ-distrib-ᵉ∘ˢ) M))
  ext[-]-[|-|]≡[|-ᵉ∘ˢ-|] (M `$ N) = cong₂ _`$_ (ext[-]-[|-|]≡[|-ᵉ∘ˢ-|] M) (ext[-]-[|-|]≡[|-ᵉ∘ˢ-|] N)
  ext[-]-[|-|]≡[|-ᵉ∘ˢ-|] (M₁ `, M₂) = cong₂ _`,_ (ext[-]-[|-|]≡[|-ᵉ∘ˢ-|] M₁) (ext[-]-[|-|]≡[|-ᵉ∘ˢ-|] M₂)
  ext[-]-[|-|]≡[|-ᵉ∘ˢ-|] (`let M `in N) = cong₂ `let_`in_ (ext[-]-[|-|]≡[|-ᵉ∘ˢ-|] M) (trans (ext[-]-[|-|]≡[|-ᵉ∘ˢ-|] N) ([|-|]-extensional (symˢ (transˢ (qˢ-congˢ qˢ-distrib-ᵉ∘ˢ) qˢ-distrib-ᵉ∘ˢ)) N))

  ᵉ∘ˢ-∘ˢ-assoc : ∀ (τ : Sub Δ Γ) →
                 δ ᵉ∘ˢ (σ ∘ˢ τ) ≈ˢ (δ ᵉ∘ˢ σ) ∘ˢ τ
  ᵉ∘ˢ-∘ˢ-assoc τ x = ext[-]-[|-|]≡[|-ᵉ∘ˢ-|] (τ x)

  ∘ˢ-distrib-,ˢ : σ ∘ˢ τ ,ˢ M ≈ˢ (σ ∘ˢ τ) ,ˢ [| σ |] M
  ∘ˢ-distrib-,ˢ (here eq)
    rewrite eq            = refl
  ∘ˢ-distrib-,ˢ (there x) = refl

  qˢ-distrib-∘ˢ : qˢ_ {A = A} (σ ∘ˢ τ) ≈ˢ qˢ σ ∘ˢ qˢ τ
  qˢ-distrib-∘ˢ {σ = σ} {τ = τ} =
    begin qˢ (σ ∘ˢ τ) ≈⟨ ,ˢ-congˢ (ᵉ∘ˢ-∘ˢ-assoc τ) ⟩
          ((qˢ σ ˢ∘ᵉ Wk1ᵉ) ∘ˢ τ) ,ˢ `#0 ≈˘⟨ ,ˢ-congˢ (∘ˢ-ᵉ∘ˢ-assoc τ) ⟩
          (qˢ σ ∘ˢ Wk1ᵉ ᵉ∘ˢ τ) ,ˢ `#0 ≈˘⟨ ∘ˢ-distrib-,ˢ {σ = qˢ σ} ⟩
          qˢ σ ∘ˢ qˢ τ ∎
    where
      open Sub-Reasoning _ _

  [|-|]-[|-|]≡[|-∘ˢ-|] : ∀ (M : Tm Ψ B) →
                         [| σ |] [| σ′ |] M ≡ [| σ ∘ˢ σ′ |] M
  [|-|]-[|-|]≡[|-∘ˢ-|] (`# x) = refl
  [|-|]-[|-|]≡[|-∘ˢ-|] (`λ M) = cong `λ_ (trans ([|-|]-[|-|]≡[|-∘ˢ-|] M) ([|-|]-extensional (symˢ qˢ-distrib-∘ˢ) M))
  [|-|]-[|-|]≡[|-∘ˢ-|] (M `$ N) = cong₂ _`$_ ([|-|]-[|-|]≡[|-∘ˢ-|] M) ([|-|]-[|-|]≡[|-∘ˢ-|] N)
  [|-|]-[|-|]≡[|-∘ˢ-|] (M₁ `, M₂) = cong₂ _`,_ ([|-|]-[|-|]≡[|-∘ˢ-|] M₁) ([|-|]-[|-|]≡[|-∘ˢ-|] M₂)
  [|-|]-[|-|]≡[|-∘ˢ-|] (`let M `in N) = cong₂ `let_`in_ ([|-|]-[|-|]≡[|-∘ˢ-|] M) (trans ([|-|]-[|-|]≡[|-∘ˢ-|] N) ([|-|]-extensional (symˢ (transˢ (qˢ-congˢ qˢ-distrib-∘ˢ) qˢ-distrib-∘ˢ)) N))

  ↠-refl : M ↠ M
  ↠-refl {M = `# x}         = `# x
  ↠-refl {M = `λ _}         = `λ ↠-refl
  ↠-refl {M = _ `$ _}       = ↠-refl `$ ↠-refl
  ↠-refl {M = _ `, _}       = ↠-refl `, ↠-refl
  ↠-refl {M = `let _ `in _} = `let ↠-refl `in ↠-refl

  ↠-≡-trans : M ↠ M′ →
              M′ ≡ M″ →
              M ↠ M″
  ↠-≡-trans {M = M} M↠ eq = subst (M ↠_) eq M↠

  ext[-]-ext[-]-ext[-]-ext[-]-cong : δ ∘ᵉ γ ≈ᵉ δ′ ∘ᵉ γ′ →
                                     ∀ (M : Tm Γ A) →
                                     ext[ δ ] ext[ γ ] M ≡ ext[ δ′ ] ext[ γ′ ] M
  ext[-]-ext[-]-ext[-]-ext[-]-cong equiv M =
    begin _ ≡⟨ ext[-]-ext[-]≡ext[-∘ᵉ-] M ⟩
          _ ≡⟨ ext[-]-extensional equiv M ⟩
          _ ≡˘⟨ ext[-]-ext[-]≡ext[-∘ᵉ-] M ⟩
          _ ∎
    where
      open ≡-Reasoning

  ext[-]-[|-|]-[|-|]-ext[-]-cong : δ ᵉ∘ˢ σ ≈ˢ τ ˢ∘ᵉ γ →
                                   ∀ (M : Tm Γ A) →
                                   ext[ δ ] [| σ |] M ≡ [| τ |] ext[ γ ] M
  ext[-]-[|-|]-[|-|]-ext[-]-cong equiv M =
    begin _ ≡⟨ ext[-]-[|-|]≡[|-ᵉ∘ˢ-|] M ⟩
          _ ≡⟨ [|-|]-extensional equiv M ⟩
          _ ≡˘⟨ [|-|]-ext[-]≡[|-ˢ∘ᵉ-|] M ⟩
          _ ∎
    where
      open ≡-Reasoning

  !ˢ-ˢ∘ᵉ-qᵉ : ∀ (δ : Ext Γ Δ) (M : Tm Δ A) →
              !ˢ ext[ δ ] M ˢ∘ᵉ qᵉ δ ≈ˢ δ ᵉ∘ˢ !ˢ M
  !ˢ-ˢ∘ᵉ-qᵉ δ M (here refl) = refl
  !ˢ-ˢ∘ᵉ-qᵉ δ M (there x)   =
    begin (!ˢ ext[ δ ] M ˢ∘ᵉ Wk1ᵉ ∘ᵉ δ) x ≡⟨ ˢ∘ᵉ-∘ᵉ-assoc {σ = !ˢ ext[ δ ] M} {δ = Wk1ᵉ} δ x ⟩
          (Idˢ ˢ∘ᵉ δ) x ≡⟨ [|Idˢ|]-id (`# δ x) ⟩
          `# δ x ∎
    where
      open ≡-Reasoning

  !ˢ-ˢ∘ᵉ-qᵉ′ : ∀ (δ : Ext Γ Δ) (M : Tm Γ A) →
               !ˢ M ˢ∘ᵉ qᵉ δ ≈ˢ forgetˢ δ ,ˢ M
  !ˢ-ˢ∘ᵉ-qᵉ′ δ M (here refl) = refl
  !ˢ-ˢ∘ᵉ-qᵉ′ δ M (there x)   =
    begin (!ˢ M ˢ∘ᵉ Wk1ᵉ ∘ᵉ δ) x ≡⟨ ˢ∘ᵉ-∘ᵉ-assoc {σ = !ˢ M} {δ = Wk1ᵉ} δ x ⟩
          (Idˢ ˢ∘ᵉ δ) x ≡⟨ [|Idˢ|]-id (`# δ x) ⟩
          `# δ x ∎
    where
      open ≡-Reasoning

  !ˢ-,ˢ-ˢ∘ᵉ-qᵉ-qᵉ : ∀ (δ : Ext Γ Δ) (M : Tm Δ A) (N : Tm Δ B) →
                    (!ˢ ext[ δ ] M ,ˢ ext[ δ ] N) ˢ∘ᵉ qᵉ qᵉ δ ≈ˢ δ ᵉ∘ˢ (!ˢ M ,ˢ N)
  !ˢ-,ˢ-ˢ∘ᵉ-qᵉ-qᵉ δ M N (here refl) = refl
  !ˢ-,ˢ-ˢ∘ᵉ-qᵉ-qᵉ δ M N (there x)   =
    begin ((!ˢ ext[ δ ] M ,ˢ ext[ δ ] N) ˢ∘ᵉ Wk1ᵉ ∘ᵉ qᵉ δ) x ≡⟨ ˢ∘ᵉ-∘ᵉ-assoc {σ = !ˢ ext[ δ ] M ,ˢ ext[ δ ] N} {δ = Wk1ᵉ} (qᵉ δ) x ⟩
          ((!ˢ ext[ δ ] M) ˢ∘ᵉ qᵉ δ) x ≡⟨ !ˢ-ˢ∘ᵉ-qᵉ δ M x ⟩
          (δ ᵉ∘ˢ !ˢ M) x ∎
    where
      open ≡-Reasoning

  !ˢ-,ˢ-ˢ∘ᵉ-qᵉ-qᵉ′ : ∀ (δ : Ext Γ Δ) (M : Tm Γ A) (N : Tm Γ B) →
                     (!ˢ M ,ˢ N) ˢ∘ᵉ qᵉ qᵉ δ ≈ˢ forgetˢ δ ,ˢ M ,ˢ N
  !ˢ-,ˢ-ˢ∘ᵉ-qᵉ-qᵉ′ δ M N (here refl) = refl
  !ˢ-,ˢ-ˢ∘ᵉ-qᵉ-qᵉ′ δ M N (there x)   =
    begin ((!ˢ M ,ˢ N) ˢ∘ᵉ Wk1ᵉ ∘ᵉ qᵉ δ) x ≡⟨ ˢ∘ᵉ-∘ᵉ-assoc {σ = !ˢ M ,ˢ N} {δ = Wk1ᵉ} (qᵉ δ) x ⟩
          ((!ˢ M) ˢ∘ᵉ qᵉ δ) x ≡⟨ !ˢ-ˢ∘ᵉ-qᵉ′ δ M x ⟩
          (forgetˢ δ ,ˢ M) x ∎
    where
      open ≡-Reasoning

  infixr 30 ext[_]↠_
  ext[_]↠_ : ∀ (δ : Ext Γ Δ) → M ↠ M′ → ext[ δ ] M ↠ ext[ δ ] M′
  ext[ δ ]↠ (`# x) = ↠-refl
  ext[ δ ]↠ (`λ M↠M′) = `λ (ext[ qᵉ δ ]↠ M↠M′)
  ext[ δ ]↠ (M↠M′ `$ N↠N′) = (ext[ δ ]↠ M↠M′) `$ (ext[ δ ]↠ N↠N′)
  ext[ δ ]↠ (`→β {M′ = M′} {N′ = N′} M↠M′ N↠N′) = ↠-≡-trans (`→β (ext[ qᵉ δ ]↠ M↠M′) (ext[ δ ]↠ N↠N′))
    (sym (ext[-]-[|-|]-[|-|]-ext[-]-cong (symˢ (!ˢ-ˢ∘ᵉ-qᵉ δ N′)) M′))
  ext[ δ ]↠ (`→η {M′ = M′} M↠M′) = ↠-≡-trans (`→η (ext[ δ ]↠ M↠M′))
    (cong `λ_
      (cong (_`$ _)
        (ext[-]-ext[-]-ext[-]-ext[-]-cong (λ x → refl) M′)))
  ext[ δ ]↠ (M₁↠M′₁ `, M₂↠M′₂) = ext[ δ ]↠ M₁↠M′₁ `, ext[ δ ]↠ M₂↠M′₂
  ext[ δ ]↠ (`let M↠M′ `in N↠N′) = `let ext[ δ ]↠ M↠M′ `in ext[ qᵉ qᵉ δ ]↠ N↠N′
  ext[ δ ]↠ (`∧β {N′ = N′} M₁↠M′₁ M₂↠M′₂ N↠N′) = ↠-≡-trans (`∧β (ext[ δ ]↠ M₁↠M′₁) (ext[ δ ]↠ M₂↠M′₂) (ext[ qᵉ qᵉ δ ]↠ N↠N′))
    (sym (ext[-]-[|-|]-[|-|]-ext[-]-cong (symˢ (!ˢ-,ˢ-ˢ∘ᵉ-qᵉ-qᵉ δ _ _)) N′))
  ext[ δ ]↠ (`∧η M↠M′) = `∧η (ext[ δ ]↠ M↠M′)
  ext[ δ ]↠ (`→c {M = M} {L = L}) = ↠-≡-trans `→c
    (cong `let ext[ δ ] M `in_
      (cong (_ `$_)
        (ext[-]-ext[-]-ext[-]-ext[-]-cong (λ x → refl) L)))
  ext[ δ ]↠ (`∧c {M = M} {L = L}) = ↠-≡-trans `∧c
    (cong `let ext[ δ ] M `in_
      (cong `let _ `in_
        (ext[-]-ext[-]-ext[-]-ext[-]-cong
          (λ{ (here refl) → refl ; (there (here refl)) → refl ; (there (there x)) → refl })
          L)))

  infixr 30 ext[_]↠*_
  ext[_]↠*_ : ∀ (δ : Ext Γ Δ) → M ↠* M′ → ext[ δ ] M ↠* ext[ δ ] M′
  ext[ δ ]↠* ε           = ε
  ext[ δ ]↠* (M↠ ◅ M′↠*) = ext[ δ ]↠ M↠ ◅ ext[ δ ]↠* M′↠*

  [|-|]-[|-|]-[|-|]-[|-|]-cong : σ ∘ˢ τ ≈ˢ σ′ ∘ˢ τ′ →
                                 ∀ (M : Tm Γ A) →
                                 [| σ |] [| τ |] M ≡ [| σ′ |] [| τ′ |] M
  [|-|]-[|-|]-[|-|]-[|-|]-cong equiv M =
    begin _ ≡⟨ [|-|]-[|-|]≡[|-∘ˢ-|] M ⟩
          _ ≡⟨ [|-|]-extensional equiv M ⟩
          _ ≡˘⟨ [|-|]-[|-|]≡[|-∘ˢ-|] M ⟩
          _ ∎
    where
      open ≡-Reasoning

  !ˢ-∘ˢ-qˢ : ∀ (σ : Sub Γ Δ) (M : Tm Δ A) →
             !ˢ [| σ |] M ∘ˢ qˢ σ ≈ˢ σ ∘ˢ !ˢ M
  !ˢ-∘ˢ-qˢ σ M (here refl) = refl
  !ˢ-∘ˢ-qˢ σ M (there x)   =
    begin (!ˢ [| σ |] M ∘ˢ Wk1ᵉ ᵉ∘ˢ σ) x ≡⟨ ∘ˢ-ᵉ∘ˢ-assoc σ x ⟩
          (Idˢ ∘ˢ σ) x ≡⟨ [|Idˢ|]-id (σ x) ⟩
          σ x ∎
    where
      open ≡-Reasoning

  !ˢ-∘ˢ-qˢ′ : ∀ (σ : Sub Γ Δ) (M : Tm Γ A) →
              !ˢ M ∘ˢ qˢ σ ≈ˢ σ ,ˢ M
  !ˢ-∘ˢ-qˢ′ σ M (here refl) = refl
  !ˢ-∘ˢ-qˢ′ σ M (there x)   =
    begin (!ˢ M ∘ˢ Wk1ᵉ ᵉ∘ˢ σ) x ≡⟨ ∘ˢ-ᵉ∘ˢ-assoc σ x ⟩
          (Idˢ ∘ˢ σ) x ≡⟨ [|Idˢ|]-id (σ x) ⟩
          σ x ∎
    where
      open ≡-Reasoning

  !ˢ-,ˢ-∘ˢ-qˢ-qˢ : ∀ (σ : Sub Γ Δ) (M : Tm Δ A) (N : Tm Δ B) →
                   (!ˢ [| σ |] M ,ˢ [| σ |] N) ∘ˢ qˢ qˢ σ ≈ˢ σ ∘ˢ (!ˢ M ,ˢ N)
  !ˢ-,ˢ-∘ˢ-qˢ-qˢ σ M N (here refl) = refl
  !ˢ-,ˢ-∘ˢ-qˢ-qˢ σ M N (there x)   =
    begin ((!ˢ [| σ |] M ,ˢ [| σ |] N) ∘ˢ Wk1ᵉ ᵉ∘ˢ qˢ σ) x ≡⟨ ∘ˢ-ᵉ∘ˢ-assoc (qˢ σ) x ⟩
          ((!ˢ [| σ |] M) ∘ˢ qˢ σ) x ≡⟨ !ˢ-∘ˢ-qˢ σ M x ⟩
          (σ ∘ˢ !ˢ M) x ∎
    where
      open ≡-Reasoning

  !ˢ-,ˢ-∘ˢ-qˢ-qˢ′ : ∀ (σ : Sub Γ Δ) (M : Tm Γ A) (N : Tm Γ B) →
                    (!ˢ M ,ˢ N) ∘ˢ qˢ qˢ σ ≈ˢ σ ,ˢ M ,ˢ N
  !ˢ-,ˢ-∘ˢ-qˢ-qˢ′ σ M N (here refl) = refl
  !ˢ-,ˢ-∘ˢ-qˢ-qˢ′ σ M N (there x)   =
    begin ((!ˢ M ,ˢ N) ∘ˢ Wk1ᵉ ᵉ∘ˢ qˢ σ) x ≡⟨ ∘ˢ-ᵉ∘ˢ-assoc (qˢ σ) x ⟩
          ((!ˢ M) ∘ˢ qˢ σ) x ≡⟨ !ˢ-∘ˢ-qˢ′ σ M x ⟩
          (σ ,ˢ M) x ∎
    where
      open ≡-Reasoning

  infixr 30 [|_|]↠_
  [|_|]↠_ : ∀ (σ : Sub Γ Δ) → M ↠ M′ → [| σ |] M ↠ [| σ |] M′
  [| σ |]↠ (`# x) = ↠-refl
  [| σ |]↠ (`λ M↠M′) = `λ ([| qˢ σ |]↠ M↠M′)
  [| σ |]↠ (M↠M′ `$ N↠N′) = ([| σ |]↠ M↠M′) `$ ([| σ |]↠ N↠N′)
  [| σ |]↠ (`→β {M′ = M′} {N′ = N′} M↠M′ N↠N′) = ↠-≡-trans (`→β ([| qˢ σ |]↠ M↠M′) ([| σ |]↠ N↠N′)) ([|-|]-[|-|]-[|-|]-[|-|]-cong (!ˢ-∘ˢ-qˢ σ N′) M′)
  [| σ |]↠ (`→η {M′ = M′} M↠M′) = ↠-≡-trans (`→η ([| σ |]↠ M↠M′)) (cong `λ_ (cong (_`$ _) (ext[-]-[|-|]-[|-|]-ext[-]-cong (λ x → refl) M′)))
  [| σ |]↠ (M₁↠M′₁ `, M₂↠M′₂) = [| σ |]↠ M₁↠M′₁ `, [| σ |]↠ M₂↠M′₂
  [| σ |]↠ (`let M↠M′ `in N↠N′) = `let [| σ |]↠ M↠M′ `in [| qˢ qˢ σ |]↠ N↠N′
  [| σ |]↠ (`∧β {N′ = N′} M₁↠M′₁ M₂↠M′₂ N↠N′) = ↠-≡-trans (`∧β ([| σ |]↠ M₁↠M′₁) ([| σ |]↠ M₂↠M′₂) ([| qˢ qˢ σ |]↠ N↠N′)) ([|-|]-[|-|]-[|-|]-[|-|]-cong (!ˢ-,ˢ-∘ˢ-qˢ-qˢ σ _ _) N′)
  [| σ |]↠ (`∧η M↠M′) = `∧η ([| σ |]↠ M↠M′)
  [| σ |]↠ (`→c {M = M} {L = L}) =
    ↠-≡-trans
      `→c
      (cong `let [| σ |] M `in_
        (cong (_ `$_)
          (ext[-]-[|-|]-[|-|]-ext[-]-cong
            (sym ∘ ext[-]-ext[-]≡ext[-∘ᵉ-] ∘ σ)
            L)))
    where
      open ≡-Reasoning
  [| σ |]↠ (`∧c {M = M} {L = L}) =
    ↠-≡-trans
      `∧c
      (cong
        `let [| σ |] M `in_
        (cong
          `let _ `in_
          (ext[-]-[|-|]-[|-|]-ext[-]-cong
            (λ{ (here refl) → refl
              ; (there (here refl)) → refl
              ; (there (there x)) →
                  begin ext[ qᵉ qᵉ Wkᵉ (_ ∷ _ ∷ []) ] ext ext σ x ≡⟨ ext[-]-ext[-]≡ext[-∘ᵉ-] (ext (σ x)) ⟩
                        ext[ Wkᵉ (_ ∷ []) ∘ᵉ qᵉ Wkᵉ (_ ∷ _ ∷ []) ] ext σ x ≡⟨ ext[-]-ext[-]≡ext[-∘ᵉ-] (σ x) ⟩
                        ext[ Wkᵉ (_ ∷ _ ∷ _ ∷ _ ∷ []) ] σ x ≡˘⟨ ext[-]-ext[-]≡ext[-∘ᵉ-] (σ x) ⟩
                        ext ext[ Wkᵉ (_ ∷ _ ∷ _ ∷ []) ] σ x ≡˘⟨ cong ext_ (ext[-]-ext[-]≡ext[-∘ᵉ-] (σ x)) ⟩
                        ext ext ext[ Wkᵉ (_ ∷ _ ∷ []) ] σ x ≡˘⟨ cong ext_ (cong ext_ (ext[-]-ext[-]≡ext[-∘ᵉ-] (σ x))) ⟩
                        ext ext ext ext (σ x) ∎ })
            L)))
    where
      open ≡-Reasoning

  ------------------------------------------------------------
  -- Helpers for multi-step parallel reduction
  ------------------------------------------------------------

  ξ-of-↝*-↠* : ∀ {ℓ″} (_↝_ : Rel (Tm Γ A) ℓ″) (f : Tm Γ A → Tm Δ B) →
               (∀ {L L′} → L ↝ L′ → f L ↠ f L′) →
               ∀ {L L′} → Star _↝_ L L′ → f L ↠* f L′
  ξ-of-↝*-↠* _↝_ f ξ-rule ε           = ε
  ξ-of-↝*-↠* _↝_ f ξ-rule (L↠ ◅ L′↠*) = ξ-rule L↠ ◅ ξ-of-↝*-↠* _↝_ f ξ-rule L′↠*

  ξ-of-↠* : ∀ (f : Tm Γ A → Tm Δ B) →
            (∀ {L L′} → L ↠ L′ → f L ↠ f L′) →
            ∀ {L L′} → L ↠* L′ → f L ↠* f L′
  ξ-of-↠* = ξ-of-↝*-↠* _↠_

open OpSemProp

module LogRel where
  data Cont∧ : Ctx → Tp → Tp → Set where
    []  : ------------
          Cont∧ Γ A A

    _∷_ : Tm (A₁ ∷ A₂ ∷ Γ) B →
          Cont∧ Γ B C →
          ---------------------
          Cont∧ Γ (A₁ `∧ A₂) C

  variable
    K K′ K′₀ K′₁ K′₂ K′₃ K″ K″₀ K″₁ K″₂ K″₃ K‴ K‴₀ K‴₁ K‴₂ K‴₃ K₀ K₁ K₂ K₃ : Cont∧ Γ A B
    J J′ J′₀ J′₁ J′₂ J′₃ J″ J″₀ J″₁ J″₂ J″₃ J‴ J‴₀ J‴₁ J‴₂ J‴₃ J₀ J₁ J₂ J₃ : Cont∧ Γ A B

  data Nfᶜ : Cont∧ Γ A B → Set where
    []   : -------------------------------
           Nfᶜ {Γ = Γ} {A = A} {B = A} []

    _∷[] : Nf N →
           -------------
           Nfᶜ (N ∷ [])

  _`$$ᶜ_ : Cont∧ Γ A B → Tm Γ A → Tm Γ B
  []      `$$ᶜ M = M
  (N ∷ K) `$$ᶜ M = K `$$ᶜ (`let M `in N)

  infixr 30 ext[_]ᶜ_
  ext[_]ᶜ_ : Ext Δ Γ → Cont∧ Γ A B → Cont∧ Δ A B
  ext[ δ ]ᶜ []      = []
  ext[ δ ]ᶜ (N ∷ K) = ext[ qᵉ qᵉ δ ] N ∷ ext[ δ ]ᶜ K

  infix 4 _↠ᶜ_
  _↠ᶜ_ : Cont∧ Γ A B → Cont∧ Γ A B → Set
  K ↠ᶜ K′ = ∀ M → K `$$ᶜ M ↠ K′ `$$ᶜ M

  infix   4 _↠ᶜ*_
  _↠ᶜ*_ : Rel (Cont∧ Γ A B) _
  K ↠ᶜ* K′ = ∀ M → K `$$ᶜ M ↠* K′ `$$ᶜ M

  infix 4 _haltsᶜ
  _haltsᶜ : Cont∧ Γ A B → Set
  K haltsᶜ = ∃[ K′ ] K ↠ᶜ* K′ × Nfᶜ K′

  mutual
    infix 4 ℜ[_]_
    ℜ[_]_ : ∀ A {Γ} → Tm Γ A → Set
    ℜ[ base     ] M = M halts
    ℜ[ A `→ B   ] M = ∀ {Δ} {N} (δ : Ext Δ _) → ℜ[ A ] N → ℜ[ B ] (ext[ δ ] M `$ N)
    ℜ[ A₁ `∧ A₂ ] M = ∀ {Δ} (δ : Ext Δ _) {B} (K : Cont∧ _ _ B) → ℜᶜ[ A₁ & A₂ ] K → (K `$$ᶜ ext[ δ ] M) halts

    infix 4 ℜᶜ[_&_]_
    ℜᶜ[_&_]_ : ∀ A₁ A₂ {Γ} → Cont∧ Γ (A₁ `∧ A₂) B → Set
    ℜᶜ[ A₁ & A₂ ] K = ∀ {Δ} (δ : Ext Δ _) {M₁ M₂} → ℜ[ A₁ ] M₁ → ℜ[ A₂ ] M₂ → ∀ {M′} → M′ ↠* (M₁ `, M₂) → (ext[ δ ]ᶜ K `$$ᶜ M′) halts

  infix 4 ℜˢ[_]_
  ℜˢ[_]_ : ∀ Δ → ∀ {Γ} → Sub Γ Δ → Set
  ℜˢ[ []    ] σ = ⊤
  ℜˢ[ A ∷ Δ ] σ = ℜˢ[ Δ ] (σ ∘ there) × ℜ[ A ] (σ (here refl))

open LogRel

module LogRelProp where
  `λ-halts : M halts →
             `λ M halts
  `λ-halts (_ , M↠* , V) = -, ξ-of-↠* `λ_ `λ_ M↠* , `λ V

  `,-halts : M₁ halts →
             M₂ halts →
             (M₁ `, M₂) halts
  `,-halts (_ , M₁↠* , V₁) (_ , M₂↠* , V₂) = -, ξ-of-↠* (_`, _) (_`, ↠-refl) M₁↠* Star.◅◅ ξ-of-↠* (_ `,_) (↠-refl `,_) M₂↠* , V₁ `, V₂

  `let-`in-halts : Ne M →
                   N halts →
                   (`let M `in N) halts
  `let-`in-halts RM (_ , N↠* , VN) = -, ξ-of-↠* `let _ `in_ `let ↠-refl `in_ N↠* , `let RM `in VN

  halts-closed : M′ halts → M ↠ M′ → M halts
  halts-closed (_ , M′↠* , V) M↠M′ = -, M↠M′ ◅ M′↠* , V

  halts-closed* : M′ halts → M ↠* M′ → M halts
  halts-closed* hM ε          = hM
  halts-closed* hM (M↠M′ ◅ M′↠*M″) = halts-closed (halts-closed* hM M′↠*M″) M↠M′

  ext[-]-preserves-halts : ∀ (δ : Ext Γ Δ) → M halts → ext[ δ ] M halts
  ext[-]-preserves-halts δ (_ , M↠* , V) = -, ext[ δ ]↠* M↠* , ext[-]-preserves-Nf δ V

  _`$$ᶜ↠_ : ∀ (K : Cont∧ Γ A B) →
            M ↠ M′ →
            K `$$ᶜ M ↠ K `$$ᶜ M′
  []      `$$ᶜ↠ M↠M′ = M↠M′
  (_ ∷ K) `$$ᶜ↠ M↠M′ = K `$$ᶜ↠ (`let M↠M′ `in ↠-refl)

  _`$$ᶜ↠*_ : ∀ (K : Cont∧ Γ A B) →
             M ↠* M′ →
             K `$$ᶜ M ↠* K `$$ᶜ M′
  K `$$ᶜ↠* ε               = ε
  K `$$ᶜ↠* (M↠M′ ◅ M′↠*M″) = K `$$ᶜ↠ M↠M′ ◅ K `$$ᶜ↠* M′↠*M″

  ext[Idᵉ]ᶜ-id : ∀ (K : Cont∧ Γ A B) →
                 ext[ Idᵉ ]ᶜ K ≡ K
  ext[Idᵉ]ᶜ-id []      = refl
  ext[Idᵉ]ᶜ-id (N ∷ K) = cong₂ _∷_ (ext[qᵉ[-]-Idᵉ]-id (_ ∷ _ ∷ []) N) (ext[Idᵉ]ᶜ-id K)

  ext[-]ᶜ-ext[-]ᶜ≡ext[-∘ᵉ-]ᶜ : ∀ (K : Cont∧ Γ A B) →
                               ext[ δ ]ᶜ ext[ γ ]ᶜ K ≡ ext[ δ ∘ᵉ γ ]ᶜ K
  ext[-]ᶜ-ext[-]ᶜ≡ext[-∘ᵉ-]ᶜ                 []      = refl
  ext[-]ᶜ-ext[-]ᶜ≡ext[-∘ᵉ-]ᶜ {δ = δ} {γ = γ} (N ∷ K)
    rewrite ext[-]-ext[-]≡ext[-∘ᵉ-] {δ = qᵉ qᵉ δ} {γ = qᵉ qᵉ γ} N
          | ext[-]-extensional {δ = qᵉ qᵉ (δ ∘ᵉ γ)} {δ′ = qᵉ qᵉ δ ∘ᵉ qᵉ qᵉ γ} (transᵉ (qᵉ-congᵉ qᵉ-distrib-∘ᵉ) qᵉ-distrib-∘ᵉ) N
          | ext[-]ᶜ-ext[-]ᶜ≡ext[-∘ᵉ-]ᶜ {δ = δ} {γ = γ} K = refl

  ∈-of-ℜˢ : ∀ (x : A ∈ Γ) →
            ℜˢ[ Γ ] σ →
            ℜ[ A ] (σ x)
  ∈-of-ℜˢ {Γ = _ ∷ Γ} (here refl) rσ = rσ .proj₂
  ∈-of-ℜˢ {Γ = _ ∷ Γ} (there x)   rσ = ∈-of-ℜˢ x (rσ .proj₁)

  ℜ-closed : ℜ[ A ] M′ → M ↠ M′ → ℜ[ A ] M
  ℜ-closed {A = base}     rM′ M↠M′        = halts-closed rM′ M↠M′
  ℜ-closed {A = A `→ B}   rM′ M↠M′ δ rN   = ℜ-closed (rM′ δ rN) (ext[ δ ]↠ M↠M′ `$ ↠-refl)
  ℜ-closed {A = A₁ `∧ A₂} rM′ M↠M′ δ K rK = halts-closed (rM′ δ K rK) (K `$$ᶜ↠ ext[ δ ]↠ M↠M′)

  ℜ-closed* : ℜ[ A ] M′ → M ↠* M′ → ℜ[ A ] M
  ℜ-closed* rM′ ε               = rM′
  ℜ-closed* rM′ (M→M′ ◅ M′→*M″) = ℜ-closed (ℜ-closed* rM′ M′→*M″) M→M′

  ext[-]-preserves-ℜ : ∀ (δ : Ext Γ Δ) → ℜ[ A ] M → ℜ[ A ] (ext[ δ ] M)
  ext[-]-preserves-ℜ {A = base}             δ rM      = ext[-]-preserves-halts δ rM
  ext[-]-preserves-ℜ {A = A `→ B}   {M = M} δ rM γ rN
    rewrite ext[-]-ext[-]≡ext[-∘ᵉ-] {δ = γ} {γ = δ} M = rM (γ ∘ᵉ δ) rN
  ext[-]-preserves-ℜ {A = A₁ `∧ A₂} {M = M} δ rM γ K rK
    rewrite ext[-]-ext[-]≡ext[-∘ᵉ-] {δ = γ} {γ = δ} M = rM (γ ∘ᵉ δ) K rK

  ext[-]-preserves-ℜᶜ : ∀ (δ : Ext Γ Δ) → ℜᶜ[ A₁ & A₂ ] K → ℜᶜ[ A₁ & A₂ ] (ext[ δ ]ᶜ K)
  ext[-]-preserves-ℜᶜ {K = []}    δ rK γ = rK (γ ∘ᵉ δ)
  ext[-]-preserves-ℜᶜ {K = N ∷ K} δ rK γ
    with rK′ ← rK (γ ∘ᵉ δ)
      rewrite ext[-]ᶜ-ext[-]ᶜ≡ext[-∘ᵉ-]ᶜ {δ = γ} {γ = δ} K
            | ext[-]-ext[-]≡ext[-∘ᵉ-] {δ = qᵉ qᵉ γ} {γ = qᵉ qᵉ δ} N
            | ext[-]-extensional {δ = qᵉ qᵉ (γ ∘ᵉ δ)} {δ′ = qᵉ qᵉ γ ∘ᵉ qᵉ qᵉ δ} (transᵉ (qᵉ-congᵉ qᵉ-distrib-∘ᵉ) qᵉ-distrib-∘ᵉ) N = rK′

  ᵉ∘ˢ-preserves-ℜˢ : ∀ (δ : Ext Γ Δ) → ℜˢ[ Ψ ] σ → ℜˢ[ Ψ ] (δ ᵉ∘ˢ σ)
  ᵉ∘ˢ-preserves-ℜˢ {Ψ = []}    δ tt        = tt
  ᵉ∘ˢ-preserves-ℜˢ {Ψ = _ ∷ Ψ} δ (rσ , rM) = ᵉ∘ˢ-preserves-ℜˢ δ rσ , ext[-]-preserves-ℜ δ rM

  `∧cᶜ↠* : ∀ {M : Tm Γ (A₁ `∧ A₂)} {N : Tm (A₁ ∷ A₂ ∷ Γ) B} (K : Cont∧ Γ B C) →
           K `$$ᶜ (`let M `in N) ↠* `let M `in (ext[ Wkᵉ (_ ∷ _ ∷ []) ]ᶜ K `$$ᶜ N)
  `∧cᶜ↠* []      = ε
  `∧cᶜ↠* (L ∷ K) = K `$$ᶜ↠ `∧c ◅ `∧cᶜ↠* K

  mutual
    reify : ∀ A {M : Tm Γ A} →
            ℜ[ A ] M →
            M halts
    reify base               rM = rM
    reify (A `→ B)           rM = halts-closed (`λ-halts (reify B (rM Wk1ᵉ (reflect (`# here refl))))) (`→η ↠-refl)
    reify (A₁ `∧ A₂) {M = M} rM
      with hM ← rM Idᵉ [] (λ δ rM₁ rM₂ M′↠* → halts-closed* (`,-halts (reify A₁ rM₁) (reify A₂ rM₂)) M′↠*)
        rewrite ext[Idᵉ]-id M       = hM

    reflect : Ne M → ℜ[ A ] M
    reflect {A = base}     RM        = -, ε , `↑ RM
    reflect {A = A `→ B}   RM δ rN   =
      let _ , N↠*N′ , VN′ = reify A rN in
      ℜ-closed* (reflect {A = B} (ext[-]-preserves-Ne δ RM `$ VN′)) (ξ-of-↠* (_ `$_) (↠-refl `$_) N↠*N′)
    reflect {A = A₁ `∧ A₂} RM δ K rK =
      halts-closed*
        (`let-`in-halts
          (ext[-]-preserves-Ne δ RM)
          (rK
            (Wkᵉ (_ ∷ _ ∷ []))
            (reflect (`# here refl))
            (reflect (`# there (here refl)))
            ε))
        (K `$$ᶜ↠ `∧η ↠-refl ◅ `∧cᶜ↠* K)

  ℜ-∧-elim : ℜ[ A₁ `∧ A₂ ] M →
             (∀ {Δ} (δ : Ext Δ _) {M₁ M₂} → ℜ[ A₁ ] M₁ → ℜ[ A₂ ] M₂ → ℜ[ B ] ([| !ˢ M₂ ,ˢ M₁ |] ext[ qᵉ qᵉ δ ] N)) →
             ℜ[ B ] (`let M `in N)
  ℜ-∧-elim {M = M} {B = base}     {N = N} rM rN
    with hMN ← rM Idᵉ (_ ∷ []) (λ δ rM₁ rM₂ M′↠* → halts-closed* (halts-closed (rN δ rM₁ rM₂) (`∧β ↠-refl ↠-refl ↠-refl)) (ξ-of-↠* (`let_`in _) (`let_`in ↠-refl) M′↠*))
      rewrite ext[Idᵉ]-id M                                  = hMN
  ℜ-∧-elim {M = M} {B = B `→ C}   {N = N} rM rN {N = L} δ rL =
    ℜ-closed
      (ℜ-∧-elim
        (ext[-]-preserves-ℜ {M = M} δ rM)
        λ γ {M₁ = M₁} {M₂ = M₂} rM₁ rM₂ →
          subst
            ℜ[ C ]_
            (cong₂
              _`$_
              (begin _ ≡⟨ ext[Idᵉ]-id ([| !ˢ M₂ ,ˢ M₁ |] ext[ qᵉ qᵉ (γ ∘ᵉ δ) ] N) ⟩
                     _ ≡⟨ cong [| !ˢ M₂ ,ˢ M₁ |]_ (ext[-]-extensional (transᵉ (qᵉ-congᵉ qᵉ-distrib-∘ᵉ) qᵉ-distrib-∘ᵉ) N) ⟩
                     _ ≡˘⟨ cong [| !ˢ M₂ ,ˢ M₁ |]_ (ext[-]-ext[-]≡ext[-∘ᵉ-] N) ⟩
                     _ ∎)
              (begin _ ≡˘⟨ [|forgetˢ-|]≡ext[-] γ L ⟩
                     _ ≡˘⟨ [|-|]-ext[-]≡[|-ˢ∘ᵉ-|] L ⟩
                     _ ≡˘⟨ [|-|]-extensional (!ˢ-,ˢ-ˢ∘ᵉ-qᵉ-qᵉ′ γ M₂ M₁) (ext[ Wkᵉ (_ ∷ _ ∷ []) ] L) ⟩
                     _ ≡˘⟨ [|-|]-ext[-]≡[|-ˢ∘ᵉ-|] (ext[ Wkᵉ (_ ∷ _ ∷ []) ] L) ⟩
                     _ ∎))
            (rN (γ ∘ᵉ δ) rM₁ rM₂ Idᵉ (ext[-]-preserves-ℜ γ rL)))
      `→c
    where
      open ≡-Reasoning
  ℜ-∧-elim         {B = B₁ `∧ B₂} {N = N} rM rN δ K rK       =
    rM
      δ
      (_ ∷ K)
      λ γ {M₁ = M₁} {M₂ = M₂} rM₁ rM₂ M′↠* →
        halts-closed*
          (subst
            (λ L → (ext[ γ ]ᶜ K `$$ᶜ L) halts)
            (begin _ ≡⟨ ext[Idᵉ]-id ([| !ˢ M₂ ,ˢ M₁ |] ext[ qᵉ qᵉ (γ ∘ᵉ δ) ] N) ⟩
                   _ ≡⟨ cong [| !ˢ M₂ ,ˢ M₁ |]_ (ext[-]-extensional (transᵉ (qᵉ-congᵉ qᵉ-distrib-∘ᵉ) qᵉ-distrib-∘ᵉ) N) ⟩
                   _ ≡˘⟨ cong [| !ˢ M₂ ,ˢ M₁ |]_ (ext[-]-ext[-]≡ext[-∘ᵉ-] N) ⟩
                   _ ∎)
            (rN (γ ∘ᵉ δ) rM₁ rM₂ Idᵉ (ext[ γ ]ᶜ K) (ext[-]-preserves-ℜᶜ {K = K} γ rK)))
          (ext[ γ ]ᶜ K `$$ᶜ↠* (ξ-of-↠* (`let_`in _) (`let_`in ↠-refl) M′↠* Star.◅◅ `∧β ↠-refl ↠-refl ↠-refl ◅ ε))
    where
      open ≡-Reasoning

  eval : ℜˢ[ Γ ] σ →
         ∀ (M : Tm Γ A) →
         ℜ[ A ] [| σ |] M
  eval {σ = σ} rσ (`# x) = ∈-of-ℜˢ x rσ
  eval {σ = σ} rσ (`λ M) {N = N} δ rN =
    ℜ-closed
      (eval {σ = (δ ᵉ∘ˢ σ) ,ˢ N} (ᵉ∘ˢ-preserves-ℜˢ δ rσ , rN) M)
      (↠-≡-trans (`→β ↠-refl ↠-refl)
        (trans
          (cong
            [| !ˢ N |]_
            (trans
              (ext[-]-[|-|]≡[|-ᵉ∘ˢ-|] M)
              ([|-|]-extensional (symˢ qˢ-distrib-ᵉ∘ˢ) M)))
          (trans
            ([|-|]-[|-|]≡[|-∘ˢ-|] M)
            ([|-|]-extensional (!ˢ-∘ˢ-qˢ′ (δ ᵉ∘ˢ σ) N) M))))
  eval {σ = σ} rσ (M `$ N)
    with rMN ← eval rσ M Idᵉ (eval rσ N)
      rewrite ext[Idᵉ]-id ([| σ |] M) = rMN
  eval {σ = σ} rσ (M₁ `, M₂) δ K rK
    with rM₁ ← eval rσ M₁
       | rM₂ ← eval rσ M₂
      with rM₁M₂ ← rK Idᵉ (ext[-]-preserves-ℜ δ rM₁) (ext[-]-preserves-ℜ δ rM₂) ε
        rewrite ext[Idᵉ]ᶜ-id K        = rM₁M₂
  eval {σ = σ} rσ (`let M `in N)
    with rM ← eval rσ M =
    ℜ-∧-elim
      rM
      λ δ {M₁ = M₁} {M₂ = M₂} rM₁ rM₂ →
        subst
          ℜ[ _ ]_
          (begin _ ≡˘⟨ [|-|]-extensional (!ˢ-,ˢ-∘ˢ-qˢ-qˢ′ (δ ᵉ∘ˢ σ) M₂ M₁) N ⟩
                 _ ≡˘⟨ [|-|]-[|-|]≡[|-∘ˢ-|] N ⟩
                 _ ≡⟨ cong [| !ˢ M₂ ,ˢ M₁ |]_ ([|-|]-extensional (transˢ (qˢ-congˢ qˢ-distrib-ᵉ∘ˢ) qˢ-distrib-ᵉ∘ˢ) N) ⟩
                 _ ≡˘⟨ cong [| !ˢ M₂ ,ˢ M₁ |]_ (ext[-]-[|-|]≡[|-ᵉ∘ˢ-|] N) ⟩
                 _ ∎)
          (eval {σ = (δ ᵉ∘ˢ σ) ,ˢ M₂ ,ˢ M₁} ((ᵉ∘ˢ-preserves-ℜˢ δ rσ , rM₂) , rM₁) N)
    where
      open ≡-Reasoning
