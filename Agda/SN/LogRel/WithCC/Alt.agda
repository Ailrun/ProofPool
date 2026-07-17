{-# OPTIONS --safe #-}
module SN.LogRel.WithCC.Alt where

open import Agda.Primitive                                              using (Level; lzero)
open import Data.List                                                   using ([]; _∷_; _++_)
open import Data.List.Membership.Propositional                          using (_∈_)
open import Data.List.Relation.Unary.Any                                using (here; there)
open import Data.Nat
open import Data.Nat.Induction
import Data.Nat.Properties as ℕ
open import Data.Product                                                using (_×_; _,_; proj₁; proj₂; -,_; ∃-syntax; Σ-syntax)
open import Data.Sum                                                    as ⊎ using (_⊎_; inj₁; inj₂)
open import Data.Unit                                                   using (⊤; tt)
open import Function                                                    using (case_of_; flip; id; Morphism; _on_; _∘_; _∋_)
open import Induction.WellFounded                                       using (Acc; acc; acc-inverse; WellFounded)
open import Relation.Binary                                             using ( REL; Rel; Setoid
                                                                              ; Symmetric; Trans; Transitive
                                                                              ; _Preserves_⟶_; _Preserves₂_⟶_⟶_; _=[_]⇒_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive       using (Star; ε; _◅_; _◅◅_)
import Relation.Binary.Construct.Closure.ReflexiveTransitive            as Star
import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties as Star
open import Relation.Binary.Construct.Closure.Transitive                using (TransClosure; [_]; _∷_)
import Relation.Binary.Construct.Closure.Transitive                     as TransClosure
open import Relation.Binary.Construct.Union                             using (_∪_)
open import Relation.Binary.PropositionalEquality                       using (_≡_; refl; cong; subst; subst₂; sym; trans)
open import Relation.Unary                                              using (Pred)
open import Relation.Nullary                                            using (¬_)

open import PPLib.Membership.Nth

open import Syntax.Church.STLC.WithSum.Alt.Base         hiding (module Variables)
open import Syntax.Church.STLC.WithSum.Alt.Properties
open import Syntax.Church.STLC.WithSum.Alt.Substitution

variable
  ℓ ℓ′ ℓ″ ℓ‴ : Level

open Variables

module OpSem where
  ----------------------------------------------------------
  -- Single-step Reduction
  ----------------------------------------------------------

  infix 4 _⟶_
  infix 4 _⟶ᵉ_
  data _⟶_ : Rel (Ex Γ A) lzero
  data _⟶ᵉ_ : Rel (ExE Γ A B) lzero

  data _⟶_ where
    _`∷ˢ? : e ⟶ e′ →
            ----------------------
            e `∷ˢ ee ⟶ e′ `∷ˢ ee

    ?`∷ˢ_ : ∀ {ee : ExE Γ A B} →
            ee ⟶ᵉ ee′ →
            ----------------------
            e `∷ˢ ee ⟶ e `∷ˢ ee′

    `λ_   : e ⟶ e′ →
            --------------
            `λ e ⟶ `λ e′

    `→β   : ∀ {e : Ex (A ∷ Γ) B} {f : Ex Γ A} →
            ------------------------------------
            `λ e `∷ˢ -`$ f ⟶ ⟦ !ˢ f ⟧ᵛ e

    `injₗ : e ⟶ e′ →
            ----------------------------
            `injₗ {B = B} e ⟶ `injₗ e′

    `injᵣ : e ⟶ e′ →
            ----------------------------
            `injᵣ {A = A} e ⟶ `injᵣ e′

    `+βₗ  : ∀ {e : Ex Γ A}
              {fₗ : Ex (A ∷ Γ) C} {fᵣ : Ex (B ∷ Γ) C} →
            -----------------------------------------------
            `injₗ e `∷ˢ `case-`of fₗ `/ fᵣ ⟶ ⟦ !ˢ e ⟧ᵛ fₗ

    `+βᵣ  : ∀ {e : Ex Γ B}
              {fₗ : Ex (A ∷ Γ) C} {fᵣ : Ex (B ∷ Γ) C} →
            -----------------------------------------------
            `injᵣ e `∷ˢ `case-`of fₗ `/ fᵣ ⟶ ⟦ !ˢ e ⟧ᵛ fᵣ

    `+χ   : ∀ {e : Ex Γ (A `+ B)}
              {fₗ : Ex (A ∷ Γ) C} {fᵣ : Ex (B ∷ Γ) C}
              {ee : ExE Γ C D} →
            --------------------------------------------------
            e `∷ˢ `case-`of fₗ `/ fᵣ `∷ˢ ee
              ⟶ e `∷ˢ
                   `case-`of (fₗ `∷ˢ RawAppSub.forExE Wkᵛ ee)
                          `/ (fᵣ `∷ˢ RawAppSub.forExE Wkᵛ ee)

  data _⟶ᵉ_ where
    -`$_          : e ⟶ e′ →
                    -------------------------
                    -`$_ {B = B} e ⟶ᵉ -`$ e′

    `case-`of_`/? : fₗ ⟶ f′ₗ →
                    ------------------------------------------
                    `case-`of fₗ `/ fᵣ ⟶ᵉ `case-`of f′ₗ `/ fᵣ

    `case-`of?`/_ : fᵣ ⟶ f′ᵣ →
                    ------------------------------------------
                    `case-`of fₗ `/ fᵣ ⟶ᵉ `case-`of fₗ `/ f′ᵣ

  ----------------------------------------------------------
  -- Ordinary Multi-step Reduction
  ----------------------------------------------------------

  infix   4 _⟶*_
  _⟶*_ : Rel (Ex Γ A) _
  _⟶*_ = Star _⟶_

  module ⟶*-Reasoning {Γ A} = Star.StarReasoning (_⟶_ {Γ} {A})

  infix   4 _⟶ᵉ*_
  _⟶ᵉ*_ : Rel (ExE Γ A B) _
  _⟶ᵉ*_ = Star _⟶ᵉ_

  module ⟶ᵉ*-Reasoning {Γ A B} = Star.StarReasoning (_⟶ᵉ_ {Γ} {A} {B})

  ----------------------------------------------------------
  -- Flipped Reductions
  ----------------------------------------------------------

  infix 4 _⟵_
  _⟵_ : Rel (Ex Γ A) _
  _⟵_ = flip _⟶_

  infix 4 _+⟵_
  _+⟵_ : Rel (Ex Γ A) _
  _+⟵_ = TransClosure _⟵_

  module Properties where
    module ⟦_⟧ᵉ⟶_ where
      forEx  : (δ : Ext Γ Δ) → ∀ {e e′ : Ex Δ A} → e ⟶ e′ → ⟦ δ ⟧ᵛ e ⟶ ⟦ δ ⟧ᵛ e′
      forExE : (δ : Ext Γ Δ) → ∀ {ee ee′ : ExE Δ A B} → ee ⟶ᵉ ee′ → RawAppSub.forExE δ ee ⟶ᵉ RawAppSub.forExE δ ee′

      forEx δ (e⟶ `∷ˢ?)                              = (forEx δ e⟶) `∷ˢ?
      forEx δ (  ?`∷ˢ_ {Γ = Δ} {A = A} {B = B} ee⟶)  = ?`∷ˢ forExE δ ee⟶
      forEx δ (`λ e⟶)                                = `λ (forEx (qᵉ δ) e⟶)
      forEx δ (`→β {e = e} {f})
        rewrite sym (⟦!ᵛ⟦-⟧ᵛ-⟧ᵛ⟦qᵛ-⟧ᵛ≡⟦-⟧ᵛ⟦!ᵛ-⟧ᵛ δ f e) = `→β
      forEx δ (`injₗ e⟶)                             = `injₗ (forEx δ e⟶)
      forEx δ (`injᵣ e⟶)                             = `injᵣ (forEx δ e⟶)
      forEx δ (`+βₗ {e = e} {fₗ = fₗ})
        rewrite sym (⟦!ᵛ⟦-⟧ᵛ-⟧ᵛ⟦qᵛ-⟧ᵛ≡⟦-⟧ᵛ⟦!ᵛ-⟧ᵛ δ e fₗ) = `+βₗ
      forEx δ (`+βᵣ {e = e} {fᵣ = fᵣ})
        rewrite sym (⟦!ᵛ⟦-⟧ᵛ-⟧ᵛ⟦qᵛ-⟧ᵛ≡⟦-⟧ᵛ⟦!ᵛ-⟧ᵛ δ e fᵣ) = `+βᵣ
      forEx δ (`+χ {A = A} {B = B} {ee = ee})
        rewrite forExE-qᵉᵉ-forExE-Wkᵛ≡forExE-Wkᵛ-forExE {A = A} δ ee
              | forExE-qᵉᵉ-forExE-Wkᵛ≡forExE-Wkᵛ-forExE {A = B} δ ee = `+χ

      forExE δ (-`$ e⟶)           = -`$ (forEx δ e⟶)
      forExE δ `case-`of eₗ⟶ `/?  = `case-`of (forEx (qᵉ δ) eₗ⟶) `/?
      forExE δ (`case-`of?`/ eᵣ⟶) = `case-`of?`/ (forEx (qᵉ δ) eᵣ⟶)
    infixr 50 ⟦_⟧ᵉ⟶_
    ⟦_⟧ᵉ⟶_ : (δ : Ext Γ Δ) → ∀ {e e′ : Ex Δ A} → e ⟶ e′ → ⟦ δ ⟧ᵛ e ⟶ ⟦ δ ⟧ᵛ e′
    ⟦_⟧ᵉ⟶_ = ⟦_⟧ᵉ⟶_.forEx

    infixr 50 ⟦_⟧ᵉ⟶*_
    ⟦_⟧ᵉ⟶*_ : ∀ {e e′ : Ex Δ A} (δ : Ext Γ Δ) → e ⟶* e′ → ⟦ δ ⟧ᵛ e ⟶* ⟦ δ ⟧ᵛ e′
    ⟦_⟧ᵉ⟶*_ δ = Star.gmap (Appᵛ δ) ⟦ δ ⟧ᵉ⟶_

    module ⟦_⟧ᵛ⟶_ where
      forEx  : (σ : Sub Γ Δ) → ∀ {e e′ : Ex Δ A} → e ⟶ e′ → ⟦ σ ⟧ᵛ e ⟶ ⟦ σ ⟧ᵛ e′
      forExE : (σ : Sub Γ Δ) → ∀ {ee ee′ : ExE Δ A B} → ee ⟶ᵉ ee′ → RawAppSub.forExE σ ee ⟶ᵉ RawAppSub.forExE σ ee′

      forEx σ (e⟶ `∷ˢ?)                                              = (forEx σ e⟶) `∷ˢ?
      forEx σ (?`∷ˢ_ {Γ = Δ} {A = A} {B = B} ee⟶)                    = ?`∷ˢ forExE σ ee⟶
      forEx σ (`λ e⟶)                                                = `λ (forEx (qᵉ σ) e⟶)
      forEx σ (`→β {e = e} {f})
        rewrite sym (⟦!ᵛ⟦-⟧ᵛ-⟧ᵛ⟦qᵛ-⟧ᵛ≡⟦-⟧ᵛ⟦!ᵛ-⟧ᵛ ⦃ ExtVarSub ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ SubVarSub ⦄ σ f e)             = `→β
      forEx σ (`injₗ e⟶)                                             = `injₗ (forEx σ e⟶)
      forEx σ (`injᵣ e⟶)                                             = `injᵣ (forEx σ e⟶)
      forEx σ (`+βₗ {e = e} {fₗ = fₗ})
        rewrite sym (⟦!ᵛ⟦-⟧ᵛ-⟧ᵛ⟦qᵛ-⟧ᵛ≡⟦-⟧ᵛ⟦!ᵛ-⟧ᵛ ⦃ ExtVarSub ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ SubVarSub ⦄ σ e fₗ)            = `+βₗ
      forEx σ (`+βᵣ {e = e} {fᵣ = fᵣ})
        rewrite sym (⟦!ᵛ⟦-⟧ᵛ-⟧ᵛ⟦qᵛ-⟧ᵛ≡⟦-⟧ᵛ⟦!ᵛ-⟧ᵛ ⦃ ExtVarSub ⦄ ⦃ _ ⦄ ⦃ _ ⦄ ⦃ SubVarSub ⦄ σ e fᵣ)            = `+βᵣ
      forEx σ (`+χ {A = A} {B = B} {ee = ee})
        rewrite forExE-qᵉˢ-forExE-Wkᵛ≡forExE-Wkᵛ-forExE {A = A} σ ee
              | forExE-qᵉˢ-forExE-Wkᵛ≡forExE-Wkᵛ-forExE {A = B} σ ee = `+χ

      forExE σ (-`$ e⟶)           = -`$ (forEx σ e⟶)
      forExE σ `case-`of eₗ⟶ `/?  = `case-`of (forEx (qᵉ σ) eₗ⟶) `/?
      forExE σ (`case-`of?`/ eᵣ⟶) = `case-`of?`/ (forEx (qᵉ σ) eᵣ⟶)
    infixr 50 ⟦_⟧ᵛ⟶_
    ⟦_⟧ᵛ⟶_ : (σ : Sub Γ Δ) → ∀ {e e′ : Ex Δ A} → e ⟶ e′ → ⟦ σ ⟧ᵛ e ⟶ ⟦ σ ⟧ᵛ e′
    ⟦_⟧ᵛ⟶_ = ⟦_⟧ᵛ⟶_.forEx

    infixr 50 ⟦_⟧ᵛ⟶*_
    ⟦_⟧ᵛ⟶*_ : ∀ {e e′ : Ex Δ A} (σ : Sub Γ Δ) → e ⟶* e′ → ⟦ σ ⟧ᵛ e ⟶* ⟦ σ ⟧ᵛ e′
    ⟦_⟧ᵛ⟶*_ σ = Star.gmap (Appᵛ σ) ⟦ σ ⟧ᵛ⟶_

    ------------------------------------------------------------
    -- Helpers for multi-step parallel reduction
    ------------------------------------------------------------

    ξ-of-⟶* : ∀ {T : Set ℓ′} {R : Rel T ℓ″} (f : T → Ex Δ A) → R =[ f ]⇒ _⟶_ → Star R =[ f ]⇒ _⟶*_
    ξ-of-⟶* = Star.gmap

    ξ-of-⟶*′ : ∀ (f : Ex Γ A → Ex Δ B) → _⟶_ =[ f ]⇒ _⟶_ → _⟶*_ =[ f ]⇒ _⟶*_
    ξ-of-⟶*′ = ξ-of-⟶*

    [!ᵛ⟶_]_ : ∀ {g g′ : Ex Δ B} → g ⟶ g′ → (x : A ∈ _) → (!ᵛ g) x ⟶* (!ᵛ g′) x
    [!ᵛ⟶ g⟶ ] here refl = g⟶ ◅ ε
    [!ᵛ⟶ g⟶ ] there x   = ε

    infixr 7 qᵉˢ⟦_⟧_
    qᵉˢ⟦_⟧_ = qᵛ⟦_⟧_ ⦃ ExtVarSub ⦄ ⦃ SubVarSub ⦄

    [qᵉ⟦_⟧!ᵛ⟶_]_ : ∀ {g g′ : Ex Δ B} Ψ → g ⟶ g′ → (x : A ∈ _) → (qᵉˢ⟦ Ψ ⟧ (!ᵛ g)) x ⟶* (qᵉˢ⟦ Ψ ⟧ (!ᵛ g′)) x
    [qᵉ⟦ []    ⟧!ᵛ⟶ g⟶ ] x         = [!ᵛ⟶ g⟶ ] x
    [qᵉ⟦ _ ∷ Ψ ⟧!ᵛ⟶ g⟶ ] here refl = ε
    [qᵉ⟦ _ ∷ Ψ ⟧!ᵛ⟶ g⟶ ] there x   = ⟦ Wkᵛ ⟧ᵉ⟶* ([qᵉ⟦ Ψ ⟧!ᵛ⟶ g⟶ ] x) 

    ⟦qᵉ⟦_⟧!ᵛ⟶_⟧ˣ_ : ∀ {g g′ : Ex Δ B} Ψ → g ⟶ g′ → (e : Ex _ A) → ⟦ qᵉˢ⟦ Ψ ⟧ !ᵛ g ⟧ᵛ e ⟶* ⟦ qᵉˢ⟦ Ψ ⟧ !ᵛ g′ ⟧ᵛ e
    ⟦qᵉ⟦ Ψ ⟧!ᵛ⟶ g⟶ ⟧ˣ `# x       = [qᵉ⟦ Ψ ⟧!ᵛ⟶ g⟶ ] x
    ⟦qᵉ⟦ Ψ ⟧!ᵛ⟶ g⟶ ⟧ˣ (`λ e)     = ξ-of-⟶*′ _ `λ_ (⟦qᵉ⟦ _ ∷ Ψ ⟧!ᵛ⟶ g⟶ ⟧ˣ e)
    ⟦qᵉ⟦ Ψ ⟧!ᵛ⟶ g⟶ ⟧ˣ (`injₗ e)  = ξ-of-⟶*′ _ `injₗ (⟦qᵉ⟦ Ψ ⟧!ᵛ⟶ g⟶ ⟧ˣ e)
    ⟦qᵉ⟦ Ψ ⟧!ᵛ⟶ g⟶ ⟧ˣ (`injᵣ e)  = ξ-of-⟶*′ _ `injᵣ (⟦qᵉ⟦ Ψ ⟧!ᵛ⟶ g⟶ ⟧ˣ e)
    ⟦qᵉ⟦ Ψ ⟧!ᵛ⟶ g⟶ ⟧ˣ (e `∷ˢ ee) = ξ-of-⟶*′ _ _`∷ˢ? (⟦qᵉ⟦ Ψ ⟧!ᵛ⟶ g⟶ ⟧ˣ e) ◅◅ ξ-of-⟶* _ ?`∷ˢ_ (forExE ee)
      where
        forExE : (ee : ExE _ A B) →
                 RawAppSub.forExE (qᵉˢ⟦ Ψ ⟧ !ᵛ _) ee ⟶ᵉ* RawAppSub.forExE (qᵉˢ⟦ Ψ ⟧ !ᵛ _) ee
        forExE (-`$ e)              = Star.gmap _ -`$_ (⟦qᵉ⟦ Ψ ⟧!ᵛ⟶ g⟶ ⟧ˣ e)
        forExE (`case-`of eₗ `/ eᵣ) = Star.gmap _ `case-`of_`/? (⟦qᵉ⟦ _ ∷ Ψ ⟧!ᵛ⟶ g⟶ ⟧ˣ eₗ)
                                      ◅◅ Star.gmap _ `case-`of?`/_ (⟦qᵉ⟦ _ ∷ Ψ ⟧!ᵛ⟶ g⟶ ⟧ˣ eᵣ)

    ⟦!ᵛ⟶_⟧ˣ_ : ∀ {g g′ : Ex Δ B} → g ⟶ g′ → (e : Ex _ A) → ⟦ !ˢ g ⟧ᵛ e ⟶* ⟦ !ˢ g′ ⟧ᵛ e
    ⟦!ᵛ⟶_⟧ˣ_ = ⟦qᵉ⟦ [] ⟧!ᵛ⟶_⟧ˣ_

    ⟶*-cases : e ⟶* e′ → e ≡ e′ ⊎ e′ +⟵ e
    ⟶*-cases =
      flip (Star.foldl (_≡_ ∪ flip _+⟵_)) (inj₁ refl) λ where
        (inj₁ refl) e⟶ → inj₂ [ e⟶ ]
        (inj₂ e″⟶+) e⟶ → inj₂ (e⟶ ∷ e″⟶+)

open OpSem hiding (module Properties)
open OpSem.Properties

module AccessibilitySN where
  infix 4 _∈sn
  _∈sn : Pred (Ex Γ A) _
  _∈sn = Acc _⟵_

  infix 4 _∈sn+
  _∈sn+ : Pred (Ex Γ A) _
  _∈sn+ = Acc _+⟵_

  infix 4 _∈ne$
  data _∈ne$ : Pred (Ex Γ A) lzero where
    `#_  : (x : A ∈ Γ) →
           --------------
           `# x ∈ne$

    _`$- : e ∈ne$ →
           -----------------
           e `∷ˢ -`$ f ∈ne$

  infix 4 _⟶sn⟦_⟧_
  data _⟶sn⟦_⟧_ : Ex Γ A → ExEs Γ A B → Ex Γ A → Set where
    _`∷ˢ? : e ⟶sn⟦ ee `∷ es ⟧ e′ →
            -----------------------------
            e `∷ˢ ee ⟶sn⟦ es ⟧ e′ `∷ˢ ee

    `→β   : ∀ {e : Ex (A ∷ Γ) B}
              {f : Ex Γ A} →
            f ∈sn →
            ---------------------------------------
            (`λ e) `∷ˢ -`$ f ⟶sn⟦ es ⟧ ⟦ !ˢ f ⟧ᵛ e

    `+βₗ  : ∀ {e : Ex Γ A}
              {fₗ : Ex (A ∷ Γ) C} {fᵣ : Ex (B ∷ Γ) C} →
            e ∈sn →
            fᵣ `++ˢ ⟦ Wkᵛ ⟧ᵛ* es ∈sn →
            ------------------------------------------------------
            `injₗ e `∷ˢ `case-`of fₗ `/ fᵣ ⟶sn⟦ es ⟧ ⟦ !ˢ e ⟧ᵛ fₗ

    `+βᵣ  : ∀ {e : Ex Γ B}
              {fₗ : Ex (A ∷ Γ) C} {fᵣ : Ex (B ∷ Γ) C} →
            e ∈sn →
            fₗ `++ˢ ⟦ Wkᵛ ⟧ᵛ* es ∈sn →
            ------------------------------------------------------
            `injᵣ e `∷ˢ `case-`of fₗ `/ fᵣ ⟶sn⟦ es ⟧ ⟦ !ˢ e ⟧ᵛ fᵣ

    `+χ   : ∀ {e : Ex Γ (A `+ B)}
              {fₗ : Ex (A ∷ Γ) C} {fᵣ : Ex (B ∷ Γ) C}
              {ee : ExE Γ C D} →
            e ∈ne$ →
            --------------------------------------------------------------
            e `∷ˢ `case-`of fₗ `/ fᵣ `∷ˢ ee
              ⟶sn⟦ es ⟧ e `∷ˢ
                          `case-`of fₗ `∷ˢ RawAppSub.forExE Wkᵛ ee
                                 `/ (fᵣ `∷ˢ RawAppSub.forExE Wkᵛ ee)

  module Properties where
    ⟶*∧∈sn⇒∈sn : e ⟶* e′ → e ∈sn → e′ ∈sn
    ⟶*∧∈sn⇒∈sn = flip (Star.fold (Morphism on _∈sn)) id λ e⟶ ff esn → ff (acc-inverse esn e⟶)

    `#∈sn : (x : A ∈ Γ) → `# x ∈sn
    `#∈sn x∈ = acc λ ()

    `λ∈sn : e ∈sn → `λ e ∈sn
    `λ∈sn (acc Mrec) =
      acc λ where
        (`λ M⟶) → `λ∈sn (Mrec M⟶)

    `injₗ∈sn : e ∈sn → `injₗ {B = B} e ∈sn
    `injₗ∈sn (acc erec) =
      acc λ where
        (`injₗ e⟶) → `injₗ∈sn (erec e⟶)

    `injᵣ∈sn : e ∈sn → `injᵣ {A = A} e ∈sn
    `injᵣ∈sn (acc erec) =
      acc λ where
        (`injᵣ e⟶) → `injᵣ∈sn (erec e⟶)

    -- ⟦_⟧ᵛ∈sn : ∀ {M : Tm Γ A} (σ : Sub Δ Γ) → ⟦ σ ⟧ᵛ M ∈sn → M ∈sn
    -- ⟦ σ ⟧ᵛ∈sn (acc ⟦σ⟧Mrec) = acc λ M⟶ → ⟦ σ ⟧ᵛ∈sn (⟦σ⟧Mrec (⟦ σ ⟧ˢ⟶ M⟶))

    `λ∈sn-inv : `λ e ∈sn → e ∈sn
    `λ∈sn-inv (acc erec) = acc λ e⟶ → `λ∈sn-inv (erec (`λ e⟶))

    `injₗ∈sn-inv : `injₗ {B = B} e ∈sn → e ∈sn
    `injₗ∈sn-inv (acc erec) = acc λ e⟶ → `injₗ∈sn-inv (erec (`injₗ e⟶))

    `injᵣ∈sn-inv : `injᵣ {A = A} e ∈sn → e ∈sn
    `injᵣ∈sn-inv (acc erec) = acc λ e⟶ → `injᵣ∈sn-inv (erec (`injᵣ e⟶))

    `∷ˢ∈sn-invˡ : e `∷ˢ ee ∈sn → e ∈sn
    `∷ˢ∈sn-invˡ (acc erec) = acc λ e⟶ → `∷ˢ∈sn-invˡ (erec (e⟶ `∷ˢ?))

    -- `$∈sn-invˡ : M `$ N ∈sn → M ∈sn
    -- `$∈sn-invˡ (acc MNrec) = acc λ M⟶ → `$∈sn-invˡ (MNrec (M⟶ `$?))

    -- `$∈sn-invʳ : M `$ N ∈sn → N ∈sn
    -- `$∈sn-invʳ (acc MNrec) = acc λ N⟶ → `$∈sn-invʳ (MNrec (?`$ N⟶))

    -- `case-`of-`/∈sn-invˢ : `case M `of Nₗ `/ Nᵣ ∈sn → M ∈sn
    -- `case-`of-`/∈sn-invˢ (acc MNₗNᵣrec) = acc λ M⟶ → `case-`of-`/∈sn-invˢ (MNₗNᵣrec (`case M⟶ `of?`/?))

    -- `case-`of-`/∈sn-invˡ : `case M `of Nₗ `/ Nᵣ ∈sn → Nₗ ∈sn
    -- `case-`of-`/∈sn-invˡ (acc MNₗNᵣrec) = acc λ Nₗ⟶ → `case-`of-`/∈sn-invˡ (MNₗNᵣrec (`case?`of Nₗ⟶ `/?))

    -- `case-`of-`/∈sn-invʳ : `case M `of Nₗ `/ Nᵣ ∈sn → Nᵣ ∈sn
    -- `case-`of-`/∈sn-invʳ (acc MNₗNᵣrec) = acc λ Nᵣ⟶ → `case-`of-`/∈sn-invʳ (MNₗNᵣrec (`case?`of?`/ Nᵣ⟶))

    _`++ˢ?⟶ : e ⟶ e′ →
               e `++ˢ es ⟶ e′ `++ˢ es
    _`++ˢ?⟶ {es = `[]}     e⟶ = e⟶
    _`++ˢ?⟶ {es = _ `∷ˢ _} e⟶ = (e⟶ `++ˢ?⟶) `∷ˢ?

    data `→β-case : Ex (A ∷ Γ) B → Ex Γ A → ExEs Γ B C → Ex Γ C → Set where
      e-step  : e ⟶ e′ →
                --------------------------------------------
                `→β-case e f es ((`λ e′) `∷ˢ -`$ f `++ˢ es)

      f-step  : f ⟶ f′ →
                --------------------------------------------
                `→β-case e f es ((`λ e) `∷ˢ -`$ f′ `++ˢ es)

      `→β     : ∀ {e : Ex (A ∷ Γ) B} {f : Ex Γ A} {es : ExEs Γ B C} →
                ------------------------------------------------------
                `→β-case e f es (⟦ !ˢ f ⟧ᵛ e `++ˢ es)

      es-step : ∀ {e : Ex (A ∷ Γ) B} {f : Ex Γ A} {es es′ : ExEs Γ B C} →
                ⟦ !ˢ f ⟧ᵛ e `++ˢ es ⟶ ⟦ !ˢ f ⟧ᵛ e `++ˢ es′ →
                ----------------------------------------------------------
                `→β-case e f es ((`λ e) `∷ˢ (-`$ f) `++ˢ es′)

    `→β-cases : ∀ (e : Ex (A ∷ Γ) B) (f : Ex Γ A) (es : ExEs Γ B C) {efes′} →
                (`λ e) `∷ˢ -`$ f `++ˢ es ⟶ efes′ →
                `→β-case e f es efes′
    `→β-cases e f `[]             ((`λ e⟶) `∷ˢ?)         = e-step e⟶
    `→β-cases e f `[]             (       ?`∷ˢ (-`$ f⟶)) = f-step f⟶
    `→β-cases e f `[]             `→β                    = `→β
    `→β-cases e f (_ `∷ˢ _ `∷ˢ _) `+χ                    = es-step `+χ
    `→β-cases e f (_       `∷ˢ _) (efes⟶ `∷ˢ?)
      with `→β-cases e f _ efes⟶
    ...  | e-step e⟶                                     = e-step e⟶
    ...  | f-step f⟶                                     = f-step f⟶
    ...  | `→β                                           = `→β
    ...  | es-step ⟦f⟧ees⟶                               = es-step (⟦f⟧ees⟶ `∷ˢ?)
    `→β-cases e f (_       `∷ˢ _) (?`∷ˢ ee⟶)             = es-step (?`∷ˢ ee⟶)

    ∈sn-weak-head-expansion`→ : ∀ {e : Ex (A ∷ Γ) B} {f : Ex Γ A} (es : ExEs Γ B C) →
                                f ∈sn →
                                ⟦ !ˢ f ⟧ᵛ e `++ˢ es ∈sn →
                                (`λ e) `∷ˢ -`$ f `++ˢ es ∈sn
    ∈sn-weak-head-expansion`→ = λ es fsn ⟦f⟧esn → acc (go es fsn (TC.accessible _⟵_ ⟦f⟧esn))
      where
        open Function.Equivalence
        module TC = Relation.Binary.Construct.Closure.Transitive

        go : ∀ es →
             f ∈sn →
             ⟦ !ˢ f ⟧ᵛ e `++ˢ es ∈sn+ →
             Induction.WellFounded.WfRec _⟵_ (Acc _⟵_) ((`λ e) `∷ˢ -`$ f `++ˢ es)
        go es (acc frec) (acc ⟦f⟧eesrec) efes⟶
          with `→β-cases _ _ _ efes⟶
        ...  | es-step ⟦f⟧ees⟶                 = acc (go _ (acc frec) (⟦f⟧eesrec [ ⟦f⟧ees⟶ ]))
        ...  | `→β                             = TC.accessible⁻ _⟵_ (acc ⟦f⟧eesrec)
        ...  | e-step e⟶                       = acc (go _ (acc frec) (⟦f⟧eesrec [ (⟦ !ᵛ _ ⟧ᵛ⟶ e⟶) `++ˢ?⟶ ]))
        ...  | f-step {e = e} f⟶
            with ⟶*-cases (⟦!ᵛ⟶ f⟶ ⟧ˣ e)
        ...    | inj₁ eq″
              rewrite eq″                      = acc (go _ (frec f⟶) (acc ⟦f⟧eesrec))
        ...    | inj₂ ⟦f⟧e⟶+                   = acc (go _ (frec f⟶) (⟦f⟧eesrec (TC.equivalent .to (TC.map (_`++ˢ?⟶ {es = es}) (TC.equivalent .from ⟦f⟧e⟶+)))))

    data `+βₗ-case : Ex Γ A → Ex (A ∷ Γ) C → Ex (B ∷ Γ) C → ExEs Γ C D → Ex Γ D → Set where
      e-step  : e ⟶ e′ →
                -----------------------------------------------------------------
                `+βₗ-case e fₗ fᵣ es ((`injₗ e′) `∷ˢ `case-`of fₗ `/ fᵣ `++ˢ es)

      fₗ-step : fₗ ⟶ f′ₗ →
                -----------------------------------------------------------------
                `+βₗ-case e fₗ fᵣ es ((`injₗ e) `∷ˢ `case-`of f′ₗ `/ fᵣ `++ˢ es)

      fᵣ-step : fᵣ ⟶ f′ᵣ →
                -----------------------------------------------------------------
                `+βₗ-case e fₗ fᵣ es ((`injₗ e) `∷ˢ `case-`of fₗ `/ f′ᵣ `++ˢ es)

      `+βₗ    : ∀ {e : Ex Γ A} {fₗ : Ex (A ∷ Γ) C} {fᵣ : Ex (B ∷ Γ) C}
                  {es : ExEs Γ C D} →
                -------------------------------------------------------
                `+βₗ-case e fₗ fᵣ es (⟦ !ˢ e ⟧ᵛ fₗ `++ˢ es)

      es-step : ∀ {e : Ex Γ A} {fₗ : Ex (A ∷ Γ) C} {fᵣ : Ex (B ∷ Γ) C}
                  {es es′ : ExEs Γ C D} →
                lengthˢ es′ ≤‴ lengthˢ es →
                ⟦ !ˢ e ⟧ᵛ fₗ `++ˢ es ⟶ ⟦ !ˢ e ⟧ᵛ fₗ `++ˢ es′ →
                fᵣ `++ˢ ⟦ Wkᵛ ⟧ᵛ* es ⟶ fᵣ `++ˢ ⟦ Wkᵛ ⟧ᵛ* es′ →
                -----------------------------------------------------------------
                `+βₗ-case e fₗ fᵣ es ((`injₗ e) `∷ˢ `case-`of fₗ `/ fᵣ `++ˢ es′)

      `+χ     : ∀ {e : Ex Γ A} {fₗ : Ex (A ∷ Γ) C} {fᵣ : Ex (B ∷ Γ) C}
                  {es : ExEs Γ C D} {ee′ : ExE Γ C C′} (es′ : ExEs Γ C′ D) →
                es ≡ ee′ `∷ es′ →
                -------------------------------------------------------------
                `+βₗ-case e fₗ fᵣ es
                  ((`injₗ e) `∷ˢ `case-`of (fₗ `∷ˢ RawAppSub.forExE Wkᵛ ee′)
                                        `/ (fᵣ `∷ˢ RawAppSub.forExE Wkᵛ ee′)
                             `++ˢ es′)

    `+βₗ-cases : ∀ (e : Ex Γ A) (fₗ : Ex (A ∷ Γ) C) (fᵣ : Ex (B ∷ Γ) C) (es : ExEs Γ C D) {efₗfᵣes′} →
                 (`injₗ e) `∷ˢ `case-`of fₗ `/ fᵣ `++ˢ es ⟶ efₗfᵣes′ →
                 `+βₗ-case e fₗ fᵣ es efₗfᵣes′
    `+βₗ-cases e fₗ fᵣ `[]             (`injₗ e⟶ `∷ˢ?)                   = e-step e⟶
    `+βₗ-cases e fₗ fᵣ `[]             (        ?`∷ˢ `case-`of fₗ⟶ `/?)  = fₗ-step fₗ⟶
    `+βₗ-cases e fₗ fᵣ `[]             (        ?`∷ˢ (`case-`of?`/ fᵣ⟶)) = fᵣ-step fᵣ⟶
    `+βₗ-cases e fₗ fᵣ `[]             `+βₗ                              = `+βₗ
    `+βₗ-cases e fₗ fᵣ (`[]     `∷ˢ _) `+χ                               = `+χ `[] refl
    `+βₗ-cases e fₗ fᵣ (_ `∷ˢ _ `∷ˢ _) `+χ                               = es-step (≤‴-step ≤‴-refl) `+χ `+χ′
      where
        `+χ′ = subst₂
               (λ x y → fᵣ `++ˢ _ `∷ˢ `case-`of _ `/ _ `∷ˢ _ ⟶ fᵣ `++ˢ _ `∷ˢ `case-`of (_ `∷ˢ x) `/ (_ `∷ˢ y))
               (sym (forExE-qᵉᵉ-forExE-Wkᵛ≡forExE-Wkᵛ-forExE Wkᵛ _))
               (sym (forExE-qᵉᵉ-forExE-Wkᵛ≡forExE-Wkᵛ-forExE Wkᵛ _))
               `+χ
    `+βₗ-cases e fₗ fᵣ (es      `∷ˢ _) (efₗfᵣes⟶ `∷ˢ?)
      with `+βₗ-cases e fₗ fᵣ es efₗfᵣes⟶
    ...  | e-step e⟶                                                     = e-step e⟶
    ...  | fₗ-step fₗ⟶                                                   = fₗ-step fₗ⟶
    ...  | fᵣ-step fᵣ⟶                                                   = fᵣ-step fᵣ⟶
    ...  | `+βₗ                                                          = `+βₗ
    ...  | es-step ≤es ⟦e⟧fₗes⟶ fᵣes⟶                                    = es-step (ℕ.≤⇒≤‴ (s≤s (ℕ.≤‴⇒≤ ≤es))) (⟦e⟧fₗes⟶ `∷ˢ?) (fᵣes⟶ `∷ˢ?)
    ...  | `+χ _ refl                                                    = `+χ (_ `∷ˢ _) refl
    `+βₗ-cases e fₗ fᵣ (_       `∷ˢ _) (        ?`∷ˢ ee⟶)                = es-step ≤‴-refl (?`∷ˢ ee⟶) (?`∷ˢ ⟦_⟧ᵉ⟶_.forExE Wkᵛ ee⟶)

    ∈sn-weak-head-expansion`+ₗ : ∀ {e : Ex Γ A} {fₗ : Ex (A ∷ Γ) C} {fᵣ : Ex (B ∷ Γ) C} (es : ExEs Γ C D) →
                                 e ∈sn →
                                 fᵣ `++ˢ ⟦ Wkᵛ ⟧ᵛ* es ∈sn →
                                 ⟦ !ˢ e ⟧ᵛ fₗ `++ˢ es ∈sn →
                                 `injₗ e `∷ˢ `case-`of fₗ `/ fᵣ `++ˢ es ∈sn
    ∈sn-weak-head-expansion`+ₗ = λ es esn fᵣessn ⟦e⟧fₗessn → acc (go es (<-wellFounded _) esn fᵣessn (TC.accessible _⟵_ ⟦e⟧fₗessn))
      where
        open Function.Equivalence
        module TC = Relation.Binary.Construct.Closure.Transitive

        go : ∀ {e : Ex Γ A} {fₗ : Ex (A ∷ Γ) C} {fᵣ : Ex (B ∷ Γ) C} (es : ExEs Γ C D) →
             Acc _<_ (lengthˢ es) →
             e ∈sn →
             fᵣ `++ˢ ⟦ Wkᵛ ⦃ ExtVarSub ⦄ ⟧ᵛ* es ∈sn →
             ⟦ !ˢ e ⟧ᵛ fₗ `++ˢ es ∈sn+ →
             Induction.WellFounded.WfRec _⟵_ (Acc _⟵_) (`injₗ e `∷ˢ `case-`of fₗ `/ fᵣ `++ˢ es)
        go es (acc esrec) (acc erec) (acc fᵣesrec) (acc ⟦e⟧fₗesrec) efₗfᵣes⟶
          with `+βₗ-cases _ _ _ _ efₗfᵣes⟶
        ...  | `+χ {B = B} {e = e} {fₗ = fₗ} {fᵣ = fᵣ} {ee′ = ee′} es′ refl
            rewrite `∷-⟦-⟧ᵛ*-commute (Wkᵛ {A = B}) ee′ es′
                  | sym (`∷ˢ-`++ˢ-commute fᵣ (RawAppSub.forExE Wkᵛ ee′) (⟦ Wkᵛ ⟧ᵛ* es′))
                  | sym (`∷ˢ-`++ˢ-commute (⟦ !ˢ e ⟧ᵛ fₗ) ee′ es′)
                  | cong ((ExE _ _ _ → Ex _ _) ∋ ⟦ !ˢ e ⟧ᵛ fₗ `∷ˢ_) (sym (trans (SubAppExtCompositionalSub.forExE (!ˢ e) Wkᵛ ee′) (trans (ExtLiftSubApp.forExE Idᵛ ee′) (ExtIdNoOpSubˡ.forExE ee′))))
                  | `∷-lengthˢ ee′ es′                                       = acc (go es′ (esrec ℕ.≤-refl) (acc erec) (acc fᵣesrec) (acc ⟦e⟧fₗesrec))
        ...  | es-step (≤‴-reflexive eq) ⟦e⟧fₗes⟶ fᵣes⟶
          rewrite sym eq                                                     = acc (go _ (acc esrec) (acc erec) (fᵣesrec fᵣes⟶) (⟦e⟧fₗesrec [ ⟦e⟧fₗes⟶ ]))
        ...  | es-step (≤‴-step <es)     ⟦e⟧fₗes⟶ fᵣes⟶                      = acc (go _ (esrec (ℕ.≤‴⇒≤ <es)) (acc erec) (fᵣesrec fᵣes⟶) (⟦e⟧fₗesrec [ ⟦e⟧fₗes⟶ ]))
        ...  | `+βₗ                                                          = TC.accessible⁻ _⟵_ (acc ⟦e⟧fₗesrec)
        ...  | fᵣ-step fᵣ⟶                                                   = acc (go _ (acc esrec) (acc erec) (fᵣesrec (fᵣ⟶ `++ˢ?⟶)) (acc ⟦e⟧fₗesrec))
        ...  | fₗ-step fₗ⟶                                                   = acc (go _ (acc esrec) (acc erec) (acc fᵣesrec) (⟦e⟧fₗesrec [ (⟦ !ᵛ _ ⟧ᵛ⟶ fₗ⟶) `++ˢ?⟶ ]))
        ...  | e-step {fₗ = fₗ} e⟶
            with ⟶*-cases (⟦!ᵛ⟶ e⟶ ⟧ˣ fₗ)
        ...    | inj₁ eq″
              rewrite eq″                                                    = acc (go _ (acc esrec) (erec e⟶) (acc fᵣesrec) (acc ⟦e⟧fₗesrec))
        ...    | inj₂ ⟦e⟧fₗ⟶+                                                = acc (go _ (acc esrec) (erec e⟶) (acc fᵣesrec) (⟦e⟧fₗesrec (TC.equivalent .to (TC.map (_`++ˢ?⟶ {es = es}) (TC.equivalent .from ⟦e⟧fₗ⟶+)))))

    data `+βᵣ-case : Ex Γ B → Ex (A ∷ Γ) C → Ex (B ∷ Γ) C → ExEs Γ C D → Ex Γ D → Set where
      e-step  : e ⟶ e′ →
                -----------------------------------------------------------------
                `+βᵣ-case e fₗ fᵣ es ((`injᵣ e′) `∷ˢ `case-`of fₗ `/ fᵣ `++ˢ es)

      fₗ-step : fₗ ⟶ f′ₗ →
                -----------------------------------------------------------------
                `+βᵣ-case e fₗ fᵣ es ((`injᵣ e) `∷ˢ `case-`of f′ₗ `/ fᵣ `++ˢ es)

      fᵣ-step : fᵣ ⟶ f′ᵣ →
                -----------------------------------------------------------------
                `+βᵣ-case e fₗ fᵣ es ((`injᵣ e) `∷ˢ `case-`of fₗ `/ f′ᵣ `++ˢ es)

      `+βᵣ    : ∀ {e : Ex Γ B} {fₗ : Ex (A ∷ Γ) C} {fᵣ : Ex (B ∷ Γ) C}
                  {es : ExEs Γ C D} →
                -------------------------------------------------------
                `+βᵣ-case e fₗ fᵣ es (⟦ !ˢ e ⟧ᵛ fᵣ `++ˢ es)

      es-step : ∀ {e : Ex Γ B} {fₗ : Ex (A ∷ Γ) C} {fᵣ : Ex (B ∷ Γ) C}
                  {es es′ : ExEs Γ C D} →
                lengthˢ es′ ≤‴ lengthˢ es →
                ⟦ !ˢ e ⟧ᵛ fᵣ `++ˢ es ⟶ ⟦ !ˢ e ⟧ᵛ fᵣ `++ˢ es′ →
                fₗ `++ˢ ⟦ Wkᵛ ⟧ᵛ* es ⟶ fₗ `++ˢ ⟦ Wkᵛ ⟧ᵛ* es′ →
                -----------------------------------------------------------------
                `+βᵣ-case e fₗ fᵣ es ((`injᵣ e) `∷ˢ `case-`of fₗ `/ fᵣ `++ˢ es′)

      `+χ     : ∀ {e : Ex Γ B} {fₗ : Ex (A ∷ Γ) C} {fᵣ : Ex (B ∷ Γ) C}
                  {es : ExEs Γ C D} {ee′ : ExE Γ C C′} (es′ : ExEs Γ C′ D) →
                es ≡ ee′ `∷ es′ →
                -------------------------------------------------------------
                `+βᵣ-case e fₗ fᵣ es
                  ((`injᵣ e) `∷ˢ `case-`of (fₗ `∷ˢ RawAppSub.forExE Wkᵛ ee′)
                                        `/ (fᵣ `∷ˢ RawAppSub.forExE Wkᵛ ee′)
                             `++ˢ es′)

    `+βᵣ-cases : ∀ (e : Ex Γ B) (fₗ : Ex (A ∷ Γ) C) (fᵣ : Ex (B ∷ Γ) C) (es : ExEs Γ C D) {efₗfᵣes′} →
                 (`injᵣ e) `∷ˢ `case-`of fₗ `/ fᵣ `++ˢ es ⟶ efₗfᵣes′ →
                 `+βᵣ-case e fₗ fᵣ es efₗfᵣes′
    `+βᵣ-cases e fₗ fᵣ `[]             (`injᵣ e⟶ `∷ˢ?)                   = e-step e⟶
    `+βᵣ-cases e fₗ fᵣ `[]             (        ?`∷ˢ `case-`of fₗ⟶ `/?)  = fₗ-step fₗ⟶
    `+βᵣ-cases e fₗ fᵣ `[]             (        ?`∷ˢ (`case-`of?`/ fᵣ⟶)) = fᵣ-step fᵣ⟶
    `+βᵣ-cases e fₗ fᵣ `[]             `+βᵣ                              = `+βᵣ
    `+βᵣ-cases e fₗ fᵣ (`[]     `∷ˢ _) `+χ                               = `+χ `[] refl
    `+βᵣ-cases e fₗ fᵣ (_ `∷ˢ _ `∷ˢ _) `+χ                               = es-step (≤‴-step ≤‴-refl) `+χ `+χ′
      where
        `+χ′ = subst₂
               (λ x y → fₗ `++ˢ _ `∷ˢ `case-`of _ `/ _ `∷ˢ _ ⟶ fₗ `++ˢ _ `∷ˢ `case-`of (_ `∷ˢ x) `/ (_ `∷ˢ y))
               (sym (forExE-qᵉᵉ-forExE-Wkᵛ≡forExE-Wkᵛ-forExE Wkᵛ _))
               (sym (forExE-qᵉᵉ-forExE-Wkᵛ≡forExE-Wkᵛ-forExE Wkᵛ _))
               `+χ
    `+βᵣ-cases e fₗ fᵣ (es      `∷ˢ _) (efₗfᵣes⟶ `∷ˢ?)
      with `+βᵣ-cases e fₗ fᵣ es efₗfᵣes⟶
    ...  | e-step e⟶                                                     = e-step e⟶
    ...  | fₗ-step fₗ⟶                                                   = fₗ-step fₗ⟶
    ...  | fᵣ-step fᵣ⟶                                                   = fᵣ-step fᵣ⟶
    ...  | `+βᵣ                                                          = `+βᵣ
    ...  | es-step ≤es ⟦e⟧fᵣes⟶ fₗes⟶                                    = es-step (ℕ.≤⇒≤‴ (s≤s (ℕ.≤‴⇒≤ ≤es))) (⟦e⟧fᵣes⟶ `∷ˢ?) (fₗes⟶ `∷ˢ?)
    ...  | `+χ _ refl                                                    = `+χ (_ `∷ˢ _) refl
    `+βᵣ-cases e fₗ fᵣ (_       `∷ˢ _) (        ?`∷ˢ ee⟶)                = es-step ≤‴-refl (?`∷ˢ ee⟶) (?`∷ˢ ⟦_⟧ᵉ⟶_.forExE Wkᵛ ee⟶)

    ∈sn-weak-head-expansion`+ᵣ : ∀ {e : Ex Γ B} {fₗ : Ex (A ∷ Γ) C} {fᵣ : Ex (B ∷ Γ) C} (es : ExEs Γ C D) →
                                 e ∈sn →
                                 fₗ `++ˢ ⟦ Wkᵛ ⟧ᵛ* es ∈sn →
                                 ⟦ !ˢ e ⟧ᵛ fᵣ `++ˢ es ∈sn →
                                 `injᵣ e `∷ˢ `case-`of fₗ `/ fᵣ `++ˢ es ∈sn
    ∈sn-weak-head-expansion`+ᵣ = λ es esn fₗessn ⟦e⟧fᵣessn → acc (go es (<-wellFounded _) esn fₗessn (TC.accessible _⟵_ ⟦e⟧fᵣessn))
      where
        open Function.Equivalence
        module TC = Relation.Binary.Construct.Closure.Transitive

        go : ∀ {e : Ex Γ B} {fₗ : Ex (A ∷ Γ) C} {fᵣ : Ex (B ∷ Γ) C} (es : ExEs Γ C D) →
             Acc _<_ (lengthˢ es) →
             e ∈sn →
             fₗ `++ˢ ⟦ Wkᵛ ⟧ᵛ* es ∈sn →
             ⟦ !ˢ e ⟧ᵛ fᵣ `++ˢ es ∈sn+ →
             Induction.WellFounded.WfRec _⟵_ (Acc _⟵_) (`injᵣ e `∷ˢ `case-`of fₗ `/ fᵣ `++ˢ es)
        go es (acc esrec) (acc erec) (acc fₗesrec) (acc ⟦e⟧fᵣesrec) efₗfᵣes⟶
          with `+βᵣ-cases _ _ _ _ efₗfᵣes⟶
        ...  | `+χ {A = A} {e = e} {fₗ = fₗ} {fᵣ = fᵣ} {ee′ = ee′} es′ refl
            rewrite `∷-⟦-⟧ᵛ*-commute (Wkᵛ {A = A}) ee′ es′
                  | sym (`∷ˢ-`++ˢ-commute fₗ (RawAppSub.forExE Wkᵛ ee′) (⟦ Wkᵛ ⟧ᵛ* es′))
                  | sym (`∷ˢ-`++ˢ-commute (⟦ !ˢ e ⟧ᵛ fᵣ) ee′ es′)
                  | cong ((ExE _ _ _ → Ex _ _) ∋ ⟦ !ˢ e ⟧ᵛ fᵣ `∷ˢ_) (sym (trans (SubAppExtCompositionalSub.forExE (!ˢ e) Wkᵛ ee′) (trans (ExtLiftSubApp.forExE Idᵛ ee′) (ExtIdNoOpSubˡ.forExE ee′))))
                  | `∷-lengthˢ ee′ es′                                       = acc (go es′ (esrec ℕ.≤-refl) (acc erec) (acc fₗesrec) (acc ⟦e⟧fᵣesrec))
        ...  | es-step (≤‴-reflexive eq) ⟦e⟧fₗes⟶ fᵣes⟶
          rewrite sym eq                                                     = acc (go _ (acc esrec) (acc erec) (fₗesrec fᵣes⟶) (⟦e⟧fᵣesrec [ ⟦e⟧fₗes⟶ ]))
        ...  | es-step (≤‴-step <es)     ⟦e⟧fₗes⟶ fᵣes⟶                      = acc (go _ (esrec (ℕ.≤‴⇒≤ <es)) (acc erec) (fₗesrec fᵣes⟶) (⟦e⟧fᵣesrec [ ⟦e⟧fₗes⟶ ]))
        ...  | `+βᵣ                                                          = TC.accessible⁻ _⟵_ (acc ⟦e⟧fᵣesrec)
        ...  | fᵣ-step fᵣ⟶                                                   = acc (go _ (acc esrec) (acc erec) (acc fₗesrec) (⟦e⟧fᵣesrec [ (⟦ !ᵛ _ ⟧ᵛ⟶ fᵣ⟶) `++ˢ?⟶ ]))
        ...  | fₗ-step fₗ⟶                                                   = acc (go _ (acc esrec) (acc erec) (fₗesrec (fₗ⟶ `++ˢ?⟶)) (acc ⟦e⟧fᵣesrec))
        ...  | e-step {fᵣ = fᵣ} e⟶
            with ⟶*-cases (⟦!ᵛ⟶ e⟶ ⟧ˣ fᵣ)
        ...    | inj₁ eq″
              rewrite eq″                                                    = acc (go _ (acc esrec) (erec e⟶) (acc fₗesrec) (acc ⟦e⟧fᵣesrec))
        ...    | inj₂ ⟦e⟧fₗ⟶+                                                = acc (go _ (acc esrec) (erec e⟶) (acc fₗesrec) (⟦e⟧fᵣesrec (TC.equivalent .to (TC.map (_`++ˢ?⟶ {es = es}) (TC.equivalent .from ⟦e⟧fₗ⟶+)))))

    ∈ne$-closed : e ∈ne$ → e ⟶ e′ → e′ ∈ne$
    ∈ne$-closed (ene$ `$-) (e⟶ `∷ˢ?)      = ∈ne$-closed ene$ e⟶ `$-
    ∈ne$-closed (ene$ `$-) (?`∷ˢ (-`$ _)) = ene$ `$-

    data `+χ-case : Ex Γ (A `+ B) → Ex (A ∷ Γ) C → Ex (B ∷ Γ) C → ExE Γ C D → ExEs Γ D E → Ex Γ E → Set where
      e-step  : e ⟶ e′ →
                ------------------------------------------------------------------
                `+χ-case e fₗ fᵣ ee es (e′ `∷ˢ `case-`of fₗ `/ fᵣ `∷ˢ ee `++ˢ es)

      fₗ-step : fₗ ⟶ f′ₗ →
                ------------------------------------------------------------------
                `+χ-case e fₗ fᵣ ee es (e `∷ˢ `case-`of f′ₗ `/ fᵣ `∷ˢ ee `++ˢ es)

      fᵣ-step : fᵣ ⟶ f′ᵣ →
                ------------------------------------------------------------------
                `+χ-case e fₗ fᵣ ee es (e `∷ˢ `case-`of fₗ `/ f′ᵣ `∷ˢ ee `++ˢ es)

      ee-step : ee ⟶ᵉ ee′ →
                ------------------------------------------------------------------
                `+χ-case e fₗ fᵣ ee es (e `∷ˢ `case-`of fₗ `/ fᵣ `∷ˢ ee′ `++ˢ es)

      `+χ-ee  : ∀ {e : Ex Γ (A `+ B)} {fₗ : Ex (A ∷ Γ) C} {fᵣ : Ex (B ∷ Γ) C}
                  {ee : ExE Γ C D} {es : ExEs Γ D E} →
                ----------------------------------------------------------------
                `+χ-case e fₗ fᵣ ee es
                  (e `∷ˢ `case-`of (fₗ `∷ˢ RawAppSub.forExE Wkᵛ ee)
                                `/ (fᵣ `∷ˢ RawAppSub.forExE Wkᵛ ee)
                     `++ˢ es)

      `+χ-es  : ∀ {e : Ex Γ (A `+ B)} {fₗ : Ex (A ∷ Γ) (C `+ D)} {fᵣ : Ex (B ∷ Γ) (C `+ D)}
                  {gₗ : Ex (C ∷ Γ) E} {gᵣ : Ex (D ∷ Γ) E}
                  {es : ExEs Γ E F} {ee′ : ExE Γ E E′} (es′ : ExEs Γ E′ F) →
                es ≡ ee′ `∷ es′ →
                ----------------------------------------------------------------------------
                `+χ-case e fₗ fᵣ (`case-`of gₗ `/ gᵣ) es
                  (e `∷ˢ `case-`of fₗ `/ fᵣ
                     `∷ˢ `case-`of (gₗ `∷ˢ RawAppSub.forExE Wkᵛ ee′)
                                `/ (gᵣ `∷ˢ RawAppSub.forExE Wkᵛ ee′)
                     `++ˢ es′)

      es-step : ∀ {e : Ex Γ (A `+ B)} {fₗ : Ex (A ∷ Γ) C} {fᵣ : Ex (B ∷ Γ) C}
                  {ee : ExE Γ C D} {es es′ : ExEs Γ D E} →
                lengthˢ es′ ≤‴ lengthˢ es →
                e `∷ˢ `case-`of (fₗ `∷ˢ RawAppSub.forExE Wkᵛ ee)
                             `/ (fᵣ `∷ˢ RawAppSub.forExE Wkᵛ ee) `++ˢ es
                  ⟶ e `∷ˢ `case-`of (fₗ `∷ˢ RawAppSub.forExE Wkᵛ ee)
                                 `/ (fᵣ `∷ˢ RawAppSub.forExE Wkᵛ ee) `++ˢ es′ →
                --------------------------------------------------------------------------------
                `+χ-case e fₗ fᵣ ee es (e `∷ˢ `case-`of fₗ `/ fᵣ `∷ˢ ee `++ˢ es′)

    `+χ-cases : ∀ (e : Ex Γ (A `+ B)) (fₗ : Ex (A ∷ Γ) C) (fᵣ : Ex (B ∷ Γ) C)
                  (ee : ExE Γ C D) (es : ExEs Γ D E) {efₗfᵣeees′} →
                e ∈ne$ →
                e `∷ˢ `case-`of fₗ `/ fᵣ `∷ˢ ee `++ˢ es ⟶ efₗfᵣeees′ →
                `+χ-case e fₗ fᵣ ee es efₗfᵣeees′
    `+χ-cases e fₗ fᵣ ee `[]             ene$ ((e⟶ `∷ˢ?)                   `∷ˢ?)    = e-step e⟶
    `+χ-cases e fₗ fᵣ ee `[]             ene$ ((  ?`∷ˢ `case-`of fₗ⟶ `/?)  `∷ˢ?)    = fₗ-step fₗ⟶
    `+χ-cases e fₗ fᵣ ee `[]             ene$ ((  ?`∷ˢ (`case-`of?`/ fᵣ⟶)) `∷ˢ?)    = fᵣ-step fᵣ⟶
    `+χ-cases e fₗ fᵣ ee `[]             ene$ (                           ?`∷ˢ ee⟶) = ee-step ee⟶
    `+χ-cases e fₗ fᵣ ee `[]             ene$ `+χ                                   = `+χ-ee
    `+χ-cases e fₗ fᵣ ee (`[]     `∷ˢ _) ene$ `+χ                                   = `+χ-es `[] refl
    `+χ-cases e fₗ fᵣ ee (_ `∷ˢ _ `∷ˢ _) ene$ `+χ                                   = es-step (≤‴-step ≤‴-refl) `+χ
    `+χ-cases e fₗ fᵣ ee (es      `∷ˢ _) ene$ (e⟶ `∷ˢ?)
      with `+χ-cases e fₗ fᵣ ee es ene$ e⟶
    ...  | e-step e⟶                                                                = e-step e⟶
    ...  | fₗ-step fₗ⟶                                                              = fₗ-step fₗ⟶
    ...  | fᵣ-step fᵣ⟶                                                              = fᵣ-step fᵣ⟶
    ...  | ee-step ee⟶                                                              = ee-step ee⟶
    ...  | `+χ-ee                                                                   = `+χ-ee
    ...  | `+χ-es es′ refl                                                          = `+χ-es (_ `∷ˢ _) refl
    ...  | es-step ≤es efₗeefᵣeees⟶                                                 = es-step (ℕ.≤⇒≤‴ (s≤s (ℕ.≤‴⇒≤ ≤es))) (efₗeefᵣeees⟶ `∷ˢ?)
    `+χ-cases e fₗ fᵣ ee (_       `∷ˢ _) ene$ (?`∷ˢ ee⟶)                            = es-step ≤‴-refl (?`∷ˢ ee⟶)

    ∈sn-commuting-expansion : ∀ {e : Ex Γ (A `+ B)} {fₗ : Ex (A ∷ Γ) C} {fᵣ : Ex (B ∷ Γ) C}
                                (ee : ExE Γ C D) (es : ExEs Γ D E) →
                              e ∈ne$ →
                              e `∷ˢ `case-`of (fₗ `∷ˢ RawAppSub.forExE Wkᵛ ee)
                                           `/ (fᵣ `∷ˢ RawAppSub.forExE Wkᵛ ee)
                                `++ˢ es ∈sn →
                              -----------------------------------------------------------------
                              e `∷ˢ `case-`of fₗ `/ fᵣ `∷ˢ ee `++ˢ es ∈sn
    ∈sn-commuting-expansion = λ ee es ene$ efₗeefᵣeesn → acc (go ee es ene$ (<-wellFounded _) (TransClosure.accessible _⟵_ efₗeefᵣeesn))
      where
        open Function.Equivalence
        module TC = Relation.Binary.Construct.Closure.Transitive

        go : ∀ {e : Ex Γ (A `+ B)} {fₗ : Ex (A ∷ Γ) C} {fᵣ : Ex (B ∷ Γ) C} (ee : ExE Γ C D) (es : ExEs Γ D E) →
             e ∈ne$ →
             Acc _<_ (lengthˢ es) →
             e `∷ˢ `case-`of (fₗ `∷ˢ RawAppSub.forExE Wkᵛ ee) `/ (fᵣ `∷ˢ RawAppSub.forExE Wkᵛ ee) `++ˢ es ∈sn+ →
             Induction.WellFounded.WfRec _⟵_ (Acc _⟵_) (e `∷ˢ `case-`of fₗ `/ fᵣ `∷ˢ ee `++ˢ es)
        go ee es ene$ (acc esrec) (acc efₗeefᵣeerec) efₗfᵣeees⟶
          with `+χ-cases _ _ _ _ _ ene$ efₗfᵣeees⟶
        ...  | e-step e⟶                                        = acc (go ee es (∈ne$-closed ene$ e⟶) (acc esrec) (efₗeefᵣeerec [ e⟶ `∷ˢ? `++ˢ?⟶ ]))
        ...  | fₗ-step fₗ⟶                                      = acc (go ee es ene$ (acc esrec) (efₗeefᵣeerec [ (?`∷ˢ `case-`of (fₗ⟶ `∷ˢ?) `/?) `++ˢ?⟶ ]))
        ...  | fᵣ-step fᵣ⟶                                      = acc (go ee es ene$ (acc esrec) (efₗeefᵣeerec [ (?`∷ˢ `case-`of?`/ (fᵣ⟶ `∷ˢ?)) `++ˢ?⟶ ]))
        ...  | ee-step ee⟶                                      = acc (go _ es ene$ (acc esrec) (efₗeefᵣeerec (((?`∷ˢ `case-`of?`/ (?`∷ˢ (⟦_⟧ᵉ⟶_.forExE Wkᵛ ee⟶))) `++ˢ?⟶) ∷ [ (?`∷ˢ `case-`of ?`∷ˢ (⟦_⟧ᵉ⟶_.forExE Wkᵛ ee⟶) `/?) `++ˢ?⟶ ])))
        ...  | es-step (≤‴-reflexive eq) efₗeefᵣeees⟶
            rewrite sym eq                                      = acc (go ee _ ene$ (acc esrec) (efₗeefᵣeerec [ efₗeefᵣeees⟶ ]))
        ...  | es-step (≤‴-step <es)     efₗeefᵣeees⟶           = acc (go ee _ ene$ (esrec (ℕ.≤‴⇒≤ <es)) (efₗeefᵣeerec [ efₗeefᵣeees⟶ ]))
        ...  | `+χ-ee                                           = TC.accessible⁻ _⟵_ (acc efₗeefᵣeerec)
        ...  | `+χ-es {A = A} {B = B} {C = C} {D = D} {e = e} {fₗ = fₗ} {fᵣ = fᵣ} {gₗ = gₗ} {gᵣ = gᵣ} {ee′ = ee′} es′ refl
            rewrite sym
                      (`∷ˢ-`++ˢ-commute
                        (e `∷ˢ
                           `case-`of fₗ `∷ˢ
                                        `case-`of RawAppSub.forEx (qᵉ Wkᵛ) gₗ
                                               `/ RawAppSub.forEx (qᵉ Wkᵛ) gᵣ
                                  `/ (fᵣ `∷ˢ
                                         `case-`of RawAppSub.forEx (qᵉ Wkᵛ) gₗ
                                                `/ RawAppSub.forEx (qᵉ Wkᵛ) gᵣ))
                        ee′ es′)
                  | `∷-lengthˢ ee′ es′ = acc (go _ _ ene$ (esrec ℕ.≤-refl) (efₗeefᵣeerec (((?`∷ˢ `case-`of?`/ `+χᵣ) `++ˢ?⟶) ∷ (?`∷ˢ `case-`of `+χₗ `/?) `++ˢ?⟶ ∷ [ `+χ `++ˢ?⟶ ])))
          where
            `+χₗ : fₗ `∷ˢ `case-`of ⟦ qᵛ Wkᵛ ⟧ᵛ gₗ `/ ⟦ qᵛ Wkᵛ ⟧ᵛ gᵣ `∷ˢ RawAppSub.forExE Wkᵛ ee′
                   ⟶ fₗ `∷ˢ
                        `case-`of ⟦ qᵛ Wkᵛ ⟧ᵛ gₗ `∷ˢ RawAppSub.forExE (qᵛ Wkᵛ) (RawAppSub.forExE Wkᵛ ee′)
                               `/ (⟦ qᵛ Wkᵛ ⟧ᵛ gᵣ `∷ˢ RawAppSub.forExE (qᵛ Wkᵛ) (RawAppSub.forExE Wkᵛ ee′))
            `+χₗ
              rewrite forExE-qᵉᵉ-forExE-Wkᵛ≡forExE-Wkᵛ-forExE {A = D} (Wkᵛ ⦃ ExtVarSub ⦄ {A = A}) ee′
                    | forExE-qᵉᵉ-forExE-Wkᵛ≡forExE-Wkᵛ-forExE {A = C} (Wkᵛ ⦃ ExtVarSub ⦄ {A = A}) ee′ = `+χ

            `+χᵣ : fᵣ `∷ˢ `case-`of ⟦ qᵛ Wkᵛ ⟧ᵛ gₗ `/ ⟦ qᵛ Wkᵛ ⟧ᵛ gᵣ `∷ˢ RawAppSub.forExE Wkᵛ ee′
                   ⟶ fᵣ `∷ˢ
                        `case-`of ⟦ qᵛ Wkᵛ ⟧ᵛ gₗ `∷ˢ RawAppSub.forExE (qᵛ Wkᵛ) (RawAppSub.forExE Wkᵛ ee′)
                               `/ (⟦ qᵛ Wkᵛ ⟧ᵛ gᵣ `∷ˢ RawAppSub.forExE (qᵛ Wkᵛ) (RawAppSub.forExE Wkᵛ ee′))
            `+χᵣ
              rewrite forExE-qᵉᵉ-forExE-Wkᵛ≡forExE-Wkᵛ-forExE {A = D} (Wkᵛ {A = B}) ee′
                    | forExE-qᵉᵉ-forExE-Wkᵛ≡forExE-Wkᵛ-forExE {A = C} (Wkᵛ {A = B}) ee′ = `+χ

    `$∈sn : e ∈ne$ → e ∈sn → f ∈sn → e `∷ˢ -`$ f ∈sn
    `$∈sn ene$ (acc erec) (acc frec) = acc λ where
      (e⟶ `∷ˢ?)         → `$∈sn (∈ne$-closed ene$ e⟶) (erec e⟶) (acc frec)
      (  ?`∷ˢ (-`$ f⟶)) → `$∈sn ene$ (acc erec) (frec f⟶)
      `→β               → case ene$ of λ ()
      `+χ               → case ene$ of λ ()

    `case∈sn : e ∈ne$ → e ∈sn → fₗ ∈sn → fᵣ ∈sn → e `∷ˢ `case-`of fₗ `/ fᵣ ∈sn
    `case∈sn ene$ (acc erec) (acc fₗrec) (acc fᵣrec) = acc λ where
      (e⟶ `∷ˢ?)                   → `case∈sn (∈ne$-closed ene$ e⟶) (erec e⟶) (acc fₗrec) (acc fᵣrec)
      (  ?`∷ˢ `case-`of fₗ⟶ `/?)  → `case∈sn ene$ (acc erec) (fₗrec fₗ⟶) (acc fᵣrec)
      (  ?`∷ˢ (`case-`of?`/ fᵣ⟶)) → `case∈sn ene$ (acc erec) (acc fₗrec) (fᵣrec fᵣ⟶)

    ∈sn-closed⁻¹ : e ⟶sn⟦ es ⟧ e′ →
                   e′ `++ˢ es ∈sn →
                   e `++ˢ es ∈sn
    ∈sn-closed⁻¹                                     (`→β fsn)         e′sn = ∈sn-weak-head-expansion`→ _ fsn e′sn
    ∈sn-closed⁻¹ {e = e `∷ˢ ee} {es = es} {e′ `∷ˢ _} (e⟶ `∷ˢ?)         e′sn
      rewrite `∷ˢ-`++ˢ-commute e ee es
            | `∷ˢ-`++ˢ-commute e′ ee es                                     = ∈sn-closed⁻¹ e⟶ e′sn
    ∈sn-closed⁻¹                                     (`+βₗ esn fₗessn) e′sn = ∈sn-weak-head-expansion`+ₗ _ esn fₗessn e′sn
    ∈sn-closed⁻¹                                     (`+βᵣ esn fᵣessn) e′sn = ∈sn-weak-head-expansion`+ᵣ _ esn fᵣessn e′sn
    ∈sn-closed⁻¹                                     (`+χ ene$)        e′sn = ∈sn-commuting-expansion _ _ ene$ e′sn

open AccessibilitySN hiding (module Properties) public
open AccessibilitySN.Properties public

module InductiveSN where
  infix 4 _∈SNe$
  infix 4 _∈SNe
  infix 4 _∈SN
  infix 4 _⟶SN⟦_⟧_
  data _∈SNe$   : Pred (Ex Γ A) lzero
  data _∈SNe    : Pred (Ex Γ A) lzero
  data _∈SN     : Pred (Ex Γ A) lzero
  data _⟶SN⟦_⟧_ : Ex Γ A → ExEs Γ A B → Ex Γ A → Set

  data _∈SNe$ where
    `#_  : (x : A ∈ Γ) →
           --------------
           `# x ∈SNe$

    _`$_ : e ∈SNe$ →
           f ∈SN →
           ------------------
           e `∷ˢ -`$ f ∈SNe$

  data _∈SNe where
    `Ne$          : e ∈SNe$ →
                    ----------
                    e ∈SNe

    `case_`of_`/_ : e ∈SNe$ →
                    fₗ ∈SN →
                    fᵣ ∈SN →
                    ------------------------------
                    e `∷ˢ `case-`of fₗ `/ fᵣ ∈SNe

  data _∈SN where
    `λ_   : e ∈SN →
            ------------
            `λ e ∈SN

    `injₗ : e ∈SN →
            --------------------
            `injₗ {B = B} e ∈SN

    `injᵣ : e ∈SN →
            --------------------
            `injᵣ {A = A} e ∈SN

    `Ne   : e ∈SNe →
            ---------
            e ∈SN

    `bclo : e ⟶SN⟦ `[] ⟧ e′ →
            e′ ∈SN →
            ------------------
            e ∈SN

  data _⟶SN⟦_⟧_ where
    _`∷ˢ? : e ⟶SN⟦ ee `∷ es ⟧ e′ →
            -----------------------------
            e `∷ˢ ee ⟶SN⟦ es ⟧ e′ `∷ˢ ee

    `→β   : ∀ {e : Ex (A ∷ Γ) B}
              {f : Ex Γ A} →
            f ∈SN →
            ---------------------------------------
            `λ e `∷ˢ -`$ f ⟶SN⟦ es ⟧ ⟦ !ˢ f ⟧ᵛ e

    `+βₗ  : ∀ {e : Ex Γ A}
              {fₗ : Ex (A ∷ Γ) C} {fᵣ : Ex (B ∷ Γ) C} →
            e ∈SN →
            fᵣ `++ˢ ⟦ Wkᵛ ⟧ᵛ* es ∈SN →
            ------------------------------------------------------
            `injₗ e `∷ˢ `case-`of fₗ `/ fᵣ ⟶SN⟦ es ⟧ ⟦ !ˢ e ⟧ᵛ fₗ

    `+βᵣ  : ∀ {e : Ex Γ B}
              {fₗ : Ex (A ∷ Γ) C} {fᵣ : Ex (B ∷ Γ) C} →
            e ∈SN →
            fₗ `++ˢ ⟦ Wkᵛ ⟧ᵛ* es ∈SN →
            ------------------------------------------------------
            `injᵣ e `∷ˢ `case-`of fₗ `/ fᵣ ⟶SN⟦ es ⟧ ⟦ !ˢ e ⟧ᵛ fᵣ

    `+χ   : ∀ {e : Ex Γ (A `+ B)}
              {fₗ : Ex (A ∷ Γ) C} {fᵣ : Ex (B ∷ Γ) C}
              {ee : ExE Γ C D} →
            e ∈SNe$ →
            --------------------------------------------------------------
            e `∷ˢ `case-`of fₗ `/ fᵣ `∷ˢ ee
              ⟶SN⟦ es ⟧ e `∷ˢ
                          `case-`of (fₗ `∷ˢ RawAppSub.forExE Wkᵛ ee)
                                 `/ (fᵣ `∷ˢ RawAppSub.forExE Wkᵛ ee)

  module Properties where
    infixr 50 ⟦_⟧ᵉ∈SN_
    infixr 50 ⟦_⟧ᵉ∈SNe$_
    infixr 50 ⟦_⟧ᵉ∈SNe_
    infixr 50 ⟦_⟧ᵉ⟶SN_
    ⟦_⟧ᵉ∈SN_   : ∀ {e : Ex Γ A} (δ : Ext Δ Γ) → e ∈SN → ⟦ δ ⟧ᵛ e ∈SN
    ⟦_⟧ᵉ∈SNe$_ : ∀ {e : Ex Γ A} (δ : Ext Δ Γ) → e ∈SNe$ → ⟦ δ ⟧ᵛ e ∈SNe$
    ⟦_⟧ᵉ∈SNe_  : ∀ {e : Ex Γ A} (δ : Ext Δ Γ) → e ∈SNe → ⟦ δ ⟧ᵛ e ∈SNe
    ⟦_⟧ᵉ⟶SN_   : ∀ {e : Ex Γ A} (δ : Ext Δ Γ) → e ⟶SN⟦ es ⟧ e′ → ⟦ δ ⟧ᵛ e ⟶SN⟦ ⟦ δ ⟧ᵛ* es ⟧ ⟦ δ ⟧ᵛ e′

    ⟦ δ ⟧ᵉ∈SN (`λ eSN)        = `λ (⟦ qᵉ δ ⟧ᵉ∈SN eSN)
    ⟦ δ ⟧ᵉ∈SN (`injₗ eSN)     = `injₗ (⟦ δ ⟧ᵉ∈SN eSN)
    ⟦ δ ⟧ᵉ∈SN (`injᵣ eSN)     = `injᵣ (⟦ δ ⟧ᵉ∈SN eSN)
    ⟦ δ ⟧ᵉ∈SN `Ne eSNe        = `Ne (⟦ δ ⟧ᵉ∈SNe eSNe)
    ⟦ δ ⟧ᵉ∈SN `bclo e⟶SN e′SN = `bclo (⟦ δ ⟧ᵉ⟶SN e⟶SN) (⟦ δ ⟧ᵉ∈SN e′SN)

    ⟦ δ ⟧ᵉ∈SNe$ (`# x)         = `# δ x
    ⟦ δ ⟧ᵉ∈SNe$ (eSNe$ `$ fSN) = (⟦ δ ⟧ᵉ∈SNe$ eSNe$) `$ (⟦ δ ⟧ᵉ∈SN fSN)

    ⟦ δ ⟧ᵉ∈SNe `Ne$ eSNe$                     = `Ne$ (⟦ δ ⟧ᵉ∈SNe$ eSNe$)
    ⟦ δ ⟧ᵉ∈SNe (`case eSNe$ `of fₗSN `/ fᵣSN) = `case (⟦ δ ⟧ᵉ∈SNe$ eSNe$) `of (⟦ qᵉ δ ⟧ᵉ∈SN fₗSN) `/ (⟦ qᵉ δ ⟧ᵉ∈SN fᵣSN)

    ⟦ δ ⟧ᵉ⟶SN (_`∷ˢ? {ee = ee} {es = es} e⟶SN)
      with ⟦δ⟧ees⟶SN ← ⟦ δ ⟧ᵉ⟶SN e⟶SN
        rewrite `∷-⟦-⟧ᵛ*-commute δ ee es       = ⟦δ⟧ees⟶SN `∷ˢ?
    ⟦ δ ⟧ᵉ⟶SN `→β {e = e} {f = f} fSN
      rewrite sym (⟦!ᵛ⟦-⟧ᵛ-⟧ᵛ⟦qᵛ-⟧ᵛ≡⟦-⟧ᵛ⟦!ᵛ-⟧ᵛ δ f e) = `→β (⟦ δ ⟧ᵉ∈SN fSN)
    ⟦ δ ⟧ᵉ⟶SN `+βₗ {B = B} {es = es} {e = e} {fₗ = fₗ} {fᵣ = fᵣ} eSN fᵣesSN
      with ⟦qδ⟧fᵣesSN ← ⟦ qᵉ δ ⟧ᵉ∈SN fᵣesSN
        rewrite sym (⟦!ᵛ⟦-⟧ᵛ-⟧ᵛ⟦qᵛ-⟧ᵛ≡⟦-⟧ᵛ⟦!ᵛ-⟧ᵛ δ e fₗ)
              | `++ˢ-⟦-⟧ᵛ-commute (qᵛ δ) fᵣ (⟦ Wkᵛ ⟧ᵛ* es)
              | ⟦qᵉᵉ-⟧ᵛ*⟦Wkᵛ⟧ᵛ*≡⟦Wkᵛ⟧ᵛ*⟦-⟧ᵛ* {A = B} δ es = `+βₗ (⟦ δ ⟧ᵉ∈SN eSN) ⟦qδ⟧fᵣesSN
    ⟦ δ ⟧ᵉ⟶SN `+βᵣ {A = A} {es = es} {e = e} {fₗ = fₗ} {fᵣ = fᵣ} eSN fₗesSN
      with ⟦qδ⟧fₗesSN ← ⟦ qᵉ δ ⟧ᵉ∈SN fₗesSN
        rewrite sym (⟦!ᵛ⟦-⟧ᵛ-⟧ᵛ⟦qᵛ-⟧ᵛ≡⟦-⟧ᵛ⟦!ᵛ-⟧ᵛ δ e fᵣ)
              | `++ˢ-⟦-⟧ᵛ-commute (qᵛ δ) fₗ (⟦ Wkᵛ ⟧ᵛ* es)
              | ⟦qᵉᵉ-⟧ᵛ*⟦Wkᵛ⟧ᵛ*≡⟦Wkᵛ⟧ᵛ*⟦-⟧ᵛ* {A = A} δ es = `+βᵣ (⟦ δ ⟧ᵉ∈SN eSN) ⟦qδ⟧fₗesSN
    ⟦ δ ⟧ᵉ⟶SN `+χ {A = A} {B = B} {ee = ee} eSNe$
      rewrite forExE-qᵉᵉ-forExE-Wkᵛ≡forExE-Wkᵛ-forExE {A = A} δ ee
            | forExE-qᵉᵉ-forExE-Wkᵛ≡forExE-Wkᵛ-forExE {A = B} δ ee = `+χ (⟦ δ ⟧ᵉ∈SNe$ eSNe$)

    infix 4 _*∈SN
    _*∈SN : Sub Δ Γ → Set
    σ *∈SN = ∀ {A} (x : A ∈ _) → σ x ∈SN

    !ᵛ∈SN : ∀ {e : Ex Γ A} →
            e ∈SN →
            !ᵛ e *∈SN
    !ᵛ∈SN eSN (here refl) = eSN
    !ᵛ∈SN eSN (there x)   = `Ne (`Ne$ (`# x))

    qᵛ∈SN : ∀ {σ : Sub Δ Γ} →
            σ *∈SN →
            qᵛ_ {A = A} σ *∈SN
    qᵛ∈SN σSN (here refl) = `Ne (`Ne$ (`# `!! 0))
    qᵛ∈SN σSN (there x)   = ⟦ Wkᵛ ⟧ᵉ∈SN (σSN x)

    Tp-size : Tp → ℕ
    Tp-size `base    = 0
    Tp-size (A `→ B) = suc (Tp-size A + Tp-size B)
    Tp-size (A `+ B) = suc (Tp-size A + Tp-size B)

    !ᵛ-closure∈ : ∀ {f : Ex Γ A} →
                  (x : B ∈ Δ ++ A ∷ Γ) →
                  f ∈SN →
                  ((qᵛ⟦ Δ ⟧ (Sub _ _ ∋ !ᵛ f)) x ∈SN × Tp-size B ≤ Tp-size A)
                    ⊎ (qᵛ⟦ Δ ⟧ (Sub _ _ ∋ !ᵛ f)) x ∈SNe$
    !ᵛ-closure∈ {Δ = []}    (here refl) fSN = inj₁ (fSN , ℕ.≤-refl)
    !ᵛ-closure∈ {Δ = []}    (there x)   fSN = inj₂ (`# x)
    !ᵛ-closure∈ {Δ = _ ∷ _} (here refl) fSN = inj₂ (`# `!! 0)
    !ᵛ-closure∈ {Δ = _ ∷ _} (there x)   fSN
      with !ᵛ-closure∈ x fSN
    ...  | inj₁ (⟦f⟧xSN , ≤A)               = inj₁ (⟦ Wkᵛ ⟧ᵉ∈SN ⟦f⟧xSN , ≤A)
    ...  | inj₂ ⟦f⟧xSNe$                    = inj₂ (⟦ Wkᵛ ⟧ᵉ∈SNe$ ⟦f⟧xSNe$)

    -- `$-closure         : ∀ {e : Ex Γ (A `→ B)} {f : Ex Γ A} →
    --                      Acc _<_ (Tp-size A) →
    --                      e ∈SN →
    --                      f ∈SN →
    --                      e `∷ˢ -`$ f ∈SN
    -- `case-closure      : ∀ {e : Ex Γ (A `+ B)} {fₗ : Ex (A ∷ Γ) C} {fᵣ : Ex (B ∷ Γ) C} →
    --                      Acc _<_ (Tp-size (A `+ B)) →
    --                      e ∈SN →
    --                      fₗ ∈SN →
    --                      fᵣ ∈SN →
    --                      e `∷ˢ `case-`of fₗ `/ fᵣ ∈SN
    -- ⟦!ᵛ-⟧ᵛ-closure     : ∀ {e : Ex (Δ ++ A ∷ Γ) B} {f : Ex Γ A} →
    --                      Acc _<_ (Tp-size A) →
    --                      e ∈SN →
    --                      f ∈SN →
    --                      ⟦ qᵛ⟦ Δ ⟧ !ˢ f ⟧ᵛ e ∈SN
    -- ⟦!ᵛ-⟧ᵛ-closure$    : ∀ {e : Ex (Δ ++ A ∷ Γ) B} {f : Ex Γ A} →
    --                      Acc _<_ (Tp-size A) →
    --                      e ∈SNe$ →
    --                      f ∈SN →
    --                      (⟦ qᵛ⟦ Δ ⟧ !ˢ f ⟧ᵛ e ∈SN × Tp-size B ≤ Tp-size A)
    --                        ⊎ ⟦ qᵛ⟦ Δ ⟧ !ˢ f ⟧ᵛ e ∈SNe$
    -- ⟶SN-`$-closure     : ∀ {e e′ : Ex Γ A} {f : Ex Γ B} →
    --                      Acc _<_ (Tp-size B) →
    --                      e ⟶SN⟦ es ⟧ e′ →
    --                      f ∈SN →
    --                      e ⟶SN⟦ es `∷ˢ -`$ f ⟧ e′
    -- ⟶SN-`case-closure  : ∀ {e e′ : Ex Γ A} {fₗ : Ex (B ∷ Γ) D} {fᵣ : Ex (C ∷ Γ) D} →
    --                      Acc _<_ (Tp-size (B `+ C)) →
    --                      e ⟶SN⟦ es ⟧ e′ →
    --                      fₗ ∈SN →
    --                      fᵣ ∈SN →
    --                      e ⟶SN⟦ es `∷ˢ `case-`of fₗ `/ fᵣ ⟧ e′
    -- ⟶SN-⟦!ᵛ-⟧ᵛ-closure : ∀ {e e′ : Ex (Δ ++ A ∷ Γ) B} {f : Ex Γ A} →
    --                      Acc _<_ (Tp-size A) →
    --                      e ⟶SN⟦ es ⟧ e′ →
    --                      f ∈SN →
    --                      (⟦ qᵛ⟦ Δ ⟧ !ˢ f ⟧ᵛ e) ⟶SN⟦ ⟦ (Sub _ _ ∋ qᵛ⟦ Δ ⟧ !ˢ f) ⟧ᵛ* es ⟧ (⟦ qᵛ⟦ Δ ⟧ !ˢ f ⟧ᵛ e′)

    -- `$-closure Aacc (`λ eSN)                             fSN = `bclo (`→β fSN) (⟦!ᵛ-⟧ᵛ-closure Aacc eSN fSN)
    -- `$-closure Aacc (`Ne (`Ne$ eSNe$))                   fSN = `Ne (`Ne$ (eSNe$ `$ fSN))
    -- `$-closure Aacc (`Ne (`case eSNe$ `of gₗSN `/ gᵣSN)) fSN = `bclo (`+χ eSNe$) (`Ne (`case eSNe$ `of `$-closure Aacc gₗSN (⟦ Wkᵛ ⟧ᵉ∈SN fSN) `/ `$-closure Aacc gᵣSN (⟦ Wkᵛ ⟧ᵉ∈SN fSN)))
    -- `$-closure Aacc (`bclo e⟶ eSN)                       fSN = `bclo ((⟶SN-`$-closure Aacc e⟶ fSN) `∷ˢ?) (`$-closure Aacc eSN fSN)

    -- `case-closure (acc ABrec) (`injₗ eSN)                          fₗSN fᵣSN = `bclo (`+βₗ eSN fᵣSN) (⟦!ᵛ-⟧ᵛ-closure (ABrec (ℕ.m≤m+n _ _)) fₗSN eSN)
    -- `case-closure (acc ABrec) (`injᵣ eSN)                          fₗSN fᵣSN = `bclo (`+βᵣ eSN fₗSN) (⟦!ᵛ-⟧ᵛ-closure (ABrec (s≤s (ℕ.m≤n+m _ _))) fᵣSN eSN)
    -- `case-closure ABacc       (`Ne (`Ne$ eSNe$))                   fₗSN fᵣSN = `Ne (`case eSNe$ `of fₗSN `/ fᵣSN)
    -- `case-closure ABacc       (`Ne (`case eSNe$ `of gₗSN `/ gᵣSN)) fₗSN fᵣSN = `bclo (`+χ eSNe$) (`Ne (`case eSNe$ `of `case-closure ABacc gₗSN (⟦ qᵉ Wkᵛ ⟧ᵉ∈SN fₗSN) (⟦ qᵉ Wkᵛ ⟧ᵉ∈SN fᵣSN) `/ `case-closure ABacc gᵣSN (⟦ qᵉ Wkᵛ ⟧ᵉ∈SN fₗSN) (⟦ qᵉ Wkᵛ ⟧ᵉ∈SN fᵣSN)))
    -- `case-closure ABacc       (`bclo e⟶ eSN)                       fₗSN fᵣSN = `bclo (⟶SN-`case-closure ABacc e⟶ fₗSN fᵣSN `∷ˢ?) (`case-closure ABacc eSN fₗSN fᵣSN)

    -- ⟦!ᵛ-⟧ᵛ-closure Aacc (`λ eSN)                             fSN = `λ (⟦!ᵛ-⟧ᵛ-closure Aacc eSN fSN)
    -- ⟦!ᵛ-⟧ᵛ-closure Aacc (`injₗ eSN)                          fSN = `injₗ (⟦!ᵛ-⟧ᵛ-closure Aacc eSN fSN)
    -- ⟦!ᵛ-⟧ᵛ-closure Aacc (`injᵣ eSN)                          fSN = `injᵣ (⟦!ᵛ-⟧ᵛ-closure Aacc eSN fSN)
    -- ⟦!ᵛ-⟧ᵛ-closure Aacc (`Ne (`Ne$ eSNe$))                   fSN
    --   with ⟦!ᵛ-⟧ᵛ-closure$ Aacc eSNe$ fSN
    -- ...  | inj₁ (⟦f⟧eSN , _)                                     = ⟦f⟧eSN
    -- ...  | inj₂ ⟦f⟧eSNe$                                         = `Ne (`Ne$ ⟦f⟧eSNe$)
    -- ⟦!ᵛ-⟧ᵛ-closure Aacc (`Ne (`case eSNe$ `of gₗSN `/ gᵣSN)) fSN
    --   with ⟦!ᵛ-⟧ᵛ-closure$ Aacc eSNe$ fSN
    -- ...  | inj₁ (⟦f⟧eSN , _)                                     = {!!}
    -- ...  | inj₂ ⟦f⟧eSNe$                                         = `Ne (`case ⟦f⟧eSNe$ `of ⟦!ᵛ-⟧ᵛ-closure Aacc gₗSN fSN `/ ⟦!ᵛ-⟧ᵛ-closure Aacc gᵣSN fSN)
    -- ⟦!ᵛ-⟧ᵛ-closure Aacc (`bclo e⟶ eSN)                       fSN = `bclo {!!} (⟦!ᵛ-⟧ᵛ-closure Aacc eSN fSN)

    -- ⟦!ᵛ-⟧ᵛ-closure$ _               (`# x)         fSN = !ᵛ-closure∈ x fSN
    -- ⟦!ᵛ-⟧ᵛ-closure$ Aacc@(acc Arec) (eSNe$ `$ gSN) fSN
    --   with ⟦!ᵛ-⟧ᵛ-closure$ Aacc eSNe$ fSN
    -- ...  | inj₁ (⟦f⟧eSN , ≤A)
    --     with ⟦f⟧gSN ← ⟦!ᵛ-⟧ᵛ-closure Aacc gSN fSN      = inj₁ (`$-closure (Arec (ℕ.m+n≤o⇒m≤o _ ≤A)) ⟦f⟧eSN ⟦f⟧gSN , ℕ.m+n≤o⇒n≤o _ ≤A)
    -- ...  | inj₂ ⟦f⟧eSNe$                               = inj₂ (⟦f⟧eSNe$ `$ ⟦!ᵛ-⟧ᵛ-closure Aacc gSN fSN)

    -- ⟶SN-`$-closure Bacc (e⟶ `∷ˢ?)         fSN = ⟶SN-`$-closure Bacc e⟶ fSN `∷ˢ?
    -- ⟶SN-`$-closure Bacc (`→β gSN)         fSN = `→β gSN
    -- ⟶SN-`$-closure Bacc (`+βₗ eSN gᵣesSN) fSN = `+βₗ eSN (`$-closure Bacc gᵣesSN (⟦ Wkᵛ ⟧ᵉ∈SN fSN))
    -- ⟶SN-`$-closure Bacc (`+βᵣ eSN gₗesSN) fSN = `+βᵣ eSN (`$-closure Bacc gₗesSN (⟦ Wkᵛ ⟧ᵉ∈SN fSN))
    -- ⟶SN-`$-closure Bacc (`+χ eSNe$)       fSN = `+χ eSNe$

    -- ⟶SN-`case-closure BCacc (e⟶ `∷ˢ?)         fₗSN fᵣSN = ⟶SN-`case-closure BCacc e⟶ fₗSN fᵣSN `∷ˢ?
    -- ⟶SN-`case-closure BCacc (`→β gSN)         fₗSN fᵣSN = `→β gSN
    -- ⟶SN-`case-closure BCacc (`+βₗ eSN gᵣesSN) fₗSN fᵣSN = `+βₗ eSN (`case-closure BCacc gᵣesSN (⟦ qᵉ Wkᵛ ⟧ᵉ∈SN fₗSN) (⟦ qᵉ Wkᵛ ⟧ᵉ∈SN fᵣSN))
    -- ⟶SN-`case-closure BCacc (`+βᵣ eSN gₗesSN) fₗSN fᵣSN = `+βᵣ eSN (`case-closure BCacc gₗesSN (⟦ qᵉ Wkᵛ ⟧ᵉ∈SN fₗSN) (⟦ qᵉ Wkᵛ ⟧ᵉ∈SN fᵣSN))
    -- ⟶SN-`case-closure BCacc (`+χ eSNe$)       fₗSN fᵣSN = `+χ eSNe$

    -- ⟶SN-⟦!ᵛ-⟧ᵛ-closure Aacc (_`∷ˢ? {ee = ee} {es = es} e⟶) fSN
    --   with ⟦f⟧e⟶ ← ⟶SN-⟦!ᵛ-⟧ᵛ-closure Aacc e⟶ fSN
    --     rewrite = {!`∷-⟦-⟧ᵛ*-commute !} `∷ˢ?
    -- ⟶SN-⟦!ᵛ-⟧ᵛ-closure Aacc (`→β gSN) fSN = {!`∷-⟦-⟧ᵛ*-commute!}
    -- ⟶SN-⟦!ᵛ-⟧ᵛ-closure Aacc (`+βₗ eSN gᵣesSN) fSN = {!`+βₗ!}
    -- ⟶SN-⟦!ᵛ-⟧ᵛ-closure Aacc (`+βᵣ eSN gₗesSN) fSN = {!!}
    -- ⟶SN-⟦!ᵛ-⟧ᵛ-closure Aacc (`+χ eSNe$) fSN = {!!}

--     infixr 50 ⟦_⟧ᵉ⁻¹∈SN_of_by_
--     infixr 50 ⟦_⟧ᵉ⁻¹∈SNe_of_by_
--     infixr 50 ⟦_⟧ᵉ⁻¹⟶SN_of_by_
--     ⟦_⟧ᵉ⁻¹∈SN_of_by_  : ∀ {M₀ : Tm Δ A} (δ : Ext Δ Γ) → M₀ ∈SN → ∀ M → M₀ ≡ ⟦ δ ⟧ᵛ M → M ∈SN
--     ⟦_⟧ᵉ⁻¹∈SNe_of_by_ : ∀ {M₀ : Tm Δ A} (δ : Ext Δ Γ) → M₀ ∈SNe → ∀ M → M₀ ≡ ⟦ δ ⟧ᵛ M → M ∈SNe
--     ⟦_⟧ᵉ⁻¹⟶SN_of_by_  : ∀ {M₀ : Tm Δ A} (δ : Ext Δ Γ) → M₀ ⟶SN M′₀ → ∀ M → M₀ ≡ ⟦ δ ⟧ᵛ M → ∃[ M′ ] M ⟶SN M′ × ⟦ δ ⟧ᵛ M′ ≡ M′₀

--     ⟦ δ ⟧ᵉ⁻¹∈SN `λ M₀SN           of `λ M by refl = `λ (⟦ qᵉ δ ⟧ᵉ⁻¹∈SN M₀SN of M by refl)
--     ⟦ δ ⟧ᵉ⁻¹∈SN `Ne M₀SNe         of M    by eq   = `Ne (⟦ δ ⟧ᵉ⁻¹∈SNe M₀SNe of M by eq)
--     ⟦ δ ⟧ᵉ⁻¹∈SN `bclo M₀⟶SN M′₀SN of M    by eq
--       with _ , M⟶SN , refl ← ⟦ δ ⟧ᵉ⁻¹⟶SN M₀⟶SN of M by eq = `bclo M⟶SN (⟦ δ ⟧ᵉ⁻¹∈SN M′₀SN of _ by refl)

--     ⟦ δ ⟧ᵉ⁻¹∈SNe `# y          of `# x   by eq = `# x
--     ⟦ δ ⟧ᵉ⁻¹∈SNe M₀SNe `$ N₀SN of M `$ N by refl = (⟦ δ ⟧ᵉ⁻¹∈SNe M₀SNe of M by refl) `$ (⟦ δ ⟧ᵉ⁻¹∈SN N₀SN of N by refl)

--     ⟦ δ ⟧ᵉ⁻¹⟶SN M₀⟶SN `$- of M `$ N      by refl
--       with _ , M⟶SN , refl ← ⟦ δ ⟧ᵉ⁻¹⟶SN M₀⟶SN of M by refl = _ , M⟶SN `$- , refl
--     ⟦ δ ⟧ᵉ⁻¹⟶SN `→β N₀SN  of (`λ M) `$ N by refl = _ , `→β (⟦ δ ⟧ᵉ⁻¹∈SN N₀SN of N by refl) , sym (⟦!ˢ⟦-⟧ᵛ-⟧ᵛ⟦qᵉᵉ-⟧ᵛ≡⟦-⟧ᵛ⟦!ˢ-⟧ᵛ δ N M)

--     infixr 50 ⟦_⟧ᵉ⁻¹∈SN_
--     ⟦_⟧ᵉ⁻¹∈SN_ : ∀ {M : Tm Γ A} (δ : Ext Δ Γ) → ⟦ δ ⟧ᵛ M ∈SN → M ∈SN
--     ⟦ δ ⟧ᵉ⁻¹∈SN [δ]MSN = ⟦ δ ⟧ᵉ⁻¹∈SN [δ]MSN of _ by refl

--     infixr 50 ⟦_⟧ᵉ⁻¹∈SNe_
--     ⟦_⟧ᵉ⁻¹∈SNe_ : ∀ {M : Tm Γ A} (δ : Ext Δ Γ) → ⟦ δ ⟧ᵛ M ∈SNe → M ∈SNe
--     ⟦ δ ⟧ᵉ⁻¹∈SNe [δ]MSNe = ⟦ δ ⟧ᵉ⁻¹∈SNe [δ]MSNe of _ by refl

--     infixr 50 ⟦_⟧ᵉ⁻¹⟶SN_
--     ⟦_⟧ᵉ⁻¹⟶SN_ : ∀ {M : Tm Γ A} (δ : Ext Δ Γ) → ⟦ δ ⟧ᵛ M ⟶SN M′ → ∃[ M″ ] M ⟶SN M″ × ⟦ δ ⟧ᵛ M″ ≡ M′
--     ⟦ δ ⟧ᵉ⁻¹⟶SN [δ]M⟶SN = ⟦ δ ⟧ᵉ⁻¹⟶SN [δ]M⟶SN of _ by refl

--     ∈SN-extensionality : M `$ (`# x) ∈SN → M ∈SN
--     ∈SN-extensionality (`Ne (MSNe `$ xSN))                                = `Ne MSNe
--     ∈SN-extensionality (`bclo                   (Mx⟶SN `$-)        M′xSN) = `bclo Mx⟶SN (∈SN-extensionality M′xSN)
--     ∈SN-extensionality (`bclo {M = (`λ M) `$ _} (`→β (`Ne (`# x))) M′xSN)
--       rewrite sym (⟦-⟧ᵛ-extensional ⦃ SubVarSub ⦄ M (liftᵛ-preserves-,ᵛ Idᵛ x))
--             | liftᵛ-preserves-Appᵛ (!ᵛ x) M                               = `λ (⟦ !ᵛ x ⟧ᵉ⁻¹∈SN M′xSN)

open InductiveSN hiding (module Properties) public
open InductiveSN.Properties public

module Soundness where
  SNe$-ne$-sound : e ∈SNe$ → e ∈ne$
  SNe$-ne$-sound (`# x)      = `# x
  SNe$-ne$-sound (eSNe `$ _) = SNe$-ne$-sound eSNe `$-

  SN-sound   : e ∈SN → e ∈sn
  SNe-sound  : e ∈SNe → e ∈sn
  SNe$-sound : e ∈SNe$ → e ∈sn
  ⟶SN-sound  : e ⟶SN⟦ es ⟧ e′ → e ⟶sn⟦ es ⟧ e′

  SN-sound (`λ eSN)         = `λ∈sn (SN-sound eSN)
  SN-sound (`injₗ eSN)      = `injₗ∈sn (SN-sound eSN)
  SN-sound (`injᵣ eSN)      = `injᵣ∈sn (SN-sound eSN)
  SN-sound (`Ne eSNe)       = SNe-sound eSNe
  SN-sound (`bclo e⟶SN eSN) = ∈sn-closed⁻¹ (⟶SN-sound e⟶SN) (SN-sound eSN)

  SNe-sound (`Ne$ eSNe$)                   = SNe$-sound eSNe$
  SNe-sound (`case eSNe$ `of fₗSN `/ fᵣSN) = `case∈sn (SNe$-ne$-sound eSNe$) (SNe$-sound eSNe$) (SN-sound fₗSN) (SN-sound fᵣSN)

  SNe$-sound (`# x)         = `#∈sn x
  SNe$-sound (eSNe$ `$ fSN) = `$∈sn (SNe$-ne$-sound eSNe$) (SNe$-sound eSNe$) (SN-sound fSN)

  ⟶SN-sound (e⟶ `∷ˢ?)         = ⟶SN-sound e⟶ `∷ˢ?
  ⟶SN-sound (`→β fSN)         = `→β (SN-sound fSN)
  ⟶SN-sound (`+βₗ eSN fᵣesSN) = `+βₗ (SN-sound eSN) (SN-sound fᵣesSN)
  ⟶SN-sound (`+βᵣ eSN fₗesSN) = `+βᵣ (SN-sound eSN) (SN-sound fₗesSN)
  ⟶SN-sound (`+χ eSNe$)       = `+χ (SNe$-ne$-sound eSNe$)

open Soundness public

-- module LogicalRelation where
--   LogicalRelation   : Pred (Ex Γ A) lzero
--   LogicalRelationEs : Pred (ExEs Γ (A `+ B) C) lzero

--   infix 4 LogicalRelationSyntax
--   LogicalRelationSyntax = LogicalRelation
--   syntax LogicalRelationSyntax {A = A} e = e ∈ℜ[ A ]

--   infix 4 LogicalRelationEsSyntax
--   LogicalRelationEsSyntax = LogicalRelationEs
--   syntax LogicalRelationEsSyntax {A = A} {B = B} es = es ∈ℜᵉ*[ A `+ B ]

--   LogicalRelation {A = `base}    = _∈SN
--   LogicalRelation {A = _ `→ _} e = ∀ {Δ} (δ : Ext Δ _) {f} → f ∈ℜ[ _ ] → ⟦ δ ⟧ᵛ e `∷ˢ -`$ f ∈ℜ[ _ ]
--   LogicalRelation {A = _ `+ _} e = ∀ {Δ} (δ : Ext Δ _) {C} (es : ExEs Δ _ C) → es ∈ℜᵉ*[ _ `+ _ ] → ⟦ δ ⟧ᵛ e `++ˢ es ∈SN

--   LogicalRelationEs {A = A} {B = B} es = ∀ {Δ} (δ : Ext Δ _) → (∀ {eₗ} → eₗ ∈ℜ[ _ ] → `injₗ eₗ `++ˢ ⟦ δ ⟧ᵛ* es ∈SN) × (∀ {eᵣ} → eᵣ ∈ℜ[ _ ] → `injᵣ eᵣ `++ˢ ⟦ δ ⟧ᵛ* es ∈SN)

--   SubstLogicalRelation : Pred (Sub Γ Δ) lzero

--   infix 4 SubstLogicalRelationSyntax
--   SubstLogicalRelationSyntax = SubstLogicalRelation
--   syntax SubstLogicalRelationSyntax {Δ = Δ} σ = σ ∈ℜs[ Δ ]

--   SubstLogicalRelation {Δ = []}    σ = ⊤
--   SubstLogicalRelation {Δ = _ ∷ _} σ = σ ∘ Wkᵛ ∈ℜs[ _ ] × σ (here refl) ∈ℜ[ _ ]

--   module Properties where
--     reify    : e ∈ℜ[ A ] → e ∈SN
--     reflect$ : e ∈SNe$ → e ∈ℜ[ A ]

--     reify {A = `base}          eℜ = eℜ
--     reify {A = _ `→ _}         eℜ = {!!} -- ⟦ Wkᵛ ⟧ᵉ⁻¹∈SN ∈SN-extensionality (reify (eℜ Wkᵛ (reflect (`# here refl))))
--     reify {A = _ `+ _} {e = e} eℜ = subst _∈SN (⟦Idᵛ⟧ᵛ≡liftᵛ ⦃ _ ⦄ ⦃ SubVarSub ⦄ e) (eℜ Idᵛ `[] λ δ → (λ eₗℜ → `injₗ (reify eₗℜ)) , (λ eᵣℜ → `injᵣ (reify eᵣℜ)))

--     reflect$ {A = `base}  eSNe$          = `Ne (`Ne$ eSNe$)
--     reflect$ {A = _ `→ _} eSNe$ δ fℜ     = reflect$ ((⟦ δ ⟧ᵉ∈SNe$ eSNe$) `$ (reify fℜ))
--     reflect$ {A = _ `+ _} eSNe$ δ es esℜ = {!esℜ Wkᵛ!} -- inj₁ (_ , ε , `Ne$ eSNe$)

--     bclosed : e ⟶SN⟦ `[] ⟧ e′ → e′ ∈ℜ[ A ] → e ∈ℜ[ A ]
--     bclosed {A = `base}  e⟶SN e′ℜ      = `bclo e⟶SN e′ℜ
--     bclosed {A = _ `→ _} e⟶SN e′ℜ δ fℜ = bclosed ({!!} `∷ˢ?) (e′ℜ δ fℜ)
--     bclosed {A = _ `+ _} e⟶SN e′ℜ      = {!!}

-- --     liftᵛ∈ℜs : ∀ Δ (δ : Ext Γ Δ) → liftᵛ∘ δ ∈ℜs[ Δ ]
-- --     liftᵛ∈ℜs []      δ = tt
-- --     liftᵛ∈ℜs (_ ∷ Δ) δ = liftᵛ∈ℜs Δ (δ ∘ Wkᵛ) , reflect (`Ne$ (`# δ (here refl)))

-- --     Idˢ∈ℜs : ∀ Γ → Idᵛ ∈ℜs[ Γ ]
-- --     Idˢ∈ℜs Γ = liftᵛ∈ℜs Γ Idᵛ

-- --     infixr 50 ⟦_⟧ᵉ∈ℜ_
-- --     ⟦_⟧ᵉ∈ℜ_ : ∀ (δ : Ext Γ Δ) → M ∈ℜ[ A ] → ⟦ δ ⟧ᵛ M ∈ℜ[ A ]
-- --     ⟦_⟧ᵉ∈ℜ_ {A = base}           δ Mℜ      = ⟦ δ ⟧ᵉ∈SN Mℜ
-- --     ⟦_⟧ᵉ∈ℜ_ {A = _ `→ _} {M = M} δ Mℜ ρ Nℜ
-- --       rewrite ⟦-⟧ᵛ-compositional ρ δ M     = Mℜ (ρ ∘ᵛ δ) Nℜ

-- --     infixr 50 ⟦_⟧ᵉ∈ℜs_
-- --     ⟦_⟧ᵉ∈ℜs_ : ∀ (δ : Ext Γ Δ) → σ ∈ℜs[ Ψ ] → δ ∘ᵛ σ ∈ℜs[ Ψ ]
-- --     ⟦_⟧ᵉ∈ℜs_ {Ψ = []}    δ σℜ = tt
-- --     ⟦_⟧ᵉ∈ℜs_ {Ψ = _ ∷ _} δ σℜ = ⟦ δ ⟧ᵉ∈ℜs σℜ .proj₁ , ⟦ δ ⟧ᵉ∈ℜ (σℜ .proj₂)

--     fundamental-lemma-∈ : ∀ {σ : Sub Γ Δ} (x : A ∈ Δ) → σ ∈ℜs[ Δ ] → σ x ∈ℜ[ A ]
--     fundamental-lemma-∈ (here refl) σℜ = σℜ .proj₂
--     fundamental-lemma-∈ (there x)   σℜ = fundamental-lemma-∈ x (σℜ .proj₁)

--     fundamental-lemma : ∀ {σ : Sub Γ Δ} (e : Ex Δ A) → σ ∈ℜs[ Δ ] → ⟦ σ ⟧ᵛ e ∈ℜ[ A ]
--     fundamental-lemma         (`# x)                     σℜ          = fundamental-lemma-∈ x σℜ
--     fundamental-lemma {σ = σ} (`λ e)                     σℜ δ {f} fℜ
--       with eℜ ← fundamental-lemma {σ = (δ ∘ᵛ σ) ,ᵛ _} e ({!!} , fℜ)
--         rewrite sym (⟦-⟧ᵛ-extensional e (!ᵛ-∘ᵛ-qᵛ (δ ∘ᵛ σ) f))
--               | sym (⟦-⟧ᵛ-compositional (!ᵛ f) (qᵉ (δ ∘ᵛ σ)) e)
--               | ⟦-⟧ᵛ-extensional e (qᵉ-distrib-∘ᵉˢ δ σ)
--               | sym (⟦-⟧ᵛ-compositional (qᵉ δ) (qᵉ σ) e) = bclosed (`→β (reify fℜ)) eℜ
--     fundamental-lemma {σ = σ} (`injₗ e)                  σℜ          = {!!} -- inj₂ (inj₁ (_ , ε , fundamental-lemma e σℜ))
--     fundamental-lemma {σ = σ} (`injᵣ e)                  σℜ          = {!!} -- inj₂ (inj₂ (_ , ε , fundamental-lemma e σℜ))
--     fundamental-lemma {σ = σ} (e `∷ˢ -`$ f)              σℜ
--       rewrite sym (⟦Idᵛ⟧ᵛ≡liftᵛ ⦃ _ ⦄ ⦃ SubVarSub ⦄ (⟦ σ ⟧ᵛ e))      = fundamental-lemma e σℜ Idᵛ (fundamental-lemma f σℜ)
--     fundamental-lemma {σ = σ} (e `∷ˢ `case-`of fₗ `/ fᵣ) σℜ          = {!!}
--     --   with fundamental-lemma e σℜ
--     -- ...  | inj₁ (_ , e⟶ , e′ℜ)                                       = bclosed {!!} {!reflect!}
--     -- ...  | inj₂ (inj₁ (_ , e⟶ , eₗℜ))                                = {!!}
--     -- ...  | inj₂ (inj₂ (_ , e⟶ , eᵣℜ))                                = {!!}
--       -- with eℜ ← fundamental-lemma e σℜ               = {!!}
--     -- fundamental-lemma {σ = σ} (M `$ N) σℜ
--     --   rewrite sym (⟦Idᵉ⟧ᵛ-id (⟦ σ ⟧ᵛ M))           = fundamental-lemma M σℜ Idᵛ (fundamental-lemma N σℜ)

-- -- open LogicalRelation hiding (module Properties) public
-- -- open LogicalRelation.Properties public

-- -- strong-normalization : ∀ (M : Tm Γ A) →
-- --                        M ∈sn
-- -- strong-normalization M
-- --   rewrite sym (⟦Idˢ⟧ˢ-id M) = SN-sound (reify (fundamental-lemma M (Idˢ∈ℜs _)))

-- -- strong-normalization′ : ∀ {Γ A} →
-- --                         WellFounded (_⟵_ {Γ} {A})
-- -- strong-normalization′ = strong-normalization
