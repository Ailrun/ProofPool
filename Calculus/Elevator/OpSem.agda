{-# OPTIONS --safe --without-K #-}
open import Calculus.Elevator.ModeSpec

module Calculus.Elevator.OpSem ℓ₁ ℓ₂ (ℳ : ModeSpec ℓ₁ ℓ₂) where
open ModeSpec ℳ

open import Agda.Primitive
open import Data.Bool as Bool using (Bool; true; false)
open import Data.Empty as ⊥ using (⊥)
open import Data.List as List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.Nat as ℕ using (ℕ; suc; _+_)
open import Data.Product as × using (_×_; _,_; ∃; ∃₂)
open import Data.Unit as ⊤ using (⊤; tt)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; _≢_)

open import Calculus.Elevator.Syntax ℓ₁ ℓ₂ ℳ

data WeakNorm : Term → Set (ℓ₁ ⊔ ℓ₂)
data WeakNeut : Term → Set (ℓ₁ ⊔ ℓ₂)
data TermWORedex[_≤] : Mode → Term → Set (ℓ₁ ⊔ ℓ₂)

data WeakNorm where
  `unit                 : WeakNorm `unit
  `lift[_⇒_]            : ∀ m₀ m₁ → TermWORedex[ m₁ ≤] L → WeakNorm (`lift[ m₀ ⇒ m₁ ] L)
  `return[_⇒_]          : ∀ m₀ m₁ → WeakNorm L → WeakNorm (`return[ m₀ ⇒ m₁ ] L)
  `λ⦂[_]_∘_             : ∀ m S L → WeakNorm (`λ⦂[ m ] S ∘ L)

  `neut                 : WeakNeut L → WeakNorm L

data WeakNeut where
  `#_                   : ∀ x → WeakNeut (`# x)
  `unlift[_⇒_]          : ∀ m₀ m₁ → WeakNeut L → WeakNeut (`unlift[ m₀ ⇒ m₁ ] L)
  `let-return[_⇒_]_`in_ : ∀ m₀ m₁ → WeakNeut L → ∀ N → WeakNeut (`let-return[ m₀ ⇒ m₁ ] L `in N)
  _`$_                  : WeakNeut L → WeakNorm M → WeakNeut (L `$ M)

≢lift[-⇒-] : Term → Set
≢lift[-⇒-] `unit = ⊤
≢lift[-⇒-] (`lift[ m₀ ⇒ m₁ ] L) = ⊥
≢lift[-⇒-] (`unlift[ m₀ ⇒ m₁ ] L) = ⊤
≢lift[-⇒-] (`return[ m₀ ⇒ m₁ ] L) = ⊤
≢lift[-⇒-] (`let-return[ m₀ ⇒ m₁ ] L `in M) = ⊤
≢lift[-⇒-] (`λ⦂[ m ] S ∘ L) = ⊤
≢lift[-⇒-] (L `$ M) = ⊤
≢lift[-⇒-] (`# x) = ⊤

≢lift[-⇒-]? : (L : Term) → Dec (≢lift[-⇒-] L)
≢lift[-⇒-]? `unit = yes tt
≢lift[-⇒-]? (`lift[ m₀ ⇒ m₁ ] L) = no (λ x → x)
≢lift[-⇒-]? (`unlift[ m₀ ⇒ m₁ ] L) = yes tt
≢lift[-⇒-]? (`return[ m₀ ⇒ m₁ ] L) = yes tt
≢lift[-⇒-]? (`let-return[ m₀ ⇒ m₁ ] L `in L₁) = yes tt
≢lift[-⇒-]? (`λ⦂[ m ] S ∘ L) = yes tt
≢lift[-⇒-]? (L `$ L₁) = yes tt
≢lift[-⇒-]? (`# x) = yes tt

¬≢lift[-⇒-]⇒≡lift[-⇒-] : (L : Term) → ¬ (≢lift[-⇒-] L) → ∃ (λ m₀ → ∃₂ (λ m₁ L′ → L ≡ `lift[ m₀ ⇒ m₁ ] L′))
¬≢lift[-⇒-]⇒≡lift[-⇒-] `unit ¬≢lift with () ← ¬≢lift tt
¬≢lift[-⇒-]⇒≡lift[-⇒-] (`lift[ m₀ ⇒ m₁ ] L) ¬≢lift = _ , _ , _ , refl
¬≢lift[-⇒-]⇒≡lift[-⇒-] (`unlift[ m₀ ⇒ m₁ ] L) ¬≢lift with () ← ¬≢lift tt
¬≢lift[-⇒-]⇒≡lift[-⇒-] (`return[ m₀ ⇒ m₁ ] L) ¬≢lift with () ← ¬≢lift tt
¬≢lift[-⇒-]⇒≡lift[-⇒-] (`let-return[ m₀ ⇒ m₁ ] L `in L₁) ¬≢lift with () ← ¬≢lift tt
¬≢lift[-⇒-]⇒≡lift[-⇒-] (`λ⦂[ m ] S ∘ L) ¬≢lift with () ← ¬≢lift tt
¬≢lift[-⇒-]⇒≡lift[-⇒-] (L `$ L₁) ¬≢lift with () ← ¬≢lift tt
¬≢lift[-⇒-]⇒≡lift[-⇒-] (`# x) ¬≢lift with () ← ¬≢lift tt

data TermWORedex[_≤] where
  `unit                 : TermWORedex[ m ≤] `unit

  `lift[_⇒_]            : ∀ m₀ m₁ → TermWORedex[ m ≤] L → TermWORedex[ m ≤] (`lift[ m₀ ⇒ m₁ ] L)
  `unlift[≰_⇒_]         : ¬ (m ≤ₘ m₀) → ∀ m₁ → TermWORedex[ m ≤] L → TermWORedex[ m ≤] (`unlift[ m₀ ⇒ m₁ ] L)
  `unlift[≤_⇒_]         : m ≤ₘ m₀ → ∀ m₁ → WeakNorm L → ≢lift[-⇒-] L → TermWORedex[ m ≤] (`unlift[ m₀ ⇒ m₁ ] L)

  `return[≰_⇒_]         : ¬ (m ≤ₘ m₀) → ∀ m₁ → TermWORedex[ m ≤] L → TermWORedex[ m ≤] (`return[ m₀ ⇒ m₁ ] L)
  `return[≤_⇒_]         : m ≤ₘ m₀ → ∀ m₁ → WeakNorm L → TermWORedex[ m ≤] (`return[ m₀ ⇒ m₁ ] L)
  `let-return[_⇒_]_`in_ : ∀ m₀ m₁ → TermWORedex[ m ≤] L → TermWORedex[ m ≤] M → TermWORedex[ m ≤] (`let-return[ m₀ ⇒ m₁ ] L `in M)

  `λ⦂[_]_∘_             : ∀ m₀ S → TermWORedex[ m ≤] L → TermWORedex[ m ≤] (`λ⦂[ m₀ ] S ∘ L)
  _`$_                  : TermWORedex[ m ≤] L → TermWORedex[ m ≤] M → TermWORedex[ m ≤] (L `$ M)

  `#_                   : ∀ x → TermWORedex[ m ≤] (`# x)

infixr 25 wk[_↑_]_
infixr 25 wk_
infixr 25 [_/[_]_]_

wk[_↑_]_ : ℕ → ℕ → Term → Term
wk[ n ↑ x ] `unit = `unit
wk[ n ↑ x ] `lift[ m₀ ⇒ m₁ ] L = `lift[ m₀ ⇒ m₁ ] (wk[ n ↑ x ] L)
wk[ n ↑ x ] `unlift[ m₀ ⇒ m₁ ] L = `unlift[ m₀ ⇒ m₁ ] (wk[ n ↑ x ] L)
wk[ n ↑ x ] `return[ m₀ ⇒ m₁ ] L = `return[ m₀ ⇒ m₁ ] (wk[ n ↑ x ] L)
wk[ n ↑ x ] (`let-return[ m₀ ⇒ m₁ ] L `in M) = `let-return[ m₀ ⇒ m₁ ] wk[ n ↑ x ] L `in wk[ n ↑ suc x ] M
wk[ n ↑ x ] (`λ⦂[ m ] S ∘ L) = `λ⦂[ m ] S ∘ wk[ n ↑ suc x ] L
wk[ n ↑ x ] (L `$ M) = wk[ n ↑ x ] L `$ wk[ n ↑ x ] M
wk[ n ↑ x ] (`# y)
  with y ℕ.≥? x
...  | no  _ = `# y
...  | yes _ = `# (n + y)

wk_ = wk[ 1 ↑ 0 ]_

[_/[_]_]_ : Term → Mode → ℕ → Term → Term
[ L /[ m ] x ] `unit = `unit
[ L /[ m ] x ] `lift[ m₀ ⇒ m₁ ] M = `lift[ m₀ ⇒ m₁ ] ([ L /[ m ] x ] M)
[ L /[ m ] x ] `unlift[ m₀ ⇒ m₁ ] M
  with m₀ ≤?ₘ m
...  | yes _ = `unlift[ m₀ ⇒ m₁ ] ([ L /[ m ] x ] M)
...  | no  _ = `unlift[ m₀ ⇒ m₁ ] ([ `unlift[ m₀ ⇒ m₁ ] `unit /[ m ] x ] M) -- strengthening substitution (note that the argument is ill-typed)
[ L /[ m ] x ] `return[ m₀ ⇒ m₁ ] M
  with m₀ ≤?ₘ m
...  | yes _ = `return[ m₀ ⇒ m₁ ] ([ L /[ m ] x ] M)
...  | no  _ = `return[ m₀ ⇒ m₁ ] ([ `unlift[ m₀ ⇒ m₁ ] `unit /[ m ] x ] M) -- strengthening substitution
[ L /[ m ] x ] (`let-return[ m₀ ⇒ m₁ ] M `in N) = `let-return[ m₀ ⇒ m₁ ] [ L /[ m ] x ] M `in [ wk L /[ m ] suc x ] N
[ L /[ m ] x ] (`λ⦂[ m′ ] S ∘ M) = `λ⦂[ m′ ] S ∘ [ wk L /[ m ] suc x ] M
[ L /[ m ] x ] (M `$ N) = [ L /[ m ] x ] M `$ [ L /[ m ] x ] N
[ L /[ m ] x ] (`# y)
  with y ℕ.≥? x
...  | no  _ = `# y
...  | yes _
    with y ℕ.≟ x
...    | no  _ = `# (ℕ.pred y)
...    | yes _ = L

infix   4 _⟶_
infix   4 _⟶[_≤]_

data _⟶_ : Term → Term → Set (ℓ₁ ⊔ ℓ₂)

data _⟶[_≤]_ : Term → Mode → Term → Set (ℓ₁ ⊔ ℓ₂)

data _⟶_ where
  ξ-`lift[-⇒-]            : L ⟶[ m₁ ≤] L′ →
                            -----------------------------------------
                            `lift[ m₀ ⇒ m₁ ] L ⟶ `lift[ m₀ ⇒ m₁ ] L′

  ξ-`unlift[-⇒-]          : L ⟶ L′ →
                            ---------------------------------------------
                            `unlift[ m₀ ⇒ m₁ ] L ⟶ `unlift[ m₀ ⇒ m₁ ] L′

  β-↑                     : TermWORedex[ m₁ ≤] L →
                            --------------------------------------------
                            `unlift[ m₁ ⇒ m₀ ] (`lift[ m₀ ⇒ m₁ ] L) ⟶ L


  ξ-`return[-⇒-]          : L ⟶ L′ →
                            ---------------------------------------------
                            `return[ m₀ ⇒ m₁ ] L ⟶ `return[ m₀ ⇒ m₁ ] L′

  ξ-`let-return[-⇒-]_`in- : L ⟶ L′ →
                            -----------------------------------------------------------------
                            `let-return[ m₀ ⇒ m₁ ] L `in M ⟶ `let-return[ m₀ ⇒ m₁ ] L′ `in M

  β-↓                     : WeakNorm L →
                            ------------------------------------------------------------------------
                            `let-return[ m₁ ⇒ m₀ ] (`return[ m₀ ⇒ m₁ ] L) `in M ⟶ [ L /[ m₀ ] 0 ] M


  ξ-_`$?                  : L ⟶ L′ →
                            -----------------
                            L `$ M ⟶ L′ `$ M

  ξ-!_`$_                 : WeakNorm L →
                            M ⟶ M′ →
                            -----------------
                            L `$ M ⟶ L `$ M′

  β-⊸                     : -----------------------------------------
                            (`λ⦂[ m ] S ∘ L) `$ M ⟶ [ M /[ m ] 0 ] L

data _⟶[_≤]_ where
  ξ-`lift[-⇒-]             : L ⟶[ m ≤] L′ →
                             -----------------------------------------------
                             `lift[ m₀ ⇒ m₁ ] L ⟶[ m ≤] `lift[ m₀ ⇒ m₁ ] L′

  ξ-`unlift[≰_⇒-]          : ¬ (m ≤ₘ m₀) →
                             L ⟶[ m ≤] L′ →
                             ---------------------------------------------------
                             `unlift[ m₀ ⇒ m₁ ] L ⟶[ m ≤] `unlift[ m₀ ⇒ m₁ ] L′

  ξ-`unlift[≤_⇒-]          : m ≤ₘ m₀ →
                             L ⟶ L′ →
                             ---------------------------------------------------
                             `unlift[ m₀ ⇒ m₁ ] L ⟶[ m ≤] `unlift[ m₀ ⇒ m₁ ] L′

  β-↑                      : m ≤ₘ m₁ →
                             TermWORedex[ m₁ ≤] L →
                             --------------------------------------------------
                             `unlift[ m₁ ⇒ m₀ ] (`lift[ m₀ ⇒ m₁ ] L) ⟶[ m ≤] L


  ξ-`return[≰_⇒-]          : ¬ (m ≤ₘ m₀) →
                             L ⟶[ m ≤] L′ →
                             ---------------------------------------------------
                             `return[ m₀ ⇒ m₁ ] L ⟶[ m ≤] `return[ m₀ ⇒ m₁ ] L′

  ξ-`return[≤_⇒-]          : m ≤ₘ m₀ →
                             L ⟶ L′ →
                             ---------------------------------------------------
                             `return[ m₀ ⇒ m₁ ] L ⟶[ m ≤] `return[ m₀ ⇒ m₁ ] L′

  ξ-`let-return[-⇒-]_`in?  : L ⟶[ m ≤] L′ →
                             -----------------------------------------------------------------------
                             `let-return[ m₀ ⇒ m₁ ] L `in M ⟶[ m ≤] `let-return[ m₀ ⇒ m₁ ] L′ `in M

  ξ-`let-return[-⇒-]!_`in_ : TermWORedex[ m ≤] L →
                             M ⟶[ m ≤] M′ →
                             -----------------------------------------------------------------------
                             `let-return[ m₀ ⇒ m₁ ] L `in M ⟶[ m ≤] `let-return[ m₀ ⇒ m₁ ] L `in M′


  ξ-_`$?                   : L ⟶[ m ≤] L′ →
                             -----------------------
                             L `$ M ⟶[ m ≤] L′ `$ M

  ξ-!_`$_                  : TermWORedex[ m ≤] L →
                             M ⟶[ m ≤] M′ →
                             -----------------------
                             L `$ M ⟶[ m ≤] L `$ M′

  ξ-`λ⦂[-]-∘_              : L ⟶[ m ≤] L′ →
                             -----------------------------------------
                             `λ⦂[ m₀ ] S ∘ L ⟶[ m ≤] `λ⦂[ m₀ ] S ∘ L′
