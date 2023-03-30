open import Calculus.Elevator.ModeSpec

module Calculus.Elevator.Syntax ℓ₁ ℓ₂ (ℳ : ModeSpec ℓ₁ ℓ₂) where
open ModeSpec ℳ

open import Agda.Primitive
open import Data.Bool as Bool using (Bool; true; false)
open import Data.List as List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.Nat as ℕ using (ℕ; suc)
open import Data.Product as × using (_×_; _,_)
open import Data.Unit as ⊤ using (⊤)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

data Type : Set ℓ₁ where
  `⊤ : Type
  _`⊸_ : Type → Type → Type
  `↑[_⇒_] : Mode → Mode → Type → Type
  `↓[_⇒_] : Mode → Mode → Type → Type

data Term : Set ℓ₁ where
  `unit                 : Term

  `lift[_⇒_]            : Mode → Mode → Term → Term
  `unlift[_⇒_]          : Mode → Mode → Term → Term

  `return[_⇒_]          : Mode → Mode → Term → Term
  `let-return[_⇒_]_`in_ : Mode → Mode → Term → Term → Term

  `λ⦂_∘_                : Type → Term → Term
  _`$_                  : Term → Term → Term

  `#_                   : ℕ → Term

Useable = Bool
ContextEntry = Type × Mode × Useable
Context = List ContextEntry

variable
  m m₀ m₁ m₂ : Mode
  dS dS₀ dS₁ dS₂ dT dT₀ dT₁ dT₂ : Bool
  x x₀ x₁ x₂ y y₀ y₁ y₂ : ℕ
  S S₀ S₁ S₂ T T₀ T₁ T₂ : Type
  L L₀ L₁ L₂ M M₀ M₁ M₂ N N₀ N₁ N₂ : Term
  e e₀ e₁ e₂ : ContextEntry
  Γ Γ₀ Γ₁ Γ₂ Δ Δ₀ Δ₁ Δ₂ : Context

infix 4 ⊢[_]_⦂⋆
infix 4 ⊢[_]_
infix 4 _∼_⊞_
infix 4 _∤[_]_
infix 4 _⦂[_]_∈_
infix 4 _⊢[_]_⦂_

data ⊢[_]_⦂⋆ : Mode → Type → Set (ℓ₁ ⊔ ℓ₂) where
  `⊤[_]       : Bool.T (opₘ m ``⊤) →
                ---------------------
                ⊢[ m ] `⊤ ⦂⋆

  _`⊸[_]_     : ⊢[ m ] S ⦂⋆ →
                Bool.T (opₘ m ``⊸) →
                ⊢[ m ] T ⦂⋆ →
                ---------------------
                ⊢[ m ] S `⊸ T ⦂⋆

  `↑[?⇒_][_]_ : m <ₘ m₀ →
                Bool.T (opₘ m₀ ``↑) →
                ⊢[ m₀ ] S ⦂⋆ →
                -------------------------
                ⊢[ m ] `↑[ m ⇒ m₀ ] S ⦂⋆

  `↓[?⇒_][_]_ : m₀ <ₘ m →
                Bool.T (opₘ m₀ ``↓) →
                ⊢[ m₀ ] S ⦂⋆ →
                -------------------------
                ⊢[ m ] `↓[ m ⇒ m₀ ] S ⦂⋆

data ⊢[_]_ : Mode → Context → Set (ℓ₁ ⊔ ℓ₂) where
  []  : ----------
        ⊢[ m ] []

  _∷_ : ⊢[ m₀ ] S ⦂⋆ →
        ⊢[ m ] Γ →
        ----------------------------
        ⊢[ m ] (S , m₀ , false) ∷ Γ

data _is-deletable : ContextEntry → Set where
  unusable  : -----------------------------
              (S , m , false) is-deletable

  weakening : Bool.T (stₘ m ``Wk) →
              ----------------------------
              (S , m , true) is-deletable

data _∼_⊞_ : Context → Context → Context → Set where
  []     : ------------------
           [] ∼ [] ⊞ []

  _∷[_]_ : dT ≡ dT₀ Bool.∨ dT₁ →
           Bool.if stₘ m ``Co then ⊤ else dT₀ ≢ dT₁ →
           -----------------------------------------------------------
           (T , m , dT) ∷ Γ ∼ (T , m , dT₀) ∷ Γ₀ ⊞ (T , m , dT₁) ∷ Γ₁

data _∤[_]_ : Context → Mode → Context → Set (ℓ₁ ⊔ ℓ₂) where
  []      : -------------
            [] ∤[ m ] []

  _∷≰[_]_ : dT Bool.≤ stₘ m₀ ``Wk →
            ¬ (m ≤ₘ m₀) →
            ----------------------------------------------
            (T , m₀ , dT) ∷ Γ ∤[ m ] (T , m₀ , false) ∷ Γ

  ?∷≤[_]_ : m ≤ₘ m₀ →
            -------------------------------------------
            (T , m₀ , dT) ∷ Γ ∤[ m ] (T , m₀ , dT) ∷ Γ

data _⦂[_]_∈_ : ℕ → Mode → Type → Context → Set ℓ₁ where
  here  : All _is-deletable Γ →
          --------------------------------
          0 ⦂[ m ] T ∈ (T , m , true) ∷ Γ

  there : e is-deletable →
          x ⦂[ m ] T ∈ Γ →
          -----------------------
          suc x ⦂[ m ] T ∈ e ∷ Γ

data _⊢[_]_⦂_ : Context → Mode → Term → Type → Set (ℓ₁ ⊔ ℓ₂) where
  `unit                     : --------------------
                              Γ ⊢[ m ] `unit ⦂ `⊤

  `λ⦂_∘_                    : (S , m , true) ∷ Γ ⊢[ m ] L ⦂ T →
                              ----------------------------------
                              Γ ⊢[ m ] `λ⦂ S ∘ L ⦂ S `⊸ T

  _⊢_⦂_`$_                  : Γ ∼ Γ₀ ⊞ Γ₁ →
                              ⊢[ m ] T `⊸ S ⦂⋆ →
                              Γ₀ ⊢[ m ] L ⦂ T `⊸ S →
                              Γ₁ ⊢[ m ] M ⦂ T →
                              -----------------------
                              Γ ⊢[ m ] L `$ M ⦂ S

  _⊢`lift[?⇒?]              : Γ ∤[ m₀ ] Γ₀ →
                              Γ₀ ⊢[ m₀ ] L ⦂ S →
                              --------------------------------------------
                              Γ ⊢[ m ] `lift[ m ⇒ m₀ ] L ⦂ `↑[ m ⇒ m₀ ] S

  _⊢`unlift[?⇒?]_⦂_         : Γ ∤[ m₀ ] Γ₀ →
                              Γ₀ ⊢[ m₀ ] L ⦂ `↑[ m ⇒ m₀ ] S →
                              ⊢[ m₀ ] `↑[ m ⇒ m₀ ] S ⦂⋆ →
                              ---------------------------------
                              Γ ⊢[ m ] `unlift[ m₀ ⇒ m ] L ⦂ S

  _⊢`return[?⇒?]            : Γ ∤[ m₀ ] Γ₀ →
                              Γ₀ ⊢[ m₀ ] L ⦂ S →
                              ----------------------------------------------
                              Γ ⊢[ m ] `return[ m₀ ⇒ m ] L ⦂ `↓[ m₀ ⇒ m ] S

  _⊢`let-return[?⇒?]_⦂_`in_ : Γ ∼ Γ₀ ⊞ Γ₁ →
                              Γ₀ ⊢[ m ] L ⦂ `↓[ m₀ ⇒ m ] T →
                              ⊢[ m ] `↓[ m₀ ⇒ m ] T ⦂⋆ →
                              (T , m₀ , true) ∷ Γ₁ ⊢[ m ] M ⦂ S →
                              ----------------------------------------------
                              Γ ⊢[ m ] `let-return[ m ⇒ m₀ ] L `in M ⦂ S

  `#_                       : x ⦂[ m ] S ∈ Γ →
                              ------------------
                              Γ ⊢[ m ] `# x ⦂ S

data WeakNorm : Term → Set (ℓ₁ ⊔ ℓ₂)
data WeakNeut : Term → Set (ℓ₁ ⊔ ℓ₂)
data TermWORedex[≥_] : Mode → Term → Set (ℓ₁ ⊔ ℓ₂)

data WeakNorm where
data WeakNeut where
data TermWORedex[≥_] where

data _⟶_ : Term → Term → Set (ℓ₁ ⊔ ℓ₂)

data _⟶[≥_]_ : Term → Mode → Term → Set (ℓ₁ ⊔ ℓ₂)

data _⟶_ where
data _⟶[≥_]_ where
