{-# OPTIONS --safe #-}
open import Calculus.Elevator.ModeSpec

module Calculus.Elevator.Algorithmic {ℓ₁ ℓ₂} (ℳ : ModeSpec ℓ₁ ℓ₂) where
open ModeSpec ℳ

open import Agda.Primitive
open import Data.Bool as Bool using (true; false)
open import Data.List as List using ([]; _∷_)
open import Data.List.Relation.Unary.All as All using (All)
open import Data.Nat as ℕ using (ℕ; suc)
open import Data.Product as × using (_×_; _,_; ∃)
open import Relation.Nullary using (yes; no)

open import Calculus.Elevator.Syntax ℳ
open import Calculus.Elevator.Typing ℳ

infix   6 _drop[_]⇒
infix   4 _⦂[_]_∈_⇒_
infix   4 _⊢[_]_⦂_⇒_
infix   4 _A⊢[_]_⦂_
infix   4 _[_]is-used-by_
infix   4 _is-all-used-by_

ContextDelta = Context

_drop[_]⇒ : Context → Mode → Context
[]                 drop[ m ]⇒ = []
((S , m₀ , d) ∷ Γ) drop[ m ]⇒
  with m ≤?ₘ m₀
...  | yes _ = (S , m₀ , d) ∷ Γ drop[ m ]⇒
...  | no  _ = (S , m₀ , false) ∷ Γ drop[ m ]⇒

unused : Context → ContextDelta
unused = List.map (λ{ (T , m₀ , _) → (T , m₀ , false) })

data _[_]is-used-by_ : Useable → Mode → Useable → Set where
  used      : --------------------------
              true [ m ]is-used-by true

  unusable  : ----------------------------
              false [ m ]is-used-by false

  weakening : Bool.T (stₘ m ``Wk) →
              ---------------------------
              true [ m ]is-used-by false

data _is-all-used-by_ : Context → ContextDelta → Set where
  []  : ------------------
        [] is-all-used-by []

  _∷_ : d [ m ]is-used-by d′ →
        Γ is-all-used-by Δ →
        ------------------------------------------------
        (S , m , d) ∷ Γ is-all-used-by (S , m , d′) ∷ Δ

data _⦂[_]_∈_⇒_ : ℕ → Mode → Type → Context → ContextDelta → Set where
  here  : ------------------------------------------------------------
          0 ⦂[ m ] S ∈ (S , m , true) ∷ Γ ⇒ (S , m , true) ∷ unused Γ

  there : x ⦂[ m ] S ∈ Γ ⇒ Δ →
          ----------------------------------------------------------
          suc x ⦂[ m ] S ∈ (T , m₀ , dT) ∷ Γ ⇒ (T , m₀ , false) ∷ Δ

data _⊢[_]_⦂_⇒_ : Context → Mode → Term → Type → Context → Set (ℓ₁ ⊔ ℓ₂) where
  `unit                     : -------------------------------
                              Γ ⊢[ m ] `unit ⦂ `⊤ ⇒ unused Γ

  `λ⦂[_]-∘_                 : true [ m ]is-used-by d →
                              (S , m , true) ∷ Γ ⊢[ m ] L ⦂ T ⇒ (S , m , d) ∷ Δ →
                              ----------------------------------------------------
                              Γ ⊢[ m ] `λ⦂[ m ] S ∘ L ⦂ S `⊸ T ⇒ Δ

  _⊢_⦂_`$_                  : Δ ~ Δ₀ ⊞ Δ₁ →
                              Γ ⊢[ m ] L ⦂ T `⊸ S ⇒ Δ₀ →
                              ⊢[ m ] T `⊸ S ⦂⋆ →
                              Γ ⊢[ m ] M ⦂ T ⇒ Δ₁ →
                              ---------------------------
                              Γ ⊢[ m ] L `$ M ⦂ S ⇒ Δ

  `lift[-⇒-]_               : Γ ⊢[ m₀ ] L ⦂ S ⇒ Δ →
                              ------------------------------------------------
                              Γ ⊢[ m ] `lift[ m₀ ⇒ m ] L ⦂ `↑[ m₀ ⇒ m ] S ⇒ Δ

  `unlift[-⇒-]_⦂_           : Γ drop[ m₀ ]⇒ ⊢[ m₀ ] L ⦂ `↑[ m ⇒ m₀ ] S ⇒ Δ →
                              ⊢[ m₀ ] `↑[ m ⇒ m₀ ] S ⦂⋆ →
                              -------------------------------------
                              Γ ⊢[ m ] `unlift[ m₀ ⇒ m ] L ⦂ S ⇒ Δ

  `return[-⇒-]_             : Γ drop[ m₀ ]⇒ ⊢[ m₀ ] L ⦂ S ⇒ Δ →
                              --------------------------------------------------
                              Γ ⊢[ m ] `return[ m₀ ⇒ m ] L ⦂ `↓[ m₀ ⇒ m ] S ⇒ Δ

  _⊢`let-return[-⇒_]_⦂_`in_ : Δ ~ Δ₀ ⊞ Δ₁ →
                              true [ m₀ ]is-used-by d →
                              Γ ⊢[ m ] L ⦂ `↓[ m₀ ⇒ m ] T ⇒ Δ₀ →
                              ⊢[ m ] `↓[ m₀ ⇒ m ] T ⦂⋆ →
                              (T , m₀ , true) ∷ Γ ⊢[ m ] M ⦂ S ⇒ (T , m₀ , d) ∷ Δ₁ →
                              -------------------------------------------------------
                              Γ ⊢[ m ] `let-return[ m ⇒ m₀ ] L `in M ⦂ S ⇒ Δ

  `#_                       : x ⦂[ m ] S ∈ Γ ⇒ Γ′ →
                              -----------------------
                              Γ ⊢[ m ] `# x ⦂ S ⇒ Γ′

_A⊢[_]_⦂_ : Context → Mode → Term → Type → Set (ℓ₁ ⊔ ℓ₂)
Γ A⊢[ m ] L ⦂ S = ∃ (λ Δ → Γ ⊢[ m ] L ⦂ S ⇒ Δ × Γ is-all-used-by Δ)
