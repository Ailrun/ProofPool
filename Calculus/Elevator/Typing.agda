open import Calculus.Elevator.ModeSpec

module Calculus.Elevator.Typing ℓ₁ ℓ₂ (ℳ : ModeSpec ℓ₁ ℓ₂) where
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

open import Calculus.Elevator.Syntax ℓ₁ ℓ₂ ℳ

infix   4 ⊢[_]_⦂⋆
infix   4 ⊢[_]_
infix   4 _~_⊞_
infix   4 _∤[_]_
infix   4 _⦂[_]_∈_
infix   4 _⊢[_]_⦂_

data ⊢[_]_⦂⋆ : Mode → Type → Set (ℓ₁ ⊔ ℓ₂) where
  `⊤[_]       : Bool.T (opₘ m ``⊤) →
                ---------------------
                ⊢[ m ] `⊤ ⦂⋆

  _`⊸[_]_     : ⊢[ m ] S ⦂⋆ →
                Bool.T (opₘ m ``⊸) →
                ⊢[ m ] T ⦂⋆ →
                ---------------------
                ⊢[ m ] S `⊸ T ⦂⋆

  `↑[-⇒_][_]_ : m₀ <ₘ m →
                Bool.T (opₘ m ``↑) →
                ⊢[ m₀ ] S ⦂⋆ →
                -------------------------
                ⊢[ m ] `↑[ m₀ ⇒ m ] S ⦂⋆

  `↓[-⇒_][_]_ : m <ₘ m₀ →
                Bool.T (opₘ m ``↓) →
                ⊢[ m₀ ] S ⦂⋆ →
                -------------------------
                ⊢[ m ] `↓[ m₀ ⇒ m ] S ⦂⋆

data ⊢[_]_ : Mode → Context → Set (ℓ₁ ⊔ ℓ₂) where
  []     : ----------
           ⊢[ m ] []

  _[_]∷_ : ⊢[ m₀ ] S ⦂⋆ →
           m ≤ₘ m₀ →
           ⊢[ m ] Γ →
           ----------------------------
           ⊢[ m ] (S , m₀ , true) ∷ Γ

  _[?]∷_ : ⊢[ m₀ ] S ⦂⋆ →
           ⊢[ m ] Γ →
           ----------------------------
           ⊢[ m ] (S , m₀ , false) ∷ Γ

data _is-deletable : ContextEntry → Set where
  unusable  : -----------------------------
              (S , m , false) is-deletable

  weakening : Bool.T (stₘ m ``Wk) →
              ----------------------------
              (S , m , true) is-deletable

-- extract entry-wise maps (like "_is-deletable")

data _~_⊞_ : Context → Context → Context → Set where
  []     : ------------------
           [] ~ [] ⊞ []

  _∷[_]_ : dS₀ Bool.∨ dS₁ ≡ dS →
           Bool.if stₘ m ``Co then ⊤ else dS₀ Bool.∧ dS₁ ≡ false →
           Γ ~ Γ₀ ⊞ Γ₁ →
           -----------------------------------------------------------
           (S , m , dS) ∷ Γ ~ (S , m , dS₀) ∷ Γ₀ ⊞ (S , m , dS₁) ∷ Γ₁

data _∤[_]_ : Context → Mode → Context → Set (ℓ₁ ⊔ ℓ₂) where
  []      : -------------
            [] ∤[ m ] []

  _∷≰[_]_ : dS Bool.≤ stₘ m₀ ``Wk →
            ¬ (m ≤ₘ m₀) →
            Γ ∤[ m ] Γ′ →
            -----------------------------------------------
            (S , m₀ , dS) ∷ Γ ∤[ m ] (S , m₀ , false) ∷ Γ′

  ∤∷≤[_]_ : m ≤ₘ m₀ →
            Γ ∤[ m ] Γ′ →
            --------------------------------------------
            (S , m₀ , dS) ∷ Γ ∤[ m ] (S , m₀ , dS) ∷ Γ′

data _⦂[_]_∈_ : ℕ → Mode → Type → Context → Set ℓ₁ where
  here  : All _is-deletable Γ →
          --------------------------------
          0 ⦂[ m ] S ∈ (S , m , true) ∷ Γ

  there : e is-deletable →
          x ⦂[ m ] S ∈ Γ →
          -----------------------
          suc x ⦂[ m ] S ∈ e ∷ Γ

data _⊢[_]_⦂_ : Context → Mode → Term → Type → Set (ℓ₁ ⊔ ℓ₂) where
  `unit                     : --------------------
                              Γ ⊢[ m ] `unit ⦂ `⊤

  `λ⦂-∘_                    : (S , m , true) ∷ Γ ⊢[ m ] L ⦂ T →
                              ----------------------------------
                              Γ ⊢[ m ] `λ⦂[ m ] S ∘ L ⦂ S `⊸ T

  _⊢_⦂_`$_                  : Γ ~ Γ₀ ⊞ Γ₁ →
                              Γ₀ ⊢[ m ] L ⦂ T `⊸ S →
                              ⊢[ m ] T `⊸ S ⦂⋆ →
                              Γ₁ ⊢[ m ] M ⦂ T →
                              -----------------------
                              Γ ⊢[ m ] L `$ M ⦂ S

  `lift[-⇒-]_               : Γ ⊢[ m₀ ] L ⦂ S →
                              --------------------------------------------
                              Γ ⊢[ m ] `lift[ m₀ ⇒ m ] L ⦂ `↑[ m₀ ⇒ m ] S

  _⊢`unlift[-⇒-]_⦂_         : Γ ∤[ m₀ ] Γ′ →
                              Γ′ ⊢[ m₀ ] L ⦂ `↑[ m ⇒ m₀ ] S →
                              ⊢[ m₀ ] `↑[ m ⇒ m₀ ] S ⦂⋆ →
                              ---------------------------------
                              Γ ⊢[ m ] `unlift[ m₀ ⇒ m ] L ⦂ S

  _⊢`return[-⇒-]_           : Γ ∤[ m₀ ] Γ′ →
                              Γ′ ⊢[ m₀ ] L ⦂ S →
                              ----------------------------------------------
                              Γ ⊢[ m ] `return[ m₀ ⇒ m ] L ⦂ `↓[ m₀ ⇒ m ] S

  _⊢`let-return[-⇒-]_⦂_`in_ : Γ ~ Γ₀ ⊞ Γ₁ →
                              Γ₀ ⊢[ m ] L ⦂ `↓[ m₀ ⇒ m ] T →
                              ⊢[ m ] `↓[ m₀ ⇒ m ] T ⦂⋆ →
                              (T , m₀ , true) ∷ Γ₁ ⊢[ m ] M ⦂ S →
                              ----------------------------------------------
                              Γ ⊢[ m ] `let-return[ m ⇒ m₀ ] L `in M ⦂ S

  `#_                       : x ⦂[ m ] S ∈ Γ →
                              ------------------
                              Γ ⊢[ m ] `# x ⦂ S
