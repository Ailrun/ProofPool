module Calculus.LinearSide.Rules where

open import Agda.Builtin.FromNat
open import Data.Nat hiding (zero; suc; _/_)
open import Data.Fin using (Fin; zero; suc)
import Data.Fin.Literals as Fin
open import Data.Fin.Substitution
open import Data.Unit hiding (_≟_)
open import Data.Vec using (Vec; _∷_)
import Data.Vec as Vec
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise)
import Data.Vec.Relation.Unary.All as VecAll
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Calculus.LinearSide.Syntax
open import Calculus.LinearSide.Syntax.Properties

infixr 4 _s⊢ₗ_⦂_
infixr 4 _⊢ₗ_⦂_
infixr 4 _unused-in_
infixr 4 _linear-in_
infixr 4 _↝ₗ_

infixr 9 λₗ*∘ₗ_∣ₗ_
infixr 9 λₗ*∘ₗ_
infixl 9 _$∘ₗ∅_
infixl 9 ∅_$∘ₗ_
infixr 9 let-bangₗ∅_inₗ_
infixr 9 let-bangₗ_inₗ∅_
infixr 9 let-bangₗ_inₗ?
infixr 9 _$∘ₗ?
infixr 9 !$∘ₗ_

data _unused-in_ : Fin n → 𝕄 n → Set where
  varₗ           : x ≢ y →
                   ---------------------
                   x unused-in (varₗ y)

  λₗ*∘ₗ_         : suc x unused-in M →
                   ------------------------
                   x unused-in (λₗ T ∘ₗ M)

  _$∘ₗ_          : x unused-in M →
                   x unused-in N →
                   ----------------------
                   x unused-in (M $∘ₗ N)

  bangₗ          : x unused-in M →
                   ----------------------
                   x unused-in (bangₗ M)

  let-bangₗ_inₗ_ : x unused-in M →
                   (suc x) unused-in N →
                   --------------------------------
                   x unused-in (let-bangₗ M inₗ N)

data _linear-in_ : Fin n → 𝕄 n → Set where
  varₗ            : x ≡ y →
                    ---------------------
                    x linear-in (varₗ y)

  λₗ*∘ₗ_          : suc x linear-in M →
                    ------------------------
                    x linear-in (λₗ T ∘ₗ M)

  _$∘ₗ∅_          : x linear-in M →
                    x unused-in N →
                    ----------------------
                    x linear-in (M $∘ₗ N)

  ∅_$∘ₗ_          : x unused-in M →
                    x linear-in N →
                    ----------------------
                    x linear-in (M $∘ₗ N)

  let-bangₗ_inₗ∅_ : x linear-in M →
                    (suc x) unused-in N →
                    --------------------------------
                    x linear-in (let-bangₗ M inₗ N)

  let-bangₗ∅_inₗ_ : x unused-in M →
                    (suc x) linear-in N →
                    --------------------------------
                    x linear-in (let-bangₗ M inₗ N)

data _⊢ₗ_⦂_ {n} (Γ : ℂ n) : 𝕄 n → 𝕋 → Set where
  varₗ           : Vec.lookup Γ x ≡ T →
                   ---------------------
                   Γ ⊢ₗ varₗ x ⦂ T

  λₗ*∘ₗ_∣ₗ_      : T ∷ Γ ⊢ₗ M ⦂ U →
                   0 linear-in M →
                   ------------------------
                   Γ ⊢ₗ λₗ T ∘ₗ M ⦂ T ⊸ₗ U

  _$∘ₗ_          : Γ ⊢ₗ M ⦂ T ⊸ₗ U →
                   Γ ⊢ₗ N ⦂ T →
                   ------------------
                   Γ ⊢ₗ M $∘ₗ N ⦂ U

  bangₗ          : Γ ⊢ₗ M ⦂ T →
                   --------------------
                   Γ ⊢ₗ bangₗ M ⦂ !ₗ T

  let-bangₗ_inₗ_ : Γ ⊢ₗ M ⦂ !ₗ T →
                   T ∷ Γ ⊢ₗ N ⦂ U →
                   ---------------------------
                   Γ ⊢ₗ let-bangₗ M inₗ N ⦂ U

_s⊢ₗ_⦂_ : ℂ n → Sub 𝕄 m n → ℂ m → Set
Δ s⊢ₗ σ ⦂ Γ = Pointwise (Δ ⊢ₗ_⦂_) σ Γ

data Valueₗ : 𝕄 n → Set where
  λₗ?∘ₗ? : -------------------
           Valueₗ (λₗ T ∘ₗ M)

  bangₗ  : Valueₗ M →
           -----------------
           Valueₗ (bangₗ M)

data _↝ₗ_ : 𝕄 n → 𝕄 n → Set where
  _$∘ₗ?          : M ↝ₗ M′ →
                   --------------------
                   M $∘ₗ N ↝ₗ M′ $∘ₗ N

  !$∘ₗ_          : N ↝ₗ N′ →
                   ----------------------------------------
                   (λₗ T ∘ₗ M) $∘ₗ N ↝ₗ (λₗ T ∘ₗ M) $∘ₗ N′

  bangₗ          : M ↝ₗ M′ →
                   --------------------
                   bangₗ M ↝ₗ bangₗ M′

  let-bangₗ_inₗ? : M ↝ₗ M′ →
                   ----------------------------------------
                   let-bangₗ M inₗ N ↝ₗ let-bangₗ M′ inₗ N

  β-⊸ₗ           : Valueₗ N →
                   -------------------------------
                   (λₗ T ∘ₗ M) $∘ₗ N ↝ₗ M / sub N

  β-!ₗ           : Valueₗ M →
                   ---------------------------------------
                   let-bangₗ (bangₗ M) inₗ N ↝ₗ N / sub M
