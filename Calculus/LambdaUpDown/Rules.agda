{-# OPTIONS --without-K --safe #-}
module Calculus.LambdaUpDown.Rules where

open import Agda.Primitive
open import Data.Empty
open import Data.List
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Unit hiding (_≟_)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

open import Calculus.LambdaUpDown.Syntax
open Variable

------------------------------------------------------------
-- Mode ordering
------------------------------------------------------------

data _≤M_ : Mode → Mode → Set where
  refl      : md ≤M md
  prog<code : prog ≤M code

_<M_ : Mode → Mode → Set
x <M y = (x ≤M y) × (x ≢ y)

_≤M?_ : ∀ (md md′ : Mode) → Dec (md ≤M md′)
prog ≤M? prog = yes refl
prog ≤M? code = yes prog<code
code ≤M? prog = no (λ ())
code ≤M? code = yes refl

------------------------------------------------------------
-- Operations
------------------------------------------------------------

infix 4.5 _∣c≤

_∣c≤ : Ctx → Ctx
[]             ∣c≤ = []
((md , S) ∷ Γ) ∣c≤
  with code ≤M? md
...  | yes _       = (md , S) ∷ (Γ ∣c≤)
...  | no  _       = Γ ∣c≤

infix 25 wk[_↑_]_
infix 25 wk_
infix 25 [_//[_]_]_
infix 25 co[_∣c≤↑_]_
infix 25 co[_∣c≤]_

wk[_↑_]_ : ℕ → ℕ → Term → Term
wk[ n ↑ x ] (lift M)         = lift (wk[ n ↑ x ] M)
wk[ n ↑ x ] (unlift M)       = unlift (wk[ n ↑ x ] M)
wk[ n ↑ x ] (return M)       = return (wk[ n ↑ x ] M)
wk[ n ↑ x ] (let-return M N) = let-return (wk[ n ↑ x ] M) (wk[ n ↑ suc x ] M)
wk[ n ↑ x ] (# y)
  with x ≤? y
...  | yes _                 = # (n + y)
...  | no  _                 = # y
wk[ n ↑ x ] (Λ S ∙ M)        = Λ S ∙ (wk[ n ↑ suc x ] M)
wk[ n ↑ x ] (M $$ N)         = wk[ n ↑ x ] M $$ wk[ n ↑ x ] N
wk[ n ↑ x ] unit             = unit

wk_ = wk[ 1 ↑ 0 ]_

[_//[_]_]_ : Term → Mode → ℕ → Term → Term
[ M //[ md   ] x ] (lift N)         = lift ([ M //[ md ] x ] N)
[ M //[ prog ] x ] (unlift N)       = unlift N
[ M //[ code ] x ] (unlift N)       = unlift ([ M //[ code ] x ] N)
[ M //[ prog ] x ] (return N)       = return N
[ M //[ code ] x ] (return N)       = return ([ M //[ code ] x ] N)
[ M //[ md   ] x ] (let-return N L) = let-return ([ M //[ md ] x ] N) ([ wk M //[ md ] suc x ] L)
[ M //[ md   ] x ] (# y)
  with x ≟ y
...  | yes _                        = M
...  | no  _
    with x <? y
...    | yes _                      = # (pred y)
...    | no  _                      = # y
[ M //[ md   ] x ] (Λ S ∙ N)        = Λ S ∙ [ wk M //[ md ] suc x ] N
[ M //[ md   ] x ] (N $$ L)         = [ M //[ md ] x ] N $$ [ M //[ md ] x ] L
[ M //[ md   ] x ] unit             = unit

ill-typed : Term
ill-typed = unlift unit

co[_∣c≤↑_]_ : Ctx → ℕ → Term → Term
co[ []           ∣c≤↑ x ] M = M
co[ (md , S) ∷ Γ ∣c≤↑ x ] M
  with code ≤M? md
...  | yes _ = co[ Γ ∣c≤↑ suc x ] M
...  | no  _ = co[ Γ ∣c≤↑ x ] ([ ill-typed //[ md ] x ] M)

co[_∣c≤]_ : Ctx → Term → Term
co[_∣c≤]_ = co[_∣c≤↑ 0 ]_

------------------------------------------------------------
-- Well-modedness
------------------------------------------------------------

infix 4 ⊢[_]_⦂ty
infix 4 ⊢ᶜ_⦂ty
infix 4 ⊢ᵖ_⦂ty

data ⊢[_]_⦂ty : Mode → Type → Set

⊢ᶜ_⦂ty = ⊢[ code ]_⦂ty
⊢ᵖ_⦂ty = ⊢[ prog ]_⦂ty

data ⊢[_]_⦂ty where
  ↑_  : ⊢ᵖ S ⦂ty →
        -----------------
        ⊢ᶜ ↑ S ⦂ty

  ↓_  : ⊢ᶜ S ⦂ty →
        -----------------
        ⊢ᵖ ↓ S ⦂ty

  _⇒_ : ⊢[ md ] S ⦂ty →
        ⊢[ md ] T ⦂ty →
        -----------------
        ⊢[ md ] S ⇒ T ⦂ty

  Top : -----------------
        ⊢[ md ] Top ⦂ty

data ⊢[_]_⦂ctx : Mode → Ctx → Set where
  []  : ----------------
        ⊢[ md ] [] ⦂ctx

  _∷_ : ⊢[ md′ ] S ⦂ty →
        ⊢[ md ] Γ ⦂ctx →
        md ≤M md′ →
        ---------------------------
        ⊢[ md ] (md′ , S) ∷ Γ ⦂ctx

------------------------------------------------------------
-- Context membership
------------------------------------------------------------

infix 4 _⦂_∈_
infix 4 _⦂[_]_∈_
infix 4 _⦂ᶜ_∈_
infix 4 _⦂ᵖ_∈_

data _⦂_∈_ {ℓ : Level} {A : Set ℓ} : ℕ → A → List A → Set ℓ where
  here  : ∀ {a b : A} {cs : List A} →
          a ≡ b →
          ---------------
          0 ⦂ a ∈ b ∷ cs
  
  there : ∀ {a b : A} {cs : List A} →
          x ⦂ a ∈ cs →
          --------------------
          suc x ⦂ a ∈ b ∷ cs

_⦂[_]_∈_ : ℕ → Mode → Type → Ctx → Set
x ⦂[ md ] a ∈ cs = _⦂_∈_ x (md , a) cs

infix 4 _⊢[_]_⦂_
infix 4 _⊢ᶜ_⦂_
infix 4 _⊢ᵖ_⦂_

data _⊢[_]_⦂_ : Ctx → Mode → Term → Type → Set

_⊢ᶜ_⦂_ = _⊢[ code ]_⦂_
_⊢ᵖ_⦂_ = _⊢[ prog ]_⦂_

data _⊢[_]_⦂_ where
  lift       : Γ ⊢ᵖ M ⦂ S →
               -------------------------
               Γ ⊢ᶜ lift M ⦂ ↑ S

  unlift     : Γ ∣c≤ ⊢ᶜ co[ Γ ∣c≤] M ⦂ ↑ S →
               -------------------------------------
               Γ ⊢ᵖ unlift M ⦂ S

  return     : Γ ∣c≤ ⊢ᶜ co[ Γ ∣c≤] M ⦂ S →
               -----------------------------------
               Γ ⊢ᵖ return M ⦂ ↓ S

  let-return : Γ ⊢ᵖ M ⦂ ↓ T →
               ⊢ᶜ T ⦂ty →
               T ∷ᶜ Γ ⊢ᵖ N ⦂ S →
               ---------------------------------
               Γ ⊢ᵖ let-return M N ⦂ S

  #_         : x ⦂[ md ] S ∈ Γ →
               -------------------------
               Γ ⊢[ md ] # x ⦂ S

  Λ_∙_       : S ≡ S′ →
               (md , S′) ∷ Γ ⊢[ md ] M ⦂ T →
               ----------------------------------
               Γ ⊢[ md ] Λ S′ ∙ M ⦂ S ⇒ T

  _$$_⦂_     : Γ ⊢[ md ] M ⦂ T ⇒ S →
               Γ ⊢[ md ] N ⦂ T →
               ⊢[ md ] T ⦂ty →
               ---------------------
               Γ ⊢[ md ] M $$ N ⦂ S

  unit       : ---------------------
               Γ ⊢[ md ] unit ⦂ Top
