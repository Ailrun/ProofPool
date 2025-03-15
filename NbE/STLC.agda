{-# OPTIONS --backtracking-instance-search #-}
module NbE.STLC where

open import Data.Bool
open import Data.Nat hiding (_^_)
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Wrap renaming ([_] to W[_])
open import Function using (id; _$_; _∘_)
import Function.Endo.Propositional as Endo
open import Level using (Level)
open import Relation.Nullary.Negation
open import Relation.Nullary.Decidable as Dec
open import Relation.Binary.Bundles
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality hiding ([_])
import Relation.Binary.Reasoning.Setoid as Setoid-Reasoning
open import Relation.Binary.Structures

module FunEq where
  _≈_ : ∀ {X Y} → (f g : X → Y) → Set
  f ≈ g = ∀ x → f x ≡ g x

  ≈-refl : ∀ {X Y} {f : X → Y} → f ≈ f
  ≈-refl = λ _ → refl

  ≈-sym : ∀ {X Y} {f g : X → Y} → f ≈ g → g ≈ f
  ≈-sym equiv = λ x → sym (equiv x)

  ≈-trans : ∀ {X Y} {f g h : X → Y} → f ≈ g → g ≈ h → f ≈ h
  ≈-trans equiv equiv' = λ x → trans (equiv x) (equiv' x)
open FunEq

infixr 40 _`→_
data Ty : Set where
  `N   : Ty
  _`→_ : Ty → Ty → Ty

_Ty≟_ : ∀ (A A' : Ty) →
        ----------------
         Dec (A ≡ A')
`N       Ty≟ `N         = yes refl
`N       Ty≟ (A' `→ B') = no λ ()
(A `→ B) Ty≟ `N         = no λ ()
(A `→ B) Ty≟ (A' `→ B') = Dec.map′ (λ{ (refl , refl) → refl }) (λ{ refl → refl , refl }) ((A Ty≟ A') Dec.×-dec (B Ty≟ B'))

infixl 30 _`,_
data Ctx : Set where
  `·   : Ctx
  _`,_ : Ctx → Ty → Ctx

infixl 30 _`,,_
_`,,_ : Ctx → Ctx → Ctx
Γ `,, `· = Γ
Γ `,, (Δ `, A) = (Γ `,, Δ) `, A

ctxLen : Ctx → ℕ
ctxLen `·       = zero
ctxLen (Γ `, A) = suc (ctxLen Γ)

infixr 37 `!_
infixl 36 _`$_
infixr 35 `λ_

data Tm : Set where
  `!_   : ℕ → Tm

  `zero : Tm
  `suc  : Tm
  `rec  : Tm

  `λ_   : Tm → Tm

  _`$_  : Tm → Tm → Tm

------------------------------------------------------------
-- The Problem of Inductive Reprentations of
-- Weakenings and Substitutions
------------------------------------------------------------
--
-- Using inductive types for weakenings and substitutions
-- is not easy. We want a weakening be also a substitution;
-- in other words, we want to define `wk2sub : Wk → Sub`.
-- Also, we want to apply a substitution on weakening to
-- get a substitution and the other way around, i.e. to define
-- `[_]_ : Sub → Wk → Sub` and `wk[_]_ : Wk → Sub → Sub`.
-- However, defining these two while preserving the meaning
-- of weakening upon an identity substitution preserves causes
-- some issues:
-- 1. If we define `Wk` to contain `` `· : Wk `` which is a
--    weakening from `` `· `` to `` `· ``, and `Sub` to contain `` `· : Sub ``
--    which is a substitution from `` `· `` to `Γ`, we do not know what
--    to return in ``[ `· ] ε`` case. `wk2sub ε` does not work
--    because it gives a substitution from `` `· `` to `` `· ``.
--    `` `· `` does not work because then we cannot prove the meaning
--    preservation upon an identity substitution in an untyped way.
-- 2. If we change `Sub` to contain `` `· : Sub `` for a substitution
--    from `` `· `` to `` `· ``, we need a way to weaken this substitution.
--    In other words, we need to add `` `wk : Sub → Sub ``.
--    Now, the problem is on the definition of ``wk[ ε ] `wk σ``.
-- Instead, we will use functional encoding to represent them;
-- even though they contains some noise (i.e. even when domain is
-- of length n, the substitution contains entries for m > n),
-- the encoding works better in terms of untyped terms.

-- Renaming
Ren = ℕ → ℕ
record Ext : Set where
  constructor ext
  field
    shift : ℕ
open Ext
Sub = ℕ → Tm

infix 30 -`,s_
-`,s_ : Tm → Sub
-`,s_ M zero    = M
-`,s_ _ (suc x) = `! x

ext2ren : Ext → Ren
ext2ren φ = φ .shift +_

ren2sub : Ren → Sub
ren2sub = _∘_ (`!_)

variable
  x x' x'' x₀ x₁ x₂ x₃ y y' y'' y₀ y₁ y₂ y₃ z z' z'' z₀ z₁ z₂ z₃ : ℕ
  Γ Γ' Γ'' Γ₀ Γ₁ Γ₂ Γ₃ Δ Δ' Δ'' Δ₀ Δ₁ Δ₂ Δ₃ Ψ Ψ' Ψ'' Ψ₀ Ψ₁ Ψ₂ Ψ₃ : Ctx
  A A' A'' A₀ A₁ A₂ A₃ B B' B'' B₀ B₁ B₂ B₃ C C' C'' C₀ C₁ C₂ C₃ : Ty
  L L' L'' L₀ L₁ L₂ L₃ M M' M'' M₀ M₁ M₂ M₃ N N' N'' N₀ N₁ N₂ N₃ : Tm
  δ δ' δ'' δ₀ δ₁ δ₂ δ₃ ε ε' ε'' ε₀ ε₁ ε₂ ε₃ : Ren
  φ φ' φ'' φ₀ φ₁ φ₂ φ₃ γ γ' γ'' γ₀ γ₁ γ₂ γ₃ : Ext
  σ σ' σ'' σ₀ σ₁ σ₂ σ₃ τ τ' τ'' τ₀ τ₁ τ₂ τ₃ : Sub

_Ctx≟_ : ∀ (Γ Γ' : Ctx) →
         -----------------
          Dec (Γ ≡ Γ')
`·       Ctx≟ `·         = yes refl
`·       Ctx≟ (Γ' `, A') = no λ ()
(Γ `, A) Ctx≟ `·         = no λ ()
(Γ `, A) Ctx≟ (Γ' `, A') = Dec.map′ (λ{ (refl , refl) → refl }) (λ{ refl → refl , refl }) ((Γ Ctx≟ Γ') Dec.×-dec (A Ty≟ A'))

`,-injective : Γ `, A ≡ Δ `, B → Γ ≡ Δ × A ≡ B
`,-injective refl = refl , refl

module _ where
  open import Algebra.Definitions {A = Ctx} _≡_

  `,,-associative : Associative _`,,_
  `,,-associative Γ Δ `·       = refl
  `,,-associative Γ Δ (Ψ `, A) = cong (_`, A) (`,,-associative Γ Δ Ψ)

ctxLen-`,, : ∀ {Γ} Γ' →
             ------------------------------------------
              ctxLen (Γ `,, Γ') ≡ ctxLen Γ + ctxLen Γ'
ctxLen-`,, `·        = sym (+-identityʳ _)
ctxLen-`,, (Γ' `, A) = trans (cong suc (ctxLen-`,, Γ')) (sym (+-suc _ (ctxLen Γ')))

Γ≢Γ,,Δ,A : ¬ Γ ≡ Γ `,, Γ' `, A
Γ≢Γ,,Δ,A {Γ = Γ `, B} {Γ' = Γ' `, C} eq
  with eq' , refl ← `,-injective eq
    rewrite `,,-associative Γ (`· `, B) (Γ' `, C) = Γ≢Γ,,Δ,A eq'

infix 25 IncludeSyntax
data _Include_`:_ : Ctx → ℕ → Ty → Set
IncludeSyntax = _Include_`:_
syntax IncludeSyntax Γ x A = x `: A ∈ Γ
data _Include_`:_ where
  here  : -----------------
           0 `: A ∈ Γ `, A

  there :  x `: A ∈ Γ →
          ---------------------
           suc x `: A ∈ Γ `, B

infix 25 _⊢_`:_
data _⊢_`:_ : Ctx → Tm → Ty → Set where
  `!_   :  x `: A ∈ Γ →
          ---------------
           Γ ⊢ `! x `: A

  `zero : -----------------
           Γ ⊢ `zero `: `N

  `suc  : ----------------------
           Γ ⊢ `suc `: `N `→ `N

  `rec  : --------------------------------------------
           Γ ⊢ `rec `: A `→ (`N `→ A `→ A) `→ `N `→ A

  `λ_   :  Γ `, A ⊢ M `: B →
          --------------------
           Γ ⊢ `λ M `: A `→ B

  _`$_  :  Γ ⊢ M `: A `→ B →
           Γ ⊢ N `: A →
          -------------------
           Γ ⊢ M `$ N `: B

infix 25 _⊢r_`:_
_⊢r_`:_ : Ctx → Ren → Ctx → Set
_⊢r_`:_ = Wrap (λ Γ δ Δ → ∀ {A x} → x `: A ∈ Δ → δ x `: A ∈ Γ)

⊢ren : (∀ {A x} → x `: A ∈ Δ → δ x `: A ∈ Γ) → Γ ⊢r δ `: Δ
⊢ren = W[_]

infix 25 _⊢e_`:_
_⊢e_`:_ : Ctx → Ext → Ctx → Set
_⊢e_`:_ = Wrap (λ Γ φ Δ → Γ ⊢r ext2ren φ `: Δ)

⊢ext : (∀ {A x} → x `: A ∈ Δ → (shift φ + x) `: A ∈ Γ) → Γ ⊢e φ `: Δ
⊢ext = W[_] ∘ W[_]

⊢ext' : Γ ⊢r ext2ren φ `: Δ → Γ ⊢e φ `: Δ
⊢ext' = W[_]

infix 25 _⊢s_`:_
_⊢s_`:_ : Ctx → Sub → Ctx → Set
_⊢s_`:_ = Wrap (λ Γ σ Δ → ∀ {A x} → x `: A ∈ Δ → Γ ⊢ σ x `: A)

⊢sub : (∀ {A x} → x `: A ∈ Δ → Γ ⊢ σ x `: A) → Γ ⊢s σ `: Δ
⊢sub = W[_]

infix 30 ⊢-`,s_
⊢-`,s_ :  Γ ⊢ M `: A →
         -----------------------
          Γ ⊢s -`,s M `: Γ `, A
⊢-`,s ⊢M = ⊢sub λ where
  here        → ⊢M
  (there x∈Γ) → `! x∈Γ

⊢ext2ren :  Γ ⊢e φ `: Δ →
           ---------------------
            Γ ⊢r ext2ren φ `: Δ
⊢ext2ren ⊢δ = ⊢δ .get

⊢ren2sub :  Γ ⊢r δ `: Δ →
           ---------------------
            Γ ⊢s ren2sub δ `: Δ
⊢ren2sub ⊢δ = ⊢sub (`!_ ∘ ⊢δ .get)

record ⊢Class (X Y : Set) : Set₁ where
  field
    ⊢Judgement : Ctx → X → Y → Set
open ⊢Class ⦃...⦄

instance
  ⊢ClassVar : ⊢Class ℕ Ty
  ⊢Judgement ⦃ ⊢ClassVar ⦄ = _Include_`:_

  ⊢ClassTm : ⊢Class Tm Ty
  ⊢Judgement ⦃ ⊢ClassTm ⦄ = _⊢_`:_

  ⊢ClassRen : ⊢Class Ren Ctx
  ⊢Judgement ⦃ ⊢ClassRen ⦄ = _⊢r_`:_

  ⊢ClassExt : ⊢Class Ext Ctx
  ⊢Judgement ⦃ ⊢ClassExt ⦄ = _⊢e_`:_

  ⊢ClassSub : ⊢Class Sub Ctx
  ⊢Judgement ⦃ ⊢ClassSub ⦄ = _⊢s_`:_

record CtxId (X : Set) : Set where
  field
    ^id : X
open CtxId ⦃...⦄

record ⊢CtxId X ⦃ CtxIdX : CtxId X ⦄ ⦃ ⊢ClassX : ⊢Class X Ctx ⦄ : Set where
  field
    ⊢^id : ⊢Judgement Γ ^id Γ
open ⊢CtxId ⦃...⦄

record CtxExt (X : Set) : Set where
  field
    ^ext : X → X
open CtxExt ⦃...⦄

record ⊢CtxExt X ⦃ CtxExtX : CtxExt X ⦄ ⦃ ⊢ClassX : ⊢Class X Ctx ⦄ : Set where
  field
    ⊢^ext : ∀ {x : X} → ⊢Judgement Γ x Δ → ⊢Judgement (Γ `, A) (^ext x) (Δ `, A)
open ⊢CtxExt ⦃...⦄

instance
  CtxIdRen : CtxId Ren
  ^id ⦃ CtxIdRen ⦄ = id

  ⊢CtxIdRen : ⊢CtxId Ren
  ⊢^id ⦃ ⊢CtxIdRen ⦄ = ⊢ren id

  CtxIdExt : CtxId Ext
  ^id ⦃ CtxIdExt ⦄ = ext 0

  ⊢CtxIdExt : ⊢CtxId Ext
  ⊢^id ⦃ ⊢CtxIdExt ⦄ = ⊢ext' ⊢^id

  CtxIdSub : CtxId Sub
  ^id ⦃ CtxIdSub ⦄ = ren2sub ^id

  ⊢CtxIdSub : ⊢CtxId Sub
  ⊢^id ⦃ ⊢CtxIdSub ⦄ = ⊢ren2sub ⊢^id

  CtxExtRen : CtxExt Ren
  ^ext ⦃ CtxExtRen ⦄ δ zero    = zero
  ^ext ⦃ CtxExtRen ⦄ δ (suc n) = suc (δ n)

  ⊢CtxExtRen : ⊢CtxExt Ren
  ⊢^ext ⦃ ⊢CtxExtRen ⦄ ⊢δ = ⊢ren λ where
      here        → here
      (there x∈Δ) → there (⊢δ .get x∈Δ)

Ren^ext^id≈^id : ^ext ^id ≈ ^id ⦃ CtxIdRen ⦄
Ren^ext^id≈^id zero    = refl
Ren^ext^id≈^id (suc _) = refl

Ren^ext-respects-≈ : δ ≈ ε → ^ext δ ≈ ^ext ε
Ren^ext-respects-≈ equiv = λ where
  zero    → refl
  (suc x) → cong suc (equiv x)

record AppRen (X : Set) : Set where
  infixr 40 ren[_]_
  field
    ren[_]_ : Ren → X → X

  infixr 40 wk1_
  wk1_ : X → X
  wk1 x = ren[ suc ] x
open AppRen ⦃...⦄

record ⊢AppRen X {Y} ⦃ AppRenX : AppRen X ⦄ ⦃ ⊢ClassX : ⊢Class X Y ⦄ : Set where
  infixr 40 ⊢ren[_]_
  field
    ⊢ren[_]_ : ∀ {x : X} {y : Y} →
               Γ ⊢r δ `: Δ →
               ⊢Judgement Δ x y →
              -----------------------------
               ⊢Judgement Γ (ren[ δ ] x) y

  infixr 40 ⊢wk1_
  ⊢wk1_ : ∀ {x : X} {y : Y} →
           ⊢Judgement Γ x y →
          --------------------------------
           ⊢Judgement (Γ `, A) (wk1 x) y
  ⊢wk1_ = ⊢ren[ ⊢ren there ]_
open ⊢AppRen ⦃...⦄

record AppRenEquiv⇒Eq X ⦃ AppRenX : AppRen X ⦄ : Set where
  field
    ren[≈]⇒≡ : ∀ (x : X) →
                δ ≈ ε →
               -------------------------
                ren[ δ ] x ≡ ren[ ε ] x
open AppRenEquiv⇒Eq ⦃...⦄

record AppRenId⇒Id X ⦃ AppRenX : AppRen X ⦄ : Set where
  field
    ren[id]⇒id : ∀ {x : X} →
                ------------------
                 ren[ ^id ] x ≡ x
open AppRenId⇒Id ⦃...⦄

instance
  AppRenVar : AppRen ℕ
  ren[_]_ ⦃ AppRenVar ⦄ = _$_

  ⊢AppRenVar : ⊢AppRen ℕ
  ⊢ren[_]_ ⦃ ⊢AppRenVar ⦄ ⊢δ = ⊢δ .get

  AppRenEquiv⇒EqVar : AppRenEquiv⇒Eq ℕ
  ren[≈]⇒≡ ⦃ AppRenEquiv⇒EqVar ⦄ _ equiv = equiv _

  AppRenId⇒IdVar : AppRenId⇒Id ℕ
  ren[id]⇒id ⦃ AppRenId⇒IdVar ⦄ = refl

  AppRenTm : AppRen Tm
  ren[_]_ ⦃ AppRenTm ⦄ δ (`! x)   = `! ren[ δ ] x
  ren[_]_ ⦃ AppRenTm ⦄ δ `zero    = `zero
  ren[_]_ ⦃ AppRenTm ⦄ δ `suc     = `suc
  ren[_]_ ⦃ AppRenTm ⦄ δ `rec     = `rec
  ren[_]_ ⦃ AppRenTm ⦄ δ (`λ M)   = `λ ren[ ^ext δ ] M
  ren[_]_ ⦃ AppRenTm ⦄ δ (M `$ N) = ren[ δ ] M `$ ren[ δ ] N

  ⊢AppRenTm : ⊢AppRen Tm
  ⊢ren[_]_ ⦃ ⊢AppRenTm ⦄ ⊢δ (`! x∈)    = `! ⊢ren[ ⊢δ ] x∈
  ⊢ren[_]_ ⦃ ⊢AppRenTm ⦄ ⊢δ `zero      = `zero
  ⊢ren[_]_ ⦃ ⊢AppRenTm ⦄ ⊢δ `suc       = `suc
  ⊢ren[_]_ ⦃ ⊢AppRenTm ⦄ ⊢δ `rec       = `rec
  ⊢ren[_]_ ⦃ ⊢AppRenTm ⦄ ⊢δ (`λ ⊢M)    = `λ ⊢ren[ ⊢^ext ⊢δ ] ⊢M
  ⊢ren[_]_ ⦃ ⊢AppRenTm ⦄ ⊢δ (⊢M `$ ⊢N) = ⊢ren[ ⊢δ ] ⊢M `$ ⊢ren[ ⊢δ ] ⊢N

  AppRenEquiv⇒EqTm : AppRenEquiv⇒Eq Tm
  ren[≈]⇒≡ ⦃ AppRenEquiv⇒EqTm ⦄ (`! x)   equiv = cong `!_ (ren[≈]⇒≡ x equiv)
  ren[≈]⇒≡ ⦃ AppRenEquiv⇒EqTm ⦄ `zero    equiv = refl
  ren[≈]⇒≡ ⦃ AppRenEquiv⇒EqTm ⦄ `suc     equiv = refl
  ren[≈]⇒≡ ⦃ AppRenEquiv⇒EqTm ⦄ `rec     equiv = refl
  ren[≈]⇒≡ ⦃ AppRenEquiv⇒EqTm ⦄ (`λ M)   equiv = cong `λ_ (ren[≈]⇒≡ M (Ren^ext-respects-≈ equiv))
  ren[≈]⇒≡ ⦃ AppRenEquiv⇒EqTm ⦄ (M `$ N) equiv = cong₂ _`$_ (ren[≈]⇒≡ M equiv) (ren[≈]⇒≡ N equiv)

  AppRenId⇒IdTm : AppRenId⇒Id Tm
  ren[id]⇒id ⦃ AppRenId⇒IdTm ⦄ {x = `! x}   = cong `!_ ren[id]⇒id
  ren[id]⇒id ⦃ AppRenId⇒IdTm ⦄ {x = `zero}  = refl
  ren[id]⇒id ⦃ AppRenId⇒IdTm ⦄ {x = `suc}   = refl
  ren[id]⇒id ⦃ AppRenId⇒IdTm ⦄ {x = `rec}   = refl
  ren[id]⇒id ⦃ AppRenId⇒IdTm ⦄ {x = `λ M}   = cong `λ_ (trans (ren[≈]⇒≡ M Ren^ext^id≈^id) ren[id]⇒id)
  ren[id]⇒id ⦃ AppRenId⇒IdTm ⦄ {x = M `$ N} = cong₂ _`$_ ren[id]⇒id ren[id]⇒id

  AppRenRen : AppRen Ren
  ren[_]_ ⦃ AppRenRen ⦄ δ ε = δ ∘ ε

  ⊢AppRenRen : ⊢AppRen Ren
  ⊢ren[_]_ ⦃ ⊢AppRenRen ⦄ ⊢δ ⊢ε = ⊢ren (⊢δ .get ∘ ⊢ε .get)

  AppRenId⇒IdRen : AppRenId⇒Id Ren
  ren[id]⇒id ⦃ AppRenId⇒IdRen ⦄ = refl

  AppRenSub : AppRen Sub
  ren[_]_ ⦃ AppRenSub ⦄ δ σ = ren[ δ ]_ ∘ σ

  ⊢AppRenSub : ⊢AppRen Sub
  ⊢ren[_]_ ⦃ ⊢AppRenSub ⦄ ⊢δ ⊢σ = ⊢sub (⊢ren[ ⊢δ ]_ ∘ ⊢σ .get)

ren[^ext]^ext≈^extren[]Ren : ren[ ^ext δ ] (^ext ε) ≈ ^ext (ren[ δ ] ε)
ren[^ext]^ext≈^extren[]Ren zero    = refl
ren[^ext]^ext≈^extren[]Ren (suc x) = refl

ext[_]_ : ∀ {X} ⦃ AppRenX : AppRen X ⦄ → Ext → X → X
ext[_]_ = ren[_]_ ∘ ext2ren

⊢ext[_]_ : ∀ {X Y}
             ⦃ AppRenX : AppRen X ⦄
             ⦃ ⊢ClassX : ⊢Class X Y ⦄
             ⦃ ⊢AppRenX : ⊢AppRen X ⦄
             {x : X} {y : Y} →
            Γ ⊢e φ `: Δ →
            ⊢Judgement Δ x y →
            ⊢Judgement Γ (ext[ φ ] x) y
⊢ext[_]_ = ⊢ren[_]_ ∘ get

ren[≈]Ren⇒≈ : δ ≈ ε → ren[ δ ] δ' ≈ ren[ ε ] δ'
ren[≈]Ren⇒≈ equiv _ = equiv _

ren[≈]Sub⇒≈ : δ ≈ ε → ren[ δ ] σ ≈ ren[ ε ] σ
ren[≈]Sub⇒≈ equiv _ = ren[≈]⇒≡ _ equiv

ren[id]Sub⇒≈ : ren[ ^id ] σ ≈ σ
ren[id]Sub⇒≈ _ = ren[id]⇒id

instance
  CtxExtSub : CtxExt Sub
  ^ext ⦃ CtxExtSub ⦄ σ zero    = `! zero
  ^ext ⦃ CtxExtSub ⦄ σ (suc x) = wk1 (σ x)

  ⊢CtxExtSub : ⊢CtxExt Sub
  ⊢^ext ⦃ ⊢CtxExtSub ⦄ ⊢σ = ⊢sub λ where
      here        → `! here
      (there x∈Δ) → ⊢wk1 (⊢σ .get x∈Δ)

Sub^ext^id≈^id : ^ext ^id ≈ ^id ⦃ CtxIdSub ⦄
Sub^ext^id≈^id zero    = refl
Sub^ext^id≈^id (suc _) = refl

Sub^ext-respects-≈ : σ ≈ τ → ^ext σ ≈ ^ext τ
Sub^ext-respects-≈ equiv = λ where
  zero    → refl
  (suc x) → cong wk1_ (equiv x)

record AppSub (X : Set) : Set₁ where
  infixr 40 [_]_
  field
    AppSubResult : Set
    AppSubResultMap : X → AppSubResult
    [_]_ : Sub → X → AppSubResult

  infixr 40 [_1]_
  [_1]_ : Tm → X → AppSubResult
  [ L 1] x = [ -`,s L ] x
open AppSub ⦃...⦄

record ⊢AppSub X {Y} ⦃ AppSubX : AppSub X ⦄ ⦃ ⊢ClassX : ⊢Class X Y ⦄ ⦃ ⊢ClassOutput : ⊢Class AppSubResult Y ⦄ : Set₁ where
  infixr 40 ⊢[_]_
  field
    ⊢[_]_ : ∀ {x : X} {y : Y} → Γ ⊢s σ `: Δ → ⊢Judgement Δ x y → ⊢Judgement Γ ([ σ ] x) y

  infixr 40 ⊢[_1]_
  ⊢[_1]_ : ∀ {x : X} {y : Y} → Γ ⊢ L `: A → ⊢Judgement (Γ `, A) x y → ⊢Judgement Γ ([ L 1] x) y
  ⊢[ ⊢L 1] ⊢x = ⊢[ ⊢-`,s ⊢L ] ⊢x
open ⊢AppSub ⦃...⦄

record AppSubEquiv⇒Eq X ⦃ AppSubX : AppSub X ⦄ : Set where
  field
    [≈]⇒≡ : ∀ (x : X) →
             σ ≈ τ →
            -------------------
             [ σ ] x ≡ [ τ ] x
open AppSubEquiv⇒Eq ⦃...⦄

record AppSubId⇒Id X ⦃ AppSubX : AppSub X ⦄ : Set where
  field
    [id]⇒id : ∀ {x : X} →
              -------------------------------
               [ ^id ] x ≡ AppSubResultMap x
open AppSubId⇒Id ⦃...⦄

instance
  AppSubVar : AppSub ℕ
  AppSubResult ⦃ AppSubVar ⦄ = Tm
  AppSubResultMap ⦃ AppSubVar ⦄ = `!_
  [_]_ ⦃ AppSubVar ⦄ = _$_

  ⊢AppSubVar : ⊢AppSub ℕ
  ⊢[_]_ ⦃ ⊢AppSubVar ⦄ ⊢σ = ⊢σ .get

  AppSubEquiv⇒EqVar : AppSubEquiv⇒Eq ℕ
  [≈]⇒≡ ⦃ AppSubEquiv⇒EqVar ⦄ _ equiv = equiv _

  AppSubId⇒IdVar : AppSubId⇒Id ℕ
  [id]⇒id ⦃ AppSubId⇒IdVar ⦄ = refl

  AppSubTm : AppSub Tm
  AppSubResult ⦃ AppSubTm ⦄ = Tm
  AppSubResultMap ⦃ AppSubTm ⦄ = id
  [_]_ ⦃ AppSubTm ⦄ σ (`! x)   = [ σ ] x
  [_]_ ⦃ AppSubTm ⦄ σ `zero    = `zero
  [_]_ ⦃ AppSubTm ⦄ σ `suc     = `suc
  [_]_ ⦃ AppSubTm ⦄ σ `rec     = `rec
  [_]_ ⦃ AppSubTm ⦄ σ (`λ M)   = `λ [ ^ext σ ] M
  [_]_ ⦃ AppSubTm ⦄ σ (M `$ N) = [ σ ] M `$ [ σ ] N

  ⊢AppSubTm : ⊢AppSub Tm
  ⊢[_]_ ⦃ ⊢AppSubTm ⦄ ⊢σ (`! x∈Γ)   = ⊢[ ⊢σ ] x∈Γ
  ⊢[_]_ ⦃ ⊢AppSubTm ⦄ ⊢σ `zero      = `zero
  ⊢[_]_ ⦃ ⊢AppSubTm ⦄ ⊢σ `suc       = `suc
  ⊢[_]_ ⦃ ⊢AppSubTm ⦄ ⊢σ `rec       = `rec
  ⊢[_]_ ⦃ ⊢AppSubTm ⦄ ⊢σ (`λ ⊢M)    = `λ ⊢[ ⊢^ext ⊢σ ] ⊢M
  ⊢[_]_ ⦃ ⊢AppSubTm ⦄ ⊢σ (⊢M `$ ⊢N) = ⊢[ ⊢σ ] ⊢M `$ ⊢[ ⊢σ ] ⊢N

  AppSubEquiv⇒EqTm : AppSubEquiv⇒Eq Tm
  [≈]⇒≡ ⦃ AppSubEquiv⇒EqTm ⦄ (`! x)   equiv = [≈]⇒≡ x equiv
  [≈]⇒≡ ⦃ AppSubEquiv⇒EqTm ⦄ `zero    equiv = refl
  [≈]⇒≡ ⦃ AppSubEquiv⇒EqTm ⦄ `suc     equiv = refl
  [≈]⇒≡ ⦃ AppSubEquiv⇒EqTm ⦄ `rec     equiv = refl
  [≈]⇒≡ ⦃ AppSubEquiv⇒EqTm ⦄ (`λ M)   equiv = cong `λ_ ([≈]⇒≡ M (Sub^ext-respects-≈ equiv))
  [≈]⇒≡ ⦃ AppSubEquiv⇒EqTm ⦄ (M `$ N) equiv = cong₂ _`$_ ([≈]⇒≡ M equiv) ([≈]⇒≡ N equiv)

  AppSubId⇒IdTm : AppSubId⇒Id Tm
  [id]⇒id ⦃ AppSubId⇒IdTm ⦄ {x = `! x}   = [id]⇒id ⦃ _ ⦄ ⦃ AppSubId⇒IdVar ⦄
  [id]⇒id ⦃ AppSubId⇒IdTm ⦄ {x = `zero}  = refl
  [id]⇒id ⦃ AppSubId⇒IdTm ⦄ {x = `suc}   = refl
  [id]⇒id ⦃ AppSubId⇒IdTm ⦄ {x = `rec}   = refl
  [id]⇒id ⦃ AppSubId⇒IdTm ⦄ {x = `λ M}   = cong `λ_ (trans ([≈]⇒≡ M Sub^ext^id≈^id) [id]⇒id)
  [id]⇒id ⦃ AppSubId⇒IdTm ⦄ {x = M `$ N} = cong₂ _`$_ [id]⇒id [id]⇒id

  AppSubRen : AppSub Ren
  AppSubResult ⦃ AppSubRen ⦄ = Sub
  AppSubResultMap ⦃ AppSubRen ⦄ = ren2sub
  [_]_ ⦃ AppSubRen ⦄ σ = σ ∘_

  ⊢AppSubRen : ⊢AppSub Ren
  ⊢[_]_ ⦃ ⊢AppSubRen ⦄ ⊢σ ⊢δ = ⊢sub (⊢σ .get ∘ ⊢δ .get)

  AppSubId⇒IdRen : AppSubId⇒Id Ren
  [id]⇒id ⦃ AppSubId⇒IdRen ⦄ = refl

  AppSubSub : AppSub Sub
  AppSubResult ⦃ AppSubSub ⦄ = Sub
  AppSubResultMap ⦃ AppSubSub ⦄ = id
  [_]_ ⦃ AppSubSub ⦄ σ = [ σ ]_ ∘_

  ⊢AppSubSub : ⊢AppSub Sub
  ⊢[_]_ ⦃ ⊢AppSubSub ⦄ ⊢σ ⊢τ = ⊢sub (⊢[ ⊢σ ]_ ∘ ⊢τ .get)

[≈]Ren⇒≈ : σ ≈ τ → [ σ ] δ' ≈ [ τ ] δ'
[≈]Ren⇒≈ equiv _ = equiv _

[≈]Sub⇒≈ : σ ≈ τ → [ σ ] σ' ≈ [ τ ] σ'
[≈]Sub⇒≈ {σ' = σ'} equiv x = [≈]⇒≡ (σ' x) equiv

[id]Sub⇒≈ : [ ^id ] σ ≈ σ
[id]Sub⇒≈ _ = [id]⇒id

record AppRenCompose X ⦃ AppRenX : AppRen X ⦄ : Set where
  field
    ren[]-compose : ∀ δ ε (x : X) →
                    -------------------------------------------
                     ren[ δ ] ren[ ε ] x ≡ ren[ ren[ δ ] ε ] x

record AppSubRenCompose X ⦃ AppRenX : AppRen X ⦄ ⦃ AppSubX : AppSub X ⦄ ⦃ AppRenXOutput : AppRen (AppSubResult ⦃ AppSubX ⦄) ⦄ : Set where
  field
    ren[]-[]-compose : ∀ δ σ (x : X) →
                       -------------------------------------
                        ren[ δ ] [ σ ] x ≡ [ ren[ δ ] σ ] x

record AppRenSubCompose X ⦃ AppRenX : AppRen X ⦄ ⦃ AppSubX : AppSub X ⦄ : Set where
  field
    []-ren[]-compose : ∀ σ δ (x : X) →
                       ----------------------------------
                        [ σ ] ren[ δ ] x ≡ [ [ σ ] δ ] x

record AppSubCompose X ⦃ AppSubX : AppSub X ⦄  ⦃ AppSubXOutput : AppSub (AppSubResult ⦃ AppSubX ⦄) ⦄ : Set where
  field
    []-compose : ∀ σ τ (x : X) →
                 -------------------------------------------------
                  [ σ ] [ τ ] x ≡ AppSubResultMap ([ [ σ ] τ ] x)

record CompatibleSubRen X ⦃ AppRenX : AppRen X ⦄ ⦃ AppSubX : AppSub X ⦄ : Set where
  field
    compatible-Sub-Ren : ∀ δ (x : X) →
                         ------------------------------------------------
                          [ ren2sub δ ] x ≡ AppSubResultMap (ren[ δ ] x)

open AppRenCompose ⦃...⦄
open AppSubRenCompose ⦃...⦄
open AppRenSubCompose ⦃...⦄
open AppSubCompose ⦃...⦄
open CompatibleSubRen ⦃...⦄
instance
  AppRenComposeVar : AppRenCompose ℕ
  ren[]-compose ⦃ AppRenComposeVar ⦄ _ _ _ = refl

  AppRenComposeTm : AppRenCompose Tm
  ren[]-compose ⦃ AppRenComposeTm ⦄ δ ε (`! x)   = cong `!_ (ren[]-compose δ ε x)
  ren[]-compose ⦃ AppRenComposeTm ⦄ δ ε `zero    = refl
  ren[]-compose ⦃ AppRenComposeTm ⦄ δ ε `suc     = refl
  ren[]-compose ⦃ AppRenComposeTm ⦄ δ ε `rec     = refl
  ren[]-compose ⦃ AppRenComposeTm ⦄ δ ε (`λ M)   = cong `λ_ (trans (ren[]-compose (^ext δ) (^ext ε) M) (ren[≈]⇒≡ M ren[^ext]^ext≈^extren[]Ren))
  ren[]-compose ⦃ AppRenComposeTm ⦄ δ ε (M `$ N) = cong₂ _`$_ (ren[]-compose δ ε M) (ren[]-compose δ ε N)

  AppRenComposeRen : AppRenCompose Ren
  ren[]-compose ⦃ AppRenComposeRen ⦄ _ _ _ = refl

ren[]Sub-composeEquiv : ∀ δ ε (σ : Sub) →
                        -------------------------------------------
                         ren[ δ ] ren[ ε ] σ ≈ ren[ ren[ δ ] ε ] σ
ren[]Sub-composeEquiv δ ε = ren[]-compose δ ε ∘_

ren[^ext]wk1≈wk1ren[]Tm : ren[ ^ext δ ] (wk1 M) ≡ wk1 (ren[ δ ] M)
ren[^ext]wk1≈wk1ren[]Tm {M = `! x} = refl
ren[^ext]wk1≈wk1ren[]Tm {M = `zero} = refl
ren[^ext]wk1≈wk1ren[]Tm {M = `suc} = refl
ren[^ext]wk1≈wk1ren[]Tm {M = `rec} = refl
ren[^ext]wk1≈wk1ren[]Tm {M = `λ M} = cong `λ_
  (begin ren[ ^ext (^ext _) ] ren[ ^ext suc ] M ≡⟨ ren[]-compose (^ext (^ext _)) (^ext suc) M ⟩
         ren[ ren[ ^ext (^ext _) ] ^ext suc ] M ≡⟨ ren[≈]⇒≡ M ren[^ext]^ext≈^extren[]Ren ⟩
         ren[ ^ext (ren[ suc ] _) ] M           ≡˘⟨ ren[≈]⇒≡ M ren[^ext]^ext≈^extren[]Ren ⟩
         ren[ ren[ ^ext suc ] ^ext _ ] M        ≡˘⟨ ren[]-compose (^ext suc) (^ext _) M ⟩
         ren[ ^ext suc ] ren[ ^ext _ ] M        ∎)
  where
    open ≡-Reasoning
ren[^ext]wk1≈wk1ren[]Tm {M = M `$ N} = cong₂ _`$_ ren[^ext]wk1≈wk1ren[]Tm ren[^ext]wk1≈wk1ren[]Tm

ren[^ext]^ext≈^extren[]Sub : ren[ ^ext δ ] (^ext σ) ≈ ^ext (ren[ δ ] σ)
ren[^ext]^ext≈^extren[]Sub zero    = refl
ren[^ext]^ext≈^extren[]Sub (suc x) = ren[^ext]wk1≈wk1ren[]Tm

instance
  AppSubRenComposeVar : AppSubRenCompose ℕ
  ren[]-[]-compose ⦃ AppSubRenComposeVar ⦄ _ _ _ = refl

  AppSubRenComposeTm : AppSubRenCompose Tm
  ren[]-[]-compose ⦃ AppSubRenComposeTm ⦄ δ σ (`! x)   = ren[]-[]-compose δ σ x
  ren[]-[]-compose ⦃ AppSubRenComposeTm ⦄ δ σ `zero    = refl
  ren[]-[]-compose ⦃ AppSubRenComposeTm ⦄ δ σ `suc     = refl
  ren[]-[]-compose ⦃ AppSubRenComposeTm ⦄ δ σ `rec     = refl
  ren[]-[]-compose ⦃ AppSubRenComposeTm ⦄ δ σ (`λ M)   = cong `λ_
    (begin ren[ ^ext δ ] [ ^ext σ ] M ≡⟨ ren[]-[]-compose (^ext δ) (^ext σ) M ⟩
           [ ren[ ^ext δ ] ^ext σ ] M ≡⟨ [≈]⇒≡ M ren[^ext]^ext≈^extren[]Sub ⟩
           [ ^ext (ren[ δ ] σ) ] M    ∎)
    where
      open ≡-Reasoning
  ren[]-[]-compose ⦃ AppSubRenComposeTm ⦄ δ σ (M `$ N) = cong₂ _`$_ (ren[]-[]-compose δ σ M) (ren[]-[]-compose δ σ N)

  AppSubRenComposeRen : AppSubRenCompose Ren
  ren[]-[]-compose ⦃ AppSubRenComposeRen ⦄ _ _ _ = refl

ren[]-[]Sub-compose-Equiv : ∀ δ σ (τ : Sub) →
                            -------------------------------------
                             ren[ δ ] [ σ ] τ ≈ [ ren[ δ ] σ ] τ
ren[]-[]Sub-compose-Equiv δ σ = ren[]-[]-compose δ σ ∘_

[^ext]^ext≈^ext[]Ren : [ ^ext σ ] (^ext δ) ≈ ^ext ([ σ ] δ)
[^ext]^ext≈^ext[]Ren zero    = refl
[^ext]^ext≈^ext[]Ren (suc x) = refl

instance
  AppRenSubComposeVar : AppRenSubCompose ℕ
  []-ren[]-compose ⦃ AppRenSubComposeVar ⦄ _ _ _ = refl

  AppRenSubComposeTm : AppRenSubCompose Tm
  []-ren[]-compose ⦃ AppRenSubComposeTm ⦄ σ δ (`! x)   = []-ren[]-compose σ δ x
  []-ren[]-compose ⦃ AppRenSubComposeTm ⦄ σ δ `zero    = refl
  []-ren[]-compose ⦃ AppRenSubComposeTm ⦄ σ δ `suc     = refl
  []-ren[]-compose ⦃ AppRenSubComposeTm ⦄ σ δ `rec     = refl
  []-ren[]-compose ⦃ AppRenSubComposeTm ⦄ σ δ (`λ M)   = cong `λ_
    (begin [ ^ext σ ] ren[ ^ext δ ] M ≡⟨ []-ren[]-compose (^ext σ) (^ext δ) M ⟩
           [ [ ^ext σ ] ^ext δ ] M    ≡⟨ [≈]⇒≡ M [^ext]^ext≈^ext[]Ren ⟩
           [ ^ext ([ σ ] δ) ] M       ∎)
    where
      open ≡-Reasoning
  []-ren[]-compose ⦃ AppRenSubComposeTm ⦄ σ δ (M `$ N) = cong₂ _`$_ ([]-ren[]-compose σ δ M) ([]-ren[]-compose σ δ N)

  AppRenSubComposeRen : AppRenSubCompose Ren
  []-ren[]-compose ⦃ AppRenSubComposeRen ⦄ _ _ _ = refl

[]-ren[]Sub-compose-Equiv : ∀ σ δ (τ : Sub) →
                            ----------------------------------
                             [ σ ] ren[ δ ] τ ≈ [ [ σ ] δ ] τ
[]-ren[]Sub-compose-Equiv σ δ = []-ren[]-compose σ δ ∘_

--   CompatibleSubRenVar : CompatibleSubRen (_Include A)
--   compatible-Sub-Ren ⦃ CompatibleSubRenVar ⦄ (`wk δ) x          =
--     begin [ wk1 (fromRen δ) ] x           ≡˘⟨ ren[]-[]-compose (`wk ^id) (fromRen δ) x ⟩
--           wk1 [ fromRen δ ] x             ≡⟨ cong wk1_ (compatible-Sub-Ren δ x) ⟩
--           `! there (ren[ ^id ] ren[ δ ] x) ≡⟨ cong `!_ (cong there (ren[id]⇒id (ren[ δ ] x))) ⟩
--           `! there (ren[ δ ] x)           ∎
--     where
--       open ≡-Reasoning
--   compatible-Sub-Ren ⦃ CompatibleSubRenVar ⦄ (`ext δ) here      = refl
--   compatible-Sub-Ren ⦃ CompatibleSubRenVar ⦄ (`ext δ) (there x) =
--     begin [ wk1 (fromRen δ) ] x           ≡˘⟨ ren[]-[]-compose (`wk ^id) (fromRen δ) x ⟩
--           wk1 [ fromRen δ ] x             ≡⟨ cong wk1_ (compatible-Sub-Ren δ x) ⟩
--           `! there (ren[ ^id ] ren[ δ ] x) ≡⟨ cong `!_ (cong there (ren[id]⇒id (ren[ δ ] x))) ⟩
--           `! there (ren[ δ ] x)           ∎
--     where
--       open ≡-Reasoning

--   CompatibleSubRenTm : CompatibleSubRen (_⊢Tm: A)
--   compatible-Sub-Ren ⦃ CompatibleSubRenTm ⦄ δ (`! x)   = compatible-Sub-Ren δ x
--   compatible-Sub-Ren ⦃ CompatibleSubRenTm ⦄ δ `zero    = refl
--   compatible-Sub-Ren ⦃ CompatibleSubRenTm ⦄ δ `suc     = refl
--   compatible-Sub-Ren ⦃ CompatibleSubRenTm ⦄ δ `rec     = refl
--   compatible-Sub-Ren ⦃ CompatibleSubRenTm ⦄ δ (`λ M)   = cong `λ_ (compatible-Sub-Ren (`ext δ) M)
--   compatible-Sub-Ren ⦃ CompatibleSubRenTm ⦄ δ (M `$ N) = cong₂ _`$_ (compatible-Sub-Ren δ M) (compatible-Sub-Ren δ N)

--   CompatibleSubRenSub : CompatibleSubRen (_⊢Sub: Ψ)
--   compatible-Sub-Ren ⦃ CompatibleSubRenSub ⦄ δ `·       = refl
--   compatible-Sub-Ren ⦃ CompatibleSubRenSub ⦄ δ (σ `, M) = cong₂ _`,_ (compatible-Sub-Ren δ σ) (compatible-Sub-Ren δ M)

--   AppSubComposeVar : AppSubCompose (_Include A)
--   []-compose ⦃ AppSubComposeVar ⦄ σ (τ `, M) here      = refl
--   []-compose ⦃ AppSubComposeVar ⦄ σ (τ `, M) (there x) = []-compose σ τ x

--   AppSubComposeTm : AppSubCompose (_⊢Tm: A)
--   []-compose ⦃ AppSubComposeTm ⦄ σ τ (`! x)   = []-compose σ τ x
--   []-compose ⦃ AppSubComposeTm ⦄ σ τ `zero    = refl
--   []-compose ⦃ AppSubComposeTm ⦄ σ τ `suc     = refl
--   []-compose ⦃ AppSubComposeTm ⦄ σ τ `rec     = refl
--   []-compose ⦃ AppSubComposeTm ⦄ σ τ (`λ M)   = cong `λ_
--     (begin [ ^ext σ ] [ ^ext τ ] M               ≡⟨ []-compose (^ext σ) (^ext τ) M ⟩
--            [ [ ^ext σ ] wk1 τ `, `! here ] M     ≡⟨ cong (λ x → [ x `, _ ] M) ([]-ren[]-compose (^ext σ) (`wk ^id) τ) ⟩
--            [ [ [ wk1 σ ] idRen ] τ `, `! here ] M ≡⟨ cong (λ x → [ x `, _ ] M) (cong ([_] τ) ([]-idRen⇒id (wk1 σ))) ⟩
--            [ [ wk1 σ ] τ `, `! here ] M          ≡˘⟨ cong (λ x → [ x `, _ ] M) (ren[]-[]-compose (`wk ^id) σ τ) ⟩
--            [ ^ext ([ σ ] τ) ] M                  ∎)
--     where
--       open ≡-Reasoning
--   []-compose ⦃ AppSubComposeTm ⦄ σ τ (M `$ N) = cong₂ _`$_ ([]-compose σ τ M) ([]-compose σ τ N)

--   CtxComposeIdentitySub : CtxComposeIdentity _⊢Sub:_
--   `∘-identityʳ ⦃ CtxComposeIdentitySub ⦄ `·       = refl
--   `∘-identityʳ ⦃ CtxComposeIdentitySub ⦄ (σ `, M) = cong (_`, _)
--     (begin [ σ `, M ] wk1 idSub         ≡⟨ []-ren[]-compose (σ `, M) (`wk ^id) idSub ⟩
--            [ [ σ `, M ] `wk ^id ] idSub ≡⟨ cong ([_] idSub) ([]-idRen⇒id σ) ⟩
--            [ σ ] idSub                  ≡⟨ `∘-identityʳ σ ⟩
--            σ ∎)
--     where
--       open ≡-Reasoning

-- idSub≡fromRen-idRen : ∀ {Γ} →
--                     -----------------------------
--                      idSub {Γ = Γ} ≡ fromRen idRen
-- idSub≡fromRen-idRen {`·}     = refl
-- idSub≡fromRen-idRen {Γ `, A} = cong (_`, `! here) (cong wk1_ idSub≡fromRen-idRen)

-- [id]⇒id : ∀ {F}
--             ⦃ AppRenF : AppRen F ⦄
--             ⦃ AppSubF : AppSub F ⦄
--             ⦃ AppIdRen⇒IdF : AppIdRen⇒Id F ⦄
--             ⦃ CompatibleSubRenF : CompatibleSubRen F ⦄
--             (x : F Γ) →
--           -------------------------------------------
--            [ ^id ] x ≡ AppSubResultMap x
-- [id]⇒id x =
--   begin [ ^id ] x                     ≡⟨ cong ([_] x) idSub≡fromRen-idRen ⟩
--         [ fromRen ^id ] x              ≡⟨ compatible-Sub-Ren idRen x ⟩
--         AppSubResultMap (ren[ ^id ] x) ≡⟨ cong AppSubResultMap (ren[id]⇒id x) ⟩
--         AppSubResultMap x             ∎
--   where
--     open ≡-Reasoning

-- ctx≤[]-fromCtx≤-commute : ∀ (Γ''≤Γ' : Γ'' Ctx≤ Γ')
--                             (Γ'≤Γ : Γ' Ctx≤ Γ) →
--                           -----------------------------------------------------------------
--                            fromCtx≤ (ctx≤[ Γ''≤Γ' ] Γ'≤Γ) ≡ ctx≤[ Γ''≤Γ' ] (fromCtx≤ Γ'≤Γ)
-- ctx≤[]-fromCtx≤-commute `id          Γ'≤Γ = sym (ren[id]⇒id (fromCtx≤ Γ'≤Γ))
-- ctx≤[]-fromCtx≤-commute (`wk Γ''≤Γ') Γ'≤Γ = cong `wk (ctx≤[]-fromCtx≤-commute Γ''≤Γ' Γ'≤Γ)

-- ctx≤[]-compose : ∀ {F}
--                    ⦃ AppRenF : AppRen F ⦄
--                    ⦃ AppRenComposeF : AppRenCompose F ⦄
--                    (Γ''≤Γ' : Γ'' Ctx≤ Γ')
--                    (Γ'≤Γ : Γ' Ctx≤ Γ)
--                    (x : F Γ) →
--                  ---------------------------------------------------------------
--                   ctx≤[ Γ''≤Γ' ] ctx≤[ Γ'≤Γ ] x ≡ ctx≤[ ctx≤[ Γ''≤Γ' ] Γ'≤Γ ] x
-- ctx≤[]-compose Γ''≤Γ' Γ'≤Γ x =
--   begin ctx≤[ Γ''≤Γ' ] ctx≤[ Γ'≤Γ ] x        ≡⟨ ren[]-compose (fromCtx≤ Γ''≤Γ') (fromCtx≤ Γ'≤Γ) x ⟩
--         ren[ ctx≤[ Γ''≤Γ' ] fromCtx≤ Γ'≤Γ ] x ≡˘⟨ cong (ren[_] x) (ctx≤[]-fromCtx≤-commute Γ''≤Γ' Γ'≤Γ) ⟩
--         ctx≤[ Γ''≤Γ' `∘ Γ'≤Γ ] x             ∎
--   where
--     open ≡-Reasoning

-- data Equiv : (Γ : Ctx) → (A : Ty) → Γ ⊢Tm: A → Γ ⊢Tm: A → Set

-- syntax Equiv Γ A M M' = Γ ⊢ M ≋ M' `: A

-- data Equiv where
--   `β-`→    : ∀ {M : Γ `, A ⊢Tm: B}
--                {N : Γ ⊢Tm: A} →
--              -----------------------------------
--               Γ ⊢ (`λ M) `$ N ≋ [ N 1] M `: B

--   `β-`N₀   : ∀ {M N} →
--              --------------------------------------
--               Γ ⊢ `rec `$ M `$ N `$ `zero ≋ M `: A

--   `β-`N₁   : ∀ {M N L} →
--              --------------------------------------------------------------------------
--               Γ ⊢ `rec `$ M `$ N `$ (`suc `$ L) ≋ N `$ L `$ (`rec `$ M `$ N `$ L) `: A

--   `η-`→    : ∀ {M} →
--              ---------------------------------------------------
--               Γ ⊢ `λ wk1 M `$ `! here ≋ M `: A `→ B

--   `ξ-`!    : ∀ {x} →
--              -------------------------
--               Γ ⊢ `! x ≋ `! x `: A

--   `ξ-`zero : -------------------------
--               Γ ⊢ `zero ≋ `zero `: `N

--   `ξ-`suc  : -----------------------------
--               Γ ⊢ `suc ≋ `suc `: `N `→ `N

--   `ξ-`rec  : ---------------------------------------------------
--               Γ ⊢ `rec ≋ `rec `: A `→ (`N `→ A `→ A) `→ `N `→ A

--   `ξ-`λ_   : ∀ {M M'} →
--               Γ `, A ⊢ M ≋ M' `: B →
--              ----------------------------
--               Γ ⊢ `λ M ≋ `λ M' `: A `→ B

--   `ξ-_`$_  : ∀ {M M' N N'} →
--               Γ ⊢ M ≋ M' `: A `→ B →
--               Γ ⊢ N ≋ N' `: A →
--              ----------------------------
--               Γ ⊢ M `$ N ≋ M' `$ N' `: B

--   `sym     : ∀ {M M'} →
--               Γ ⊢ M ≋ M' `: A →
--              -------------------
--               Γ ⊢ M' ≋ M `: A

--   `trans   : ∀ {M M' M''} →
--               Γ ⊢ M ≋ M' `: A →
--               Γ ⊢ M' ≋ M'' `: A →
--              ---------------------
--               Γ ⊢ M ≋ M'' `: A

-- Equiv-refl : ∀ {M} → Γ ⊢ M ≋ M `: A
-- Equiv-refl {M = `! x}   = `ξ-`!
-- Equiv-refl {M = `zero}  = `ξ-`zero
-- Equiv-refl {M = `suc}   = `ξ-`suc
-- Equiv-refl {M = `rec}   = `ξ-`rec
-- Equiv-refl {M = `λ M}   = `ξ-`λ Equiv-refl
-- Equiv-refl {M = M `$ N} = `ξ- Equiv-refl `$ Equiv-refl

-- Equiv-IsEquivalence : IsEquivalence (Equiv Γ A)
-- Equiv-IsEquivalence = record
--                       { refl = Equiv-refl
--                       ; sym = `sym
--                       ; trans = `trans
--                       }

-- Equiv-Setoid : Ctx → Ty → Setoid _ _
-- Equiv-Setoid Γ A = record
--                    { Carrier = Γ ⊢Tm: A
--                    ; _≈_ = Equiv Γ A
--                    ; isEquivalence = Equiv-IsEquivalence
--                    }

-- module Equiv-Reasoning Γ A = Setoid-Reasoning (Equiv-Setoid Γ A)

-- Equiv-Sub : ∀ {M M'} σ →
--              Γ ⊢ M ≋ M' `: A →
--             -----------------------------
--              Δ ⊢ [ σ ] M ≋ [ σ ] M' `: A
-- Equiv-Sub {M = (`λ M) `$ N} {M' = _}  σ `β-`→                =
--   begin (`λ [ ^ext σ ] M) `$ [ σ ] N         ≈⟨ `β-`→ ⟩
--         [ [ σ ] N 1] [ ^ext σ ] M            ≡⟨ []-compose (^id `, [ σ ] N) (^ext σ) M ⟩
--         [ [ [ σ ] N 1] wk1 σ `, [ σ ] N ] M  ≡⟨ cong (λ x → [ x `, [ σ ] N ] M) ([]-ren[]-compose (^id `, [ σ ] N) (`wk ^id) σ) ⟩
--         [ ([ ^id ] idRen) `∘ σ `, [ σ ] N ] M ≡⟨ cong (λ x → [ [ x ] σ `, [ σ ] N ] M) ([]-idRen⇒id idSub) ⟩
--         [ ^id `∘ σ `, [ σ ] N ] M            ≡⟨ cong (λ x → [ x `, [ σ ] N ] M) ([id]⇒id σ) ⟩
--         [ σ `, [ σ ] N ] M                   ≡˘⟨ cong (λ x → [ x `, [ σ ] N ] M) (`∘-identityʳ σ) ⟩
--         [ σ `∘ ^id `, [ σ ] N ] M            ≡˘⟨ []-compose σ (^id `, N) M ⟩
--         [ σ ] [ ^id `, N ] M                 ∎
--   where
--     open Equiv-Reasoning _ _
-- Equiv-Sub                             σ `β-`N₀               = `β-`N₀
-- Equiv-Sub                             σ `β-`N₁               = `β-`N₁
-- Equiv-Sub                   {M' = M'} σ `η-`→                =
--   begin `λ [ ^ext σ ] wk1 M' `$ `! here     ≡⟨ cong (λ x → `λ x `$ _) ([]-ren[]-compose (^ext σ) (`wk ^id) M') ⟩
--         `λ [ [ wk1 σ ] idRen ] M' `$ `! here ≡⟨ cong (λ x → `λ [ x ] M' `$ _) ([]-idRen⇒id (wk1 σ)) ⟩
--         `λ [ wk1 σ ] M' `$ `! here          ≡˘⟨ cong (λ x → `λ x `$ _) (ren[]-[]-compose (`wk ^id) σ M') ⟩
--         `λ wk1 [ σ ] M' `$ `! here          ≈⟨ `η-`→ ⟩
--         [ σ ] M'                            ∎
--   where
--     open Equiv-Reasoning _ _
-- Equiv-Sub                             σ `ξ-`!                = Equiv-refl
-- Equiv-Sub                             σ `ξ-`zero             = `ξ-`zero
-- Equiv-Sub                             σ `ξ-`suc              = `ξ-`suc
-- Equiv-Sub                             σ `ξ-`rec              = `ξ-`rec
-- Equiv-Sub                             σ (`ξ-`λ M≋M')         = `ξ-`λ (Equiv-Sub (^ext σ) M≋M')
-- Equiv-Sub                             σ (`ξ- M≋M' `$ N≋N')   = `ξ- Equiv-Sub σ M≋M' `$ Equiv-Sub σ N≋N'
-- Equiv-Sub                             σ (`sym M≋M')          = `sym (Equiv-Sub σ M≋M')
-- Equiv-Sub                             σ (`trans M≋M' M'≋M'') = `trans (Equiv-Sub σ M≋M') (Equiv-Sub σ M'≋M'')

-- Equiv-Ren : ∀ {M M'} δ →
--             Γ ⊢ M ≋ M' `: A →
--            -----------------------------
--             Δ ⊢ ren[ δ ] M ≋ ren[ δ ] M' `: A
-- Equiv-Ren {M = M} {M'} δ
--   rewrite sym (compatible-Sub-Ren δ M)
--         | sym (compatible-Sub-Ren δ M') = Equiv-Sub (fromRen δ)

-- Equiv-Ctx≤ : ∀ {M M'} Γ≤Δ →
--               Γ ⊢ M ≋ M' `: A →
--              -----------------------------------------
--               Δ ⊢ ctx≤[ Γ≤Δ ] M ≋ ctx≤[ Γ≤Δ ] M' `: A
-- Equiv-Ctx≤ Γ≤Δ = Equiv-Ren (fromCtx≤ Γ≤Δ)

-- data Nf : Ctx → Ty → Set
-- data Ne : Ctx → Ty → Set

-- syntax Nf Γ A = Γ ⊢⇇: A
-- syntax Ne Γ A = Γ ⊢⇉: A

-- data Nf where
--   `zero : ----------
--            Γ ⊢⇇: `N

--   `suc  :  Γ ⊢⇇: `N →
--           ------------
--            Γ ⊢⇇: `N

--   `λ_   :  Γ `, A ⊢⇇: B →
--           ----------------
--            Γ ⊢⇇: A `→ B

--   `⇑    :  Γ ⊢⇉: A →
--           -----------
--            Γ ⊢⇇: A

-- data Ne where
--   `!_   :  A ∈ Γ →
--           ---------
--            Γ ⊢⇉: A

--   `rec  :  Γ ⊢⇇: A →
--            Γ ⊢⇇: `N `→ A `→ A →
--            Γ ⊢⇉: `N →
--           ----------------------
--            Γ ⊢⇉: A

--   _`$_  :  Γ ⊢⇉: A `→ B →
--            Γ ⊢⇇: A →
--           ----------------
--            Γ ⊢⇉: B

-- record IntoTm (F : Ctx → Ty → Set) : Set where
--   field
--     embed : F Γ A → Γ ⊢Tm: A

-- open IntoTm ⦃...⦄
-- instance
--   IntoTmNf : IntoTm Nf
--   IntoTmNe : IntoTm Ne

--   embed ⦃ IntoTmNf ⦄ `zero    = `zero
--   embed ⦃ IntoTmNf ⦄ (`suc v) = `suc `$ embed v
--   embed ⦃ IntoTmNf ⦄ (`λ v)   = `λ embed v
--   embed ⦃ IntoTmNf ⦄ (`⇑ u)   = embed u

--   embed ⦃ IntoTmNe ⦄ (`! x)       = `! x
--   embed ⦃ IntoTmNe ⦄ (`rec z s u) = `rec `$ embed z `$ embed s `$ embed u
--   embed ⦃ IntoTmNe ⦄ (u `$ v)     = embed u `$ embed v

-- Nf* : Ty → Set
-- Nf* A = ∀ Γ → Γ ⊢⇇: A

-- Ne* : Ty → Set
-- Ne* A = ∀ Γ → Γ ⊢⇉: A ⊎ ⊤

-- Ne*! : Ctx → ∀ A → Ne* A
-- Ne*! Γ A Γ'
--   with Γ' Ctx≤? (Γ `, A)
-- ...  | yes Γ'≤Γ,A = inj₁ (`! ctx≤[ Γ'≤Γ,A ] here)
-- ...  | no  _      = inj₂ tt

-- Ne*rec : Nf* A → Nf* (`N `→ A `→ A) → Ne* `N → Ne* A
-- Ne*rec z* s* u* Γ = Data.Sum.map₁ (`rec (z* Γ) (s* Γ)) (u* Γ)

-- _Ne*$_ : Ne* (A `→ B) → Nf* A → Ne* B
-- (u* Ne*$ v*) Γ = Data.Sum.map₁ (_`$ v* Γ) (u* Γ)

-- data Nat : Set where
--   `zero : Nat
--   `suc  : Nat → Nat
--   `⇑    : Ne* `N → Nat

-- ↓Nat : Nat → Nf* `N
-- ↓Nat `zero    Γ = `zero
-- ↓Nat (`suc n) Γ = `suc (↓Nat n Γ)
-- ↓Nat (`⇑ u*)  Γ
--   with u* Γ
-- ... | inj₁ n    = `⇑ n
-- ... | inj₂ _    = `zero

-- record Interpret {ℓ : Level} (T : Set) : Set (Level.suc ℓ) where
--   field
--     InterpretUniv : Set ℓ
--     ⟦_⟧ : T → InterpretUniv

-- record Reflect (T : Set) (Output : T → Set) : Set where
--   field
--     ↑[_] : ∀ (t : T) → Output t

-- record Reify (T : Set) (Output : T → Set) : Set where
--   field
--     ↓[_] : ∀ (t : T) → Output t

-- open Interpret ⦃...⦄
-- open Reflect ⦃...⦄
-- open Reify ⦃...⦄
-- instance
--   InterpretTy : Interpret Ty
--   InterpretUniv ⦃ InterpretTy ⦄ = Set
--   ⟦_⟧ ⦃ InterpretTy ⦄ `N       = Nat
--   ⟦_⟧ ⦃ InterpretTy ⦄ (A `→ B) = ⟦ A ⟧ → ⟦ B ⟧

--   InterpretCtx : Interpret Ctx
--   InterpretUniv ⦃ InterpretCtx ⦄ = Set
--   ⟦_⟧ ⦃ InterpretCtx ⦄ `·       = ⊤
--   ⟦_⟧ ⦃ InterpretCtx ⦄ (Γ `, A) = ⟦ Γ ⟧ × ⟦ A ⟧

--   InterpretVar : Interpret (A ∈ Γ)
--   InterpretUniv ⦃ InterpretVar {A} {Γ} ⦄ = ⟦ Γ ⟧ → ⟦ A ⟧
--   ⟦_⟧ ⦃ InterpretVar ⦄ here      ρ = proj₂ ρ
--   ⟦_⟧ ⦃ InterpretVar ⦄ (there x) ρ = ⟦ x ⟧ (proj₁ ρ)

--   interleaved mutual
--     ReflectTy : Reflect Ty (λ A → Ne* A → ⟦ A ⟧)
--     ReifyTy : Reify Ty (λ A → ⟦ A ⟧ → Nf* A)

--     ↑[_] ⦃ ReflectTy ⦄ `N       u*   = `⇑ u*
--     ↑[_] ⦃ ReflectTy ⦄ (A `→ B) u* a = ↑[ B ] (u* Ne*$ ↓[ A ] a)

--     ↓[_] ⦃ ReifyTy ⦄ `N       v   = ↓Nat v
--     ↓[_] ⦃ ReifyTy ⦄ (A `→ B) v Γ = `λ (↓[ B ] (v (↑[ A ] (Ne*! Γ A))) (Γ `, A))

--   ReflectCtx : Reflect Ctx ⟦_⟧
--   ↑[_] ⦃ ReflectCtx ⦄ `·       = tt
--   ↑[_] ⦃ ReflectCtx ⦄ (Γ `, A) = ↑[ Γ ] , (↑[ A ] (Ne*! Γ A))

-- ⟦rec⟧ : ∀ A → ⟦ A `→ (`N `→ A `→ A) `→ `N `→ A ⟧
-- ⟦rec⟧ A z s `zero    = z
-- ⟦rec⟧ A z s (`suc n) = s n (⟦rec⟧ A z s n)
-- ⟦rec⟧ A z s (`⇑ u*)  = ↑[ A ] (Ne*rec (↓[ A ] z) (↓[ `N `→ A `→ A ] s) u*)

-- instance
--   InterpretTm : Interpret (Γ ⊢Tm: A)
--   InterpretUniv ⦃ InterpretTm {Γ} {A} ⦄ = ⟦ Γ ⟧ → ⟦ A ⟧
--   ⟦_⟧ ⦃ InterpretTm ⦄ (`! x)   ρ   = ⟦ x ⟧ ρ
--   ⟦_⟧ ⦃ InterpretTm ⦄ `zero    ρ   = `zero
--   ⟦_⟧ ⦃ InterpretTm ⦄ `suc     ρ   = `suc
--   ⟦_⟧ ⦃ InterpretTm ⦄ `rec     ρ   = ⟦rec⟧ _
--   ⟦_⟧ ⦃ InterpretTm ⦄ (`λ M)   ρ a = ⟦ M ⟧ (ρ , a)
--   ⟦_⟧ ⦃ InterpretTm ⦄ (M `$ N) ρ   = ⟦ M ⟧ ρ (⟦ N ⟧ ρ)

--   InterpretRen : Interpret (Γ ⊢Ren: Δ)
--   InterpretUniv ⦃ InterpretRen {Γ} {Δ} ⦄ = ⟦ Γ ⟧ → ⟦ Δ ⟧
--   ⟦_⟧ ⦃ InterpretRen ⦄ `·       ρ = tt
--   ⟦_⟧ ⦃ InterpretRen ⦄ (`wk δ)  ρ = ⟦ δ ⟧ (proj₁ ρ)
--   ⟦_⟧ ⦃ InterpretRen ⦄ (`ext δ) ρ = ⟦ δ ⟧ (proj₁ ρ) , proj₂ ρ

--   InterpretSub : Interpret (Γ ⊢Sub: Δ)
--   InterpretUniv ⦃ InterpretSub {Γ} {Δ} ⦄ = ⟦ Γ ⟧ → ⟦ Δ ⟧
--   ⟦_⟧ ⦃ InterpretSub ⦄ `·       ρ = tt
--   ⟦_⟧ ⦃ InterpretSub ⦄ (σ `, M) ρ = ⟦ σ ⟧ ρ , ⟦ M ⟧ ρ

-- nbe : Γ ⊢Tm: A → Γ ⊢⇇: A
-- nbe M = ↓[ _ ] (⟦ M ⟧ ↑[ _ ]) _

-- open import Axiom.Extensionality.Propositional using (Extensionality)

-- module Completeness (fun-ext : ∀ {a b} → Extensionality a b) where
--   module MeaningPreservation where
--     meaning-preserving-Ren-Var : ∀ (δ : Γ ⊢Ren: Δ)
--                                   (x : A ∈ Δ)
--                                   (ρ : ⟦ Γ ⟧) →
--                                 -----------------------------------
--                                  ⟦ ren[ δ ] x ⟧ ρ ≡ ⟦ x ⟧ (⟦ δ ⟧ ρ)
--     meaning-preserving-Ren-Var (`wk δ)  x         (ρ , a) = meaning-preserving-Ren-Var δ x ρ
--     meaning-preserving-Ren-Var (`ext δ) here      ρ       = refl
--     meaning-preserving-Ren-Var (`ext δ) (there x) (ρ , a) = meaning-preserving-Ren-Var δ x ρ

--     meaning-preserving-Ren : ∀ (δ : Γ ⊢Ren: Δ)
--                               (M : Δ ⊢Tm: A)
--                               (ρ : ⟦ Γ ⟧) →
--                             -----------------------------------
--                              ⟦ ren[ δ ] M ⟧ ρ ≡ ⟦ M ⟧ (⟦ δ ⟧ ρ)
--     meaning-preserving-Ren δ (`! x)   ρ    = meaning-preserving-Ren-Var δ x ρ
--     meaning-preserving-Ren δ `zero    ρ    = refl
--     meaning-preserving-Ren δ `suc     ρ    = refl
--     meaning-preserving-Ren δ `rec     ρ    = refl
--     meaning-preserving-Ren δ (`λ M)   ρ    = fun-ext (λ a → meaning-preserving-Ren (`ext δ) M (ρ , a))
--     meaning-preserving-Ren δ (M `$ N) ρ
--       rewrite meaning-preserving-Ren δ M ρ
--             | meaning-preserving-Ren δ N ρ = refl

--     meaning-preserving-Ren-Sub : ∀ (δ : Γ ⊢Ren: Δ)
--                                   (σ : Δ ⊢Sub: Ψ)
--                                   (ρ : ⟦ Γ ⟧) →
--                                 -----------------------------------
--                                  ⟦ ren[ δ ] σ ⟧ ρ ≡ ⟦ σ ⟧ (⟦ δ ⟧ ρ)
--     meaning-preserving-Ren-Sub δ `·       ρ = refl
--     meaning-preserving-Ren-Sub δ (σ `, M) ρ = cong₂ _,_ (meaning-preserving-Ren-Sub δ σ ρ) (meaning-preserving-Ren δ M ρ)

--     meaning-preserving-Sub-Var : ∀ (σ : Γ ⊢Sub: Δ)
--                                    (x : A ∈ Δ)
--                                    (ρ : ⟦ Γ ⟧) →
--                                  ---------------------------------
--                                   ⟦ [ σ ] x ⟧ ρ ≡ ⟦ x ⟧ (⟦ σ ⟧ ρ)
--     meaning-preserving-Sub-Var (σ `, M) here      ρ = refl
--     meaning-preserving-Sub-Var (σ `, M) (there x) ρ = meaning-preserving-Sub-Var σ x ρ

--     ⟦idRen⟧-id : ∀ (ρ : ⟦ Γ ⟧) →
--                 ----------------
--                  ⟦ idRen ⟧ ρ ≡ ρ
--     ⟦idRen⟧-id {`·}     tt      = refl
--     ⟦idRen⟧-id {Γ `, A} (ρ , a) = cong (_, a) (⟦idRen⟧-id ρ)

--     meaning-preserving-Sub : ∀ (σ : Γ ⊢Sub: Δ)
--                                (M : Δ ⊢Tm: A)
--                                (ρ : ⟦ Γ ⟧) →
--                              ---------------------------------
--                               ⟦ [ σ ] M ⟧ ρ ≡ ⟦ M ⟧ (⟦ σ ⟧ ρ)
--     meaning-preserving-Sub σ (`! x)   ρ    = meaning-preserving-Sub-Var σ x ρ
--     meaning-preserving-Sub σ `zero    ρ    = refl
--     meaning-preserving-Sub σ `suc     ρ    = refl
--     meaning-preserving-Sub σ `rec     ρ    = refl
--     meaning-preserving-Sub σ (`λ M)   ρ    = fun-ext λ a →
--       begin ⟦ [ ^ext σ ] M ⟧ (ρ , a)       ≡⟨ meaning-preserving-Sub (^ext σ) M (ρ , a) ⟩
--             ⟦ M ⟧ (⟦ wk1 σ ⟧ (ρ , a) , a)  ≡⟨ cong ⟦ M ⟧ (cong (_, a) (meaning-preserving-Ren-Sub (`wk ^id) σ (ρ , a))) ⟩
--             ⟦ M ⟧ (⟦ σ ⟧ (⟦ idRen ⟧ ρ) , a) ≡⟨ cong ⟦ M ⟧ (cong (_, a) (cong ⟦ σ ⟧ (⟦idRen⟧-id ρ))) ⟩
--             ⟦ M ⟧ (⟦ σ ⟧ ρ , a)            ∎
--       where
--         open ≡-Reasoning
--     meaning-preserving-Sub σ (M `$ N) ρ
--       rewrite meaning-preserving-Sub σ M ρ
--             | meaning-preserving-Sub σ N ρ = refl

--     ⟦idSub⟧-id : ∀ (ρ : ⟦ Γ ⟧) →
--                  -----------------
--                   ⟦ idSub ⟧ ρ ≡ ρ
--     ⟦idSub⟧-id {`·}     tt      = refl
--     ⟦idSub⟧-id {Γ `, A} (ρ , a) = cong (_, a)
--       (begin ⟦ wk1 idSub ⟧ (ρ , a)  ≡⟨ meaning-preserving-Ren-Sub (`wk ^id) ^id (ρ , a) ⟩
--              ⟦ idSub ⟧ (⟦ idRen ⟧ ρ) ≡⟨ cong ⟦ idSub ⟧ (⟦idRen⟧-id ρ) ⟩
--              ⟦ idSub ⟧ ρ            ≡⟨ ⟦idSub⟧-id ρ ⟩
--              ρ                      ∎)
--       where
--         open ≡-Reasoning

--   open MeaningPreservation

--   completeness-helper : ∀ {M M'} →
--                          Γ ⊢ M ≋ M' `: A →
--                         -------------------
--                          ⟦ M ⟧ ≡ ⟦ M' ⟧
--   completeness-helper {M = (`λ M) `$ N} `β-`→ = fun-ext λ ρ →
--     begin ⟦ M ⟧ (ρ , ⟦ N ⟧ ρ)    ≡˘⟨ cong ⟦ M ⟧ (cong (_, ⟦ N ⟧ ρ) (⟦idSub⟧-id ρ)) ⟩
--           ⟦ M ⟧ (⟦ ^id `, N ⟧ ρ) ≡˘⟨ meaning-preserving-Sub (^id `, N) M ρ ⟩
--           ⟦ [ N 1] M ⟧ ρ         ∎
--     where
--       open ≡-Reasoning
--   completeness-helper `β-`N₀                  = refl
--   completeness-helper `β-`N₁                  = refl
--   completeness-helper {M' = M'} `η-`→         = fun-ext λ ρ → fun-ext λ a → cong-app
--     (begin ⟦ wk1 M' ⟧ (ρ , a)  ≡⟨ meaning-preserving-Ren (`wk ^id) M' (ρ , a) ⟩
--            ⟦ M' ⟧ (⟦ idRen ⟧ ρ) ≡⟨ cong ⟦ M' ⟧ (⟦idRen⟧-id ρ) ⟩
--            ⟦ M' ⟧ ρ            ∎) a
--     where
--       open ≡-Reasoning
--   completeness-helper `ξ-`!                   = refl
--   completeness-helper `ξ-`zero                = refl
--   completeness-helper `ξ-`suc                 = refl
--   completeness-helper `ξ-`rec                 = refl
--   completeness-helper (`ξ-`λ M≋M')            = cong curry (completeness-helper M≋M')
--   completeness-helper (`ξ- M≋M' `$ N≋N')      = cong₂ (λ x y ρ → x ρ (y ρ)) (completeness-helper M≋M') (completeness-helper N≋N')
--   completeness-helper (`sym M'≋M)             = sym (completeness-helper M'≋M)
--   completeness-helper (`trans M≋M' M'≋M'')    = trans (completeness-helper M≋M') (completeness-helper M'≋M'')

--   completeness : ∀ {M M'} →
--                   Γ ⊢ M ≋ M' `: A →
--                  -------------------
--                   nbe M ≡ nbe M'
--   completeness M≋M' = cong (λ x → (↓[ _ ] (x _)) $ _) (completeness-helper M≋M')

-- module Soundness where
--   module GluingModel where
--     gluingTm⊥ : ∀ Γ A → Γ ⊢Tm: A → Ne* A → Set
--     syntax gluingTm⊥ Γ A M u* = Γ ⊢ M `: A ®⊥ u*
--     Γ ⊢ M `: A ®⊥ u* = ∀ {Γ'} (Γ'≤Γ : Γ' Ctx≤ Γ) → ∃[ u ] u* Γ' ≡ inj₁ u × Γ' ⊢ ctx≤[ Γ'≤Γ ] M ≋ embed u `: A

--     gluingTm⊤ : ∀ Γ A → Γ ⊢Tm: A → ⟦ A ⟧ → Set
--     syntax gluingTm⊤ Γ A M a = Γ ⊢ M `: A ®⊤ a
--     Γ ⊢ M `: A ®⊤ a = ∀ {Γ'} (Γ'≤Γ : Γ' Ctx≤ Γ) → Γ' ⊢ ctx≤[ Γ'≤Γ ] M ≋ embed (↓[ A ] a Γ') `: A

--     gluingNat : ∀ Γ → Γ ⊢Tm: `N → Nat → Set
--     syntax gluingNat Γ M a = Γ ⊢ M ®Nat a
--     gluingNat Γ M `zero    = Γ ⊢ M ≋ `zero `: `N
--     gluingNat Γ M (`suc n) = ∃[ M' ] Γ ⊢ M ≋ `suc `$ M' `: `N × Γ ⊢ M' ®Nat n
--     gluingNat Γ M (`⇑ u*)  = Γ ⊢ M `: `N ®⊥ u*

--     gluingTm : ∀ Γ A → Γ ⊢Tm: A → ⟦ A ⟧ → Set
--     syntax gluingTm Γ A M a = Γ ⊢ M `: A ® a
--     gluingTm Γ `N       M n = Γ ⊢ M ®Nat n
--     gluingTm Γ (A `→ B) M f = ∀ {Γ'} (Γ'≤Γ : Γ' Ctx≤ Γ) → ∀ {N : Γ' ⊢Tm: A} {a} → Γ' ⊢ N `: A ® a → Γ' ⊢ ctx≤[ Γ'≤Γ ] M `$ N `: B ® f a

--     gluingSub : ∀ Γ Δ → Γ ⊢Sub: Δ → ⟦ Δ ⟧ → Set
--     syntax gluingSub Γ Δ σ ρ = Γ ⊢s σ `: Δ ® ρ
--     Γ ⊢s `·     `: `·     ® ρ = ⊤
--     Γ ⊢s σ `, M `: Δ `, A ® ρ = Γ ⊢s σ `: Δ ® proj₁ ρ × Γ ⊢ M `: A ® proj₂ ρ

--   open GluingModel

--   module KripkeProperty where
--     kripkeGluingTm⊥ : ∀ {M u*} (Γ'≤Γ : Γ' Ctx≤ Γ) →
--                        Γ ⊢ M `: A ®⊥ u* →
--                       --------------------------------
--                        Γ' ⊢ ctx≤[ Γ'≤Γ ] M `: A ®⊥ u*
--     kripkeGluingTm⊥ {M = M} Γ'≤Γ ⊥M Γ''≤Γ'
--       with u , eq , equivA ← ⊥M (ctx≤[ Γ''≤Γ' ] Γ'≤Γ)
--         rewrite ctx≤[]-compose Γ''≤Γ' Γ'≤Γ M = u , eq , equivA

--     kripkeGluingNat : ∀ {M n} (Γ'≤Γ : Γ' Ctx≤ Γ) →
--                        Γ ⊢ M ®Nat n →
--                       ----------------------------
--                        Γ' ⊢ ctx≤[ Γ'≤Γ ] M ®Nat n
--     kripkeGluingNat {n = `zero}  Γ'≤Γ equiv                = Equiv-Ctx≤ Γ'≤Γ equiv
--     kripkeGluingNat {n = `suc n} Γ'≤Γ (M' , equiv , natM') = ctx≤[ Γ'≤Γ ] M' , Equiv-Ctx≤ Γ'≤Γ equiv , kripkeGluingNat Γ'≤Γ natM'
--     kripkeGluingNat {n = `⇑ x}                             = kripkeGluingTm⊥

--     kripkeGluingTm : ∀ {M a} (Γ'≤Γ : Γ' Ctx≤ Γ) →
--                       Γ ⊢ M `: A ® a →
--                      -------------------------------
--                       Γ' ⊢ ctx≤[ Γ'≤Γ ] M `: A ® a
--     kripkeGluingTm {A = `N}                            = kripkeGluingNat
--     kripkeGluingTm {A = A `→ B} {M = M} Γ'≤Γ gM Γ''≤Γ'
--       rewrite ctx≤[]-compose Γ''≤Γ' Γ'≤Γ M             = gM (ctx≤[ Γ''≤Γ' ] Γ'≤Γ)

--     kripkeGluingSub : ∀ {σ ρ} (Γ'≤Γ : Γ' Ctx≤ Γ) →
--                        Γ ⊢s σ `: Δ ® ρ →
--                       -------------------------------
--                        Γ' ⊢s ctx≤[ Γ'≤Γ ] σ `: Δ ® ρ
--     kripkeGluingSub {Δ = `·}     {σ = `·}     Γ'≤Γ tt        = tt
--     kripkeGluingSub {Δ = _ `, _} {σ = _ `, M} Γ'≤Γ (gσ , ga) = kripkeGluingSub Γ'≤Γ gσ , kripkeGluingTm {M = M} Γ'≤Γ ga

--   open KripkeProperty

--   module EquivRespect where
--     gluing⊥-respects-Equiv : ∀ {M M' u*} →
--                               Γ ⊢ M `: A ®⊥ u* →
--                               Γ ⊢ M ≋ M' `: A →
--                              --------------------
--                               Γ ⊢ M' `: A ®⊥ u*
--     gluing⊥-respects-Equiv ⊥M M≋M' Γ'≤Γ
--       with u , eq , equiv ← ⊥M Γ'≤Γ     = u , eq , `trans (`sym (Equiv-Ctx≤ Γ'≤Γ M≋M')) equiv

--     gluingNat-respects-Equiv : ∀ {M M' a} →
--                                  Γ ⊢ M ®Nat a →
--                                  Γ ⊢ M ≋ M' `: `N →
--                                 --------------------
--                                  Γ ⊢ M' ®Nat a
--     gluingNat-respects-Equiv {a = `zero}  equiv                M≋M' = `trans (`sym M≋M') equiv
--     gluingNat-respects-Equiv {a = `suc a} (M' , equiv , natM') M≋M' = M' , `trans (`sym M≋M') equiv , natM'
--     gluingNat-respects-Equiv {a = `⇑ x}                             = gluing⊥-respects-Equiv

--     gluingTm-respects-Equiv : ∀ {M M' a} →
--                                Γ ⊢ M `: A ® a →
--                                Γ ⊢ M ≋ M' `: A →
--                               -------------------
--                                Γ ⊢ M' `: A ® a
--     gluingTm-respects-Equiv {A = `N}                     = gluingNat-respects-Equiv
--     gluingTm-respects-Equiv {A = A `→ B} gM M≋M' Γ'≤Γ gN = gluingTm-respects-Equiv (gM Γ'≤Γ gN) (`ξ- (Equiv-Ctx≤ Γ'≤Γ M≋M') `$ Equiv-refl)

--   open EquivRespect

--   gluingTm⊥-var : ∀ A → Γ `, A ⊢ `! here `: A ®⊥ Ne*! Γ A
--   gluingTm⊥-var _ Γ'≤Γ,A
--     with eq ← dec-yes-irr (_ Ctx≤? _) Ctx≤-Irrelevant Γ'≤Γ,A
--       rewrite eq = `! ctx≤[ Γ'≤Γ,A ] here , refl , Equiv-refl

--   gluingTm⊥-app : ∀ {M u* N a} →
--                    Γ ⊢ M `: A `→ B ®⊥ u* →
--                    Γ ⊢ N `: A ®⊤ a →
--                   ---------------------------------------
--                    Γ ⊢ M `$ N `: B ®⊥ (u* Ne*$ ↓[ A ] a)
--   gluingTm⊥-app ⊥u* ⊤a Γ'≤Γ
--     with u , eq , equivA→B ← ⊥u* Γ'≤Γ
--       rewrite eq            = _ , refl , `ξ- equivA→B `$ ⊤a Γ'≤Γ

--   module GluingRealizability where
--     realizability-nat-top : ∀ {M n} →
--                              Γ ⊢ M ®Nat n →
--                             ------------------
--                              Γ ⊢ M `: `N ®⊤ n
--     realizability-nat-top {n = `zero}  equiv                Γ'≤Γ = Equiv-Ctx≤ Γ'≤Γ equiv
--     realizability-nat-top {n = `suc n} (M' , equiv , natM') Γ'≤Γ = `trans (Equiv-Ctx≤ Γ'≤Γ equiv) (`ξ- `ξ-`suc `$ realizability-nat-top natM' Γ'≤Γ)
--     realizability-nat-top {n = `⇑ x}   ⊥M                   Γ'≤Γ
--       with u , eq , equiv ← ⊥M Γ'≤Γ
--         rewrite eq                                               = equiv

--     realizability-bot : ∀ {M u} →
--                          Γ ⊢ M `: A ®⊥ u →
--                         -----------------------
--                          Γ ⊢ M `: A ® ↑[ A ] u
--     realizability-top : ∀ {M a} →
--                          Γ ⊢ M `: A ® a →
--                         ------------------
--                          Γ ⊢ M `: A ®⊤ a

--     gluingTm-var : ∀ A → Γ `, A ⊢ `! here `: A ® ↑[ A ] (Ne*! Γ A)
--     gluingTm-var A = realizability-bot (gluingTm⊥-var A)

--     realizability-bot {A = `N}     ⊥N           = ⊥N
--     realizability-bot {A = A `→ B} ⊥A→B Γ'≤Γ gA = realizability-bot (gluingTm⊥-app (kripkeGluingTm⊥ Γ'≤Γ ⊥A→B) (realizability-top gA))

--     realizability-top {A = `N}                     = realizability-nat-top
--     realizability-top {A = A `→ B} {M = M} gA Γ'≤Γ =
--       begin Γ'⊢M                           ≈˘⟨ `η-`→ ⟩
--             `λ wk1 Γ'⊢M `$ `! here         ≡⟨ cong (λ x → `λ x `$ _) (ctx≤[]-compose (`wk ^id) Γ'≤Γ M) ⟩
--             `λ Γ',A⊢M `$ `! here           ≡˘⟨ cong (λ x → `λ x `$ _) (ren[id]⇒id Γ',A⊢M) ⟩
--             `λ ren[ ^id ] Γ',A⊢M `$ `! here ≈⟨ `ξ-`λ (realizability-top (gA (`wk Γ'≤Γ) (gluingTm-var A)) ^id) ⟩
--             `λ _                           ∎
--       where
--         Γ'⊢M = ctx≤[ Γ'≤Γ ] M
--         Γ',A⊢M = ctx≤[ `wk Γ'≤Γ ] M
--         open Equiv-Reasoning _ _

--   open GluingRealizability

--   initial-env-Sub : Γ ⊢s ^id `: Γ ® ↑[ Γ ]
--   initial-env-Sub {`·}     = tt
--   initial-env-Sub {Γ `, A} = kripkeGluingSub (`wk ^id) initial-env-Sub , gluingTm-var A

--   SoundnessTyping : ∀ Γ A (M : Γ ⊢Tm: A) → Set
--   syntax SoundnessTyping Γ A M = Γ ⊨ M `: A
--   SoundnessTyping Γ A M = ∀ {Δ σ ρ} → Δ ⊢s σ `: Γ ® ρ → Δ ⊢ [ σ ] M `: A ® ⟦ M ⟧ ρ

--   soundness-fundamental-var : ∀ x → Γ ⊨ `! x `: A
--   soundness-fundamental-var {Γ = Γ `, B} here      {σ = σ `, M} (gσ , ga) = ga
--   soundness-fundamental-var {Γ = Γ `, B} (there x) {σ = σ `, M} (gσ , ga) = soundness-fundamental-var x gσ

--   soundness-fundamental-rec : SoundnessTyping Γ (A `→ (`N `→ A `→ A) `→ `N `→ A) `rec
--   soundness-fundamental-rec         gσ Γ'≤Δ {Z} {z} gz {Γz} Γz≤Γ' {S} {s} gs {Γs} Γs≤Γz {N} {`zero}  equiv                = gluingTm-respects-Equiv (kripkeGluingTm {M = Γz⊢Z} Γs≤Γz (kripkeGluingTm {M = Z} Γz≤Γ' gz))
--     (begin Γs⊢Z             ≈˘⟨ `β-`N₀ ⟩
--            recbody `$ `zero ≈˘⟨ `ξ- Equiv-refl `$ equiv ⟩
--            recbody `$ N     ∎)
--     where
--       Γz⊢Z = ctx≤[ Γz≤Γ' ] Z
--       Γs⊢Z = ctx≤[ Γs≤Γz ] Γz⊢Z
--       recbody = `rec `$ Γs⊢Z `$ ctx≤[ Γs≤Γz ] S
--       open Equiv-Reasoning _ _
--   soundness-fundamental-rec         gσ Γ'≤Δ {Z} {z} gz {Γz} Γz≤Γ' {S} {s} gs {Γs} Γs≤Γz {N} {`suc n} (N' , equiv , natM')
--     with gsubrecexp ← soundness-fundamental-rec gσ Γ'≤Δ gz Γz≤Γ' gs Γs≤Γz natM'                                           = gluingTm-respects-Equiv (gs Γs≤Γz natM' ^id gsubrecexp)
--     (begin ren[ ^id ] (Γs⊢S `$ N') `$ subrecexp ≡⟨ cong (_`$ subrecexp) (ren[id]⇒id (Γs⊢S `$ N')) ⟩
--            Γs⊢S `$ N' `$ subrecexp             ≈˘⟨ `β-`N₁ ⟩
--            recbody `$ (`suc `$ N')             ≈˘⟨ `ξ- Equiv-refl `$ equiv ⟩
--            recbody `$ N                        ∎)
--     where
--       Γs⊢S = ctx≤[ Γs≤Γz ] S
--       recbody = `rec `$ ctx≤[ Γs≤Γz ] ctx≤[ Γz≤Γ' ] Z `$ Γs⊢S
--       subrecexp = recbody `$ N'
--       open Equiv-Reasoning Γs _
--   soundness-fundamental-rec {A = A} gσ Γ'≤Δ {Z} {z} gz {Γz} Γz≤Γ' {S} {s} gs {Γs} Γs≤Γz {N} {`⇑ u*}  ⊥N                   = realizability-bot rec⊥
--     where
--       Γz⊢Z = ctx≤[ Γz≤Γ' ] Z
--       Γs⊢S = ctx≤[ Γs≤Γz ] S
  
--       rec⊥ : Γs ⊢ `rec `$ ctx≤[ Γs≤Γz ] Γz⊢Z `$ Γs⊢S `$ N `: _ ®⊥ Ne*rec (↓[ _ ] z) (↓[ _ ] s) u*
--       rec⊥ Δ≤Γs
--         with u , eq , equiv ← ⊥N Δ≤Γs
--           rewrite eq = _ , refl , `ξ- `ξ- `ξ- `ξ-`rec `$ equiv-z `$ equiv-s `$ equiv
--         where
--           Δ≤Γz = Δ≤Γs `∘ Γs≤Γz
--           Δ⊢S = ctx≤[ Δ≤Γz ] S
--           Δ,N⊢S = ctx≤[ `wk Δ≤Γs `∘ Γs≤Γz ] S
  
--           equiv-z =
--             begin ctx≤[ Δ≤Γs ] ctx≤[ Γs≤Γz ] Γz⊢Z ≡⟨ ctx≤[]-compose Δ≤Γs Γs≤Γz Γz⊢Z ⟩
--                   ctx≤[ Δ≤Γz ] Γz⊢Z               ≡⟨ ctx≤[]-compose Δ≤Γz Γz≤Γ' Z ⟩
--                   ctx≤[ Δ≤Γz `∘ Γz≤Γ' ] Z         ≈⟨ realizability-top gz (Δ≤Γz `∘ Γz≤Γ') ⟩
--                   embed (↓[ _ ] z _)              ∎
--             where
--               open Equiv-Reasoning _ _
  
--           s`!1 = `! there here
--           s`!0 = `! here
--           gs#0#1 = gs (`wk Δ≤Γs `∘ Γs≤Γz) (λ {Δ'} → gluingTm⊥-var `N) (`wk ^id) (gluingTm-var A)
  
--           equiv-s =
--             begin ctx≤[ Δ≤Γs ] Γs⊢S                         ≡⟨ ctx≤[]-compose Δ≤Γs Γs≤Γz S ⟩
--                   Δ⊢S                                       ≈˘⟨ `η-`→ ⟩
--                   `λ wk1 Δ⊢S `$ `! here                     ≈˘⟨ `ξ-`λ `η-`→ ⟩
--                   `λ `λ wk1 wk1 Δ⊢S `$ s`!1 `$ s`!0         ≡⟨ cong (λ x → `λ `λ wk1 x `$ s`!1 `$ s`!0) (ctx≤[]-compose (`wk ^id) Δ≤Γz S) ⟩
--                   `λ `λ wk1 Δ,N⊢S `$ s`!1 `$ s`!0           ≡˘⟨ cong (λ x → `λ `λ x) (ren[id]⇒id (wk1 Δ,N⊢S `$ s`!1 `$ s`!0)) ⟩
--                   `λ `λ ren[ ^id ] wk1 Δ,N⊢S `$ s`!1 `$ s`!0 ≈⟨ `ξ-`λ (`ξ-`λ (realizability-top gs#0#1 ^id)) ⟩
--                   embed (↓[ _ ] s _)                        ∎
--             where
--               open Equiv-Reasoning _ _

--   soundness-fundamental : ∀ M →
--                           ------------
--                            Γ ⊨ M `: A
--   soundness-fundamental (`! x)           gσ             = soundness-fundamental-var x gσ
--   soundness-fundamental `zero            gσ             = Equiv-refl
--   soundness-fundamental `suc             gσ Γ'≤Δ {N} ga = N , Equiv-refl , ga
--   soundness-fundamental `rec             gσ             = soundness-fundamental-rec gσ
--   soundness-fundamental (`λ M)   {σ = σ} gσ Γ'≤Δ {N} ga = gluingTm-respects-Equiv (soundness-fundamental M (kripkeGluingSub Γ'≤Δ gσ , ga))
--     (begin [ Γ'⊢σ `, N ] M                                  ≡˘⟨ cong (λ x → [ x `, _ ] M) ([id]⇒id Γ'⊢σ) ⟩
--            [ ^id `∘ Γ'⊢σ `, N ] M                           ≡˘⟨ cong (λ x → [ x `∘ Γ'⊢σ `, _ ] M) ([]-idRen⇒id ^id) ⟩
--            [ ([ ^id ] idRen) `∘ Γ'⊢σ `, N ] M                ≡˘⟨ cong (λ x → [ x `, _ ] M) ([]-ren[]-compose (^id `, N) (`wk ^id) Γ'⊢σ) ⟩
--            [ [ N 1] (wk1 Γ'⊢σ) `, N ] M                     ≡˘⟨ []-compose (^id `, N) (^ext Γ'⊢σ) M ⟩
--            [ N 1] [ ^ext Γ'⊢σ ] M                           ≡⟨ cong (λ x → [ N 1] [ x `, `!0 ] M) (ctx≤[]-compose (`wk ^id) Γ'≤Δ σ) ⟩
--            [ N 1] [ Γ',A⊢σ `, `!0 ] M                       ≡˘⟨ cong (λ x → [ N 1] [ ren[ x ] σ `, `!0 ] M) (`∘-identityʳ (fromCtx≤ (`wk Γ'≤Δ))) ⟩
--            [ N 1] [ ren[ ctx≤[ `wk Γ'≤Δ ] ^id ] σ `, `!0 ] M ≡˘⟨ cong (λ x → [ N 1] [ x `, `!0 ] M) (ren[]-compose Γ',A⊢Δ,A (`wk ^id) σ) ⟩
--            [ N 1] [ ren[ Γ',A⊢Δ,A ] wk1 σ `, `!0 ] M         ≡˘⟨ cong ([ N 1]_) (ren[]-[]-compose Γ',A⊢Δ,A (^ext σ) M) ⟩
--            [ N 1] ren[ Γ',A⊢Δ,A ] [ ^ext σ ] M               ≈˘⟨ `β-`→ ⟩
--            (`λ ren[ Γ',A⊢Δ,A ] [ ^ext σ ] M) `$ N            ∎)
--     where
--       `!0 = `! here
--       Γ',A⊢σ = ctx≤[ `wk Γ'≤Δ ] σ
--       Γ'⊢σ = ctx≤[ Γ'≤Δ ] σ
--       Γ',A⊢Δ,A = ^ext (fromCtx≤ Γ'≤Δ)
--       open Equiv-Reasoning _ _
--   soundness-fundamental (M `$ N) {σ = σ} gσ
--     with ⊨M ← soundness-fundamental M gσ
--        | ⊨N ← soundness-fundamental N gσ
--       with gM$N ← ⊨M ^id ⊨N                             = subst (λ x → _ ⊢ x `$ _ `: _ ® _) (ren[id]⇒id ([ σ ] M)) gM$N

--   soundness : ∀ {M} →
--               ----------------------------
--                Γ ⊢ M ≋ embed (nbe M) `: A
--   soundness {M = M} =
--     begin M                   ≡˘⟨ [id]⇒id M ⟩
--           [ ^id ] M           ≡˘⟨ ren[id]⇒id ([ ^id ] M) ⟩
--           ren[ ^id ] [ ^id ] M ≈⟨ realizability-top (soundness-fundamental M initial-env-Sub) `id ⟩
--           embed (nbe M)       ∎
--     where
--       open Equiv-Reasoning _ _
