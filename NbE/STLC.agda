{-# OPTIONS --backtracking-instance-search #-}
module NbE.STLC where

open import Data.Bool hiding (T)
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
import Relation.Binary.Reasoning.PartialSetoid as PartialSetoid-Reasoning
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
  `rec  : Ty → Tm

  `λ_   : Tm → Tm

  _`$_  : Tm → Tm → Tm

data Nf : Set
data Ne : Set

data Nf where
  `zero : Nf
  `suc  : Nf → Nf

  `λ_   : Nf → Nf

  `⇑    : Ne → Nf

data Ne where
  `!_   : ℕ → Ne

  `rec  : Ty → Nf → Nf → Ne → Ne

  _`$_  : Ne → Nf → Ne

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

infixl 30 _`,s_
_`,s_ : Sub → Tm → Sub
_`,s_ σ M = λ where
  zero    → M
  (suc x) → σ x

ext2ren : Ext → Ren
ext2ren φ = φ .shift +_

ren2sub : Ren → Sub
ren2sub = _∘_ (`!_)

variable
  x x' x'' x₀ x₁ x₂ x₃ y y' y'' y₀ y₁ y₂ y₃ z z' z'' z₀ z₁ z₂ z₃ : ℕ
  Γ Γ' Γ'' Γ₀ Γ₁ Γ₂ Γ₃ Δ Δ' Δ'' Δ₀ Δ₁ Δ₂ Δ₃ Ψ Ψ' Ψ'' Ψ₀ Ψ₁ Ψ₂ Ψ₃ : Ctx
  A A' A'' A₀ A₁ A₂ A₃ B B' B'' B₀ B₁ B₂ B₃ C C' C'' C₀ C₁ C₂ C₃ : Ty
  L L' L'' L₀ L₁ L₂ L₃ M M' M'' M₀ M₁ M₂ M₃ N N' N'' N₀ N₁ N₂ N₃ : Tm
  U U' U'' U₀ U₁ U₂ U₃ V V' V'' V₀ V₁ V₂ V₃ W W' W'' W₀ W₁ W₂ W₃ : Nf
  R R' R'' R₀ R₁ R₂ R₃ S S' S'' S₀ S₁ S₂ S₃ T T' T'' T₀ T₁ T₂ T₃ : Ne
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

`,s-≈-cong : σ ≈ τ → M ≡ N → σ `,s M ≈ τ `,s N
`,s-≈-cong equiv refl = λ where
  zero    → refl
  (suc x) → equiv _

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

  `rec  : ----------------------------------------------
           Γ ⊢ `rec A `: A `→ (`N `→ A `→ A) `→ `N `→ A

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

infixl 30 ⊢s_`,s_
⊢s_`,s_ :  Γ ⊢s σ `: Δ →
           Γ ⊢ M `: A →
          ------------------------
           Γ ⊢s σ `,s M `: Δ `, A
⊢s ⊢σ `,s ⊢M = ⊢sub λ where
  here        → ⊢M
  (there x∈Γ) → ⊢σ .get x∈Γ

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

idRen : Ren
idRen = ^id

idSub : Sub
idSub = ^id

infix 30 -`,s_
-`,s_ : Tm → Sub
-`,s_ M = ^id `,s M

infix 30 ⊢s-`,s_
⊢s-`,s_ :  Γ ⊢ M `: A →
          -----------------------
           Γ ⊢s -`,s M `: Γ `, A
⊢s-`,s ⊢M = ⊢sub λ where
  here        → ⊢M
  (there x∈Γ) → `! x∈Γ

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
  ren[_]_ ⦃ AppRenTm ⦄ δ (`rec A) = `rec A
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
  ren[≈]⇒≡ ⦃ AppRenEquiv⇒EqTm ⦄ (`rec A) equiv = refl
  ren[≈]⇒≡ ⦃ AppRenEquiv⇒EqTm ⦄ (`λ M)   equiv = cong `λ_ (ren[≈]⇒≡ M (Ren^ext-respects-≈ equiv))
  ren[≈]⇒≡ ⦃ AppRenEquiv⇒EqTm ⦄ (M `$ N) equiv = cong₂ _`$_ (ren[≈]⇒≡ M equiv) (ren[≈]⇒≡ N equiv)

  AppRenId⇒IdTm : AppRenId⇒Id Tm
  ren[id]⇒id ⦃ AppRenId⇒IdTm ⦄ {x = `! x}   = cong `!_ ren[id]⇒id
  ren[id]⇒id ⦃ AppRenId⇒IdTm ⦄ {x = `zero}  = refl
  ren[id]⇒id ⦃ AppRenId⇒IdTm ⦄ {x = `suc}   = refl
  ren[id]⇒id ⦃ AppRenId⇒IdTm ⦄ {x = `rec A} = refl
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

ren[]-distrib-`,s : ren[ δ ] (σ `,s M) ≈ ren[ δ ] σ `,s ren[ δ ] M
ren[]-distrib-`,s zero    = refl
ren[]-distrib-`,s (suc x) = refl

ren[]Ren-≈-cong : δ ≈ δ' → ren[ ε ] δ ≈ ren[ ε ] δ'
ren[]Ren-≈-cong {ε = ε} equiv = cong ε ∘ equiv

ren[]Sub-≈-cong : σ ≈ σ' → ren[ δ ] σ ≈ ren[ δ ] σ'
ren[]Sub-≈-cong {δ = δ} equiv = cong ren[ δ ]_ ∘ equiv

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
  ^ext ⦃ CtxExtSub ⦄ σ = wk1 σ `,s `! zero

  ⊢CtxExtSub : ⊢CtxExt Sub
  ⊢^ext ⦃ ⊢CtxExtSub ⦄ ⊢σ = ⊢s ⊢wk1 ⊢σ `,s `! here 

Sub^ext^id≈^id : ^ext ^id ≈ ^id ⦃ CtxIdSub ⦄
Sub^ext^id≈^id zero    = refl
Sub^ext^id≈^id (suc _) = refl

Sub^ext-≈-cong : σ ≈ τ → ^ext σ ≈ ^ext τ
Sub^ext-≈-cong equiv = `,s-≈-cong (ren[]Sub-≈-cong equiv) refl

ren2sub-^ext : ∀ δ → ren2sub (^ext δ) ≈ ^ext (ren2sub δ)
ren2sub-^ext δ zero    = refl
ren2sub-^ext δ (suc x) = refl

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
  ⊢[ ⊢L 1] ⊢x = ⊢[ ⊢s-`,s ⊢L ] ⊢x
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
  [_]_ ⦃ AppSubTm ⦄ σ (`rec A) = `rec A
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
  [≈]⇒≡ ⦃ AppSubEquiv⇒EqTm ⦄ (`rec A) equiv = refl
  [≈]⇒≡ ⦃ AppSubEquiv⇒EqTm ⦄ (`λ M)   equiv = cong `λ_ ([≈]⇒≡ M (Sub^ext-≈-cong equiv))
  [≈]⇒≡ ⦃ AppSubEquiv⇒EqTm ⦄ (M `$ N) equiv = cong₂ _`$_ ([≈]⇒≡ M equiv) ([≈]⇒≡ N equiv)

  AppSubId⇒IdTm : AppSubId⇒Id Tm
  [id]⇒id ⦃ AppSubId⇒IdTm ⦄ {x = `! x}   = [id]⇒id ⦃ _ ⦄ ⦃ AppSubId⇒IdVar ⦄
  [id]⇒id ⦃ AppSubId⇒IdTm ⦄ {x = `zero}  = refl
  [id]⇒id ⦃ AppSubId⇒IdTm ⦄ {x = `suc}   = refl
  [id]⇒id ⦃ AppSubId⇒IdTm ⦄ {x = `rec A} = refl
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

[]Ren-≈-cong : δ ≈ δ' → [ σ ] δ ≈ [ σ ] δ'
[]Ren-≈-cong {σ = σ} equiv = cong σ ∘ equiv

[]Sub-≈-cong : σ ≈ σ' → [ τ ] σ ≈ [ τ ] σ'
[]Sub-≈-cong {τ = τ} equiv = cong [ τ ]_ ∘ equiv

[≈]Ren⇒≈ : σ ≈ τ → [ σ ] δ' ≈ [ τ ] δ'
[≈]Ren⇒≈ equiv _ = equiv _

[≈]Sub⇒≈ : σ ≈ τ → [ σ ] σ' ≈ [ τ ] σ'
[≈]Sub⇒≈ {σ' = σ'} equiv x = [≈]⇒≡ (σ' x) equiv

[id]Sub⇒≈ : [ ^id ] σ ≈ σ
[id]Sub⇒≈ _ = [id]⇒id

[]-distrib-`,s : [ σ ] (τ `,s M) ≈ [ σ ] τ `,s [ σ ] M
[]-distrib-`,s zero    = refl
[]-distrib-`,s (suc x) = refl

record AppRenCompose X ⦃ AppRenX : AppRen X ⦄ : Set where
  field
    ren[]-compose : ∀ δ ε (x : X) →
                    -------------------------------------------
                     ren[ δ ] ren[ ε ] x ≡ ren[ ren[ δ ] ε ] x
open AppRenCompose ⦃...⦄
instance
  AppRenComposeVar : AppRenCompose ℕ
  ren[]-compose ⦃ AppRenComposeVar ⦄ _ _ _ = refl

  AppRenComposeTm : AppRenCompose Tm
  ren[]-compose ⦃ AppRenComposeTm ⦄ δ ε (`! x)   = cong `!_ (ren[]-compose δ ε x)
  ren[]-compose ⦃ AppRenComposeTm ⦄ δ ε `zero    = refl
  ren[]-compose ⦃ AppRenComposeTm ⦄ δ ε `suc     = refl
  ren[]-compose ⦃ AppRenComposeTm ⦄ δ ε (`rec A) = refl
  ren[]-compose ⦃ AppRenComposeTm ⦄ δ ε (`λ M)   = cong `λ_ (trans (ren[]-compose (^ext δ) (^ext ε) M) (ren[≈]⇒≡ M ren[^ext]^ext≈^extren[]Ren))
  ren[]-compose ⦃ AppRenComposeTm ⦄ δ ε (M `$ N) = cong₂ _`$_ (ren[]-compose δ ε M) (ren[]-compose δ ε N)

  AppRenComposeRen : AppRenCompose Ren
  ren[]-compose ⦃ AppRenComposeRen ⦄ _ _ _ = refl

ren[]Sub-composeEquiv : ∀ δ ε (σ : Sub) →
                        -------------------------------------------
                         ren[ δ ] ren[ ε ] σ ≈ ren[ ren[ δ ] ε ] σ
ren[]Sub-composeEquiv δ ε = ren[]-compose δ ε ∘_

ren[^ext]wk1≈wk1ren[]Tm : ren[ ^ext δ ] (wk1 M) ≡ wk1 (ren[ δ ] M)
ren[^ext]wk1≈wk1ren[]Tm {M = M} =
  begin ren[ ^ext _ ] ren[ suc ] M ≡⟨ ren[]-compose (^ext _) suc M ⟩
        ren[ wk1 _ ] M             ≡˘⟨ ren[]-compose suc _ M ⟩
        ren[ suc ] ren[ _ ] M      ∎
  where
    open ≡-Reasoning

ren[^ext]^ext≈^extren[]Sub : ren[ ^ext δ ] (^ext σ) ≈ ^ext (ren[ δ ] σ)
ren[^ext]^ext≈^extren[]Sub = ≈-trans ren[]-distrib-`,s (`,s-≈-cong (λ _ → ren[^ext]wk1≈wk1ren[]Tm) refl)

record AppSubRenCompose X ⦃ AppRenX : AppRen X ⦄ ⦃ AppSubX : AppSub X ⦄ ⦃ AppRenXOutput : AppRen (AppSubResult ⦃ AppSubX ⦄) ⦄ : Set where
  field
    ren[]-[]-compose : ∀ δ σ (x : X) →
                       -------------------------------------
                        ren[ δ ] [ σ ] x ≡ [ ren[ δ ] σ ] x
open AppSubRenCompose ⦃...⦄

instance
  AppSubRenComposeVar : AppSubRenCompose ℕ
  ren[]-[]-compose ⦃ AppSubRenComposeVar ⦄ _ _ _ = refl

  AppSubRenComposeTm : AppSubRenCompose Tm
  ren[]-[]-compose ⦃ AppSubRenComposeTm ⦄ δ σ (`! x)   = ren[]-[]-compose δ σ x
  ren[]-[]-compose ⦃ AppSubRenComposeTm ⦄ δ σ `zero    = refl
  ren[]-[]-compose ⦃ AppSubRenComposeTm ⦄ δ σ `suc     = refl
  ren[]-[]-compose ⦃ AppSubRenComposeTm ⦄ δ σ (`rec A) = refl
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

record AppRenSubCompose X ⦃ AppRenX : AppRen X ⦄ ⦃ AppSubX : AppSub X ⦄ : Set where
  field
    []-ren[]-compose : ∀ σ δ (x : X) →
                       ----------------------------------
                        [ σ ] ren[ δ ] x ≡ [ [ σ ] δ ] x
open AppRenSubCompose ⦃...⦄

instance
  AppRenSubComposeVar : AppRenSubCompose ℕ
  []-ren[]-compose ⦃ AppRenSubComposeVar ⦄ _ _ _ = refl

  AppRenSubComposeTm : AppRenSubCompose Tm
  []-ren[]-compose ⦃ AppRenSubComposeTm ⦄ σ δ (`! x)   = []-ren[]-compose σ δ x
  []-ren[]-compose ⦃ AppRenSubComposeTm ⦄ σ δ `zero    = refl
  []-ren[]-compose ⦃ AppRenSubComposeTm ⦄ σ δ `suc     = refl
  []-ren[]-compose ⦃ AppRenSubComposeTm ⦄ σ δ (`rec A) = refl
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

[`,s]wk1≡[]Tm : ∀ (M : Tm) → [ σ `,s N ] (wk1 M) ≡ [ σ ] M
[`,s]wk1≡[]Tm M = []-ren[]-compose (_ `,s _) suc M

[`,s]wk1≡[]Sub : ∀ (τ : Sub) → [ σ `,s N ] (wk1 τ) ≈ [ σ ] τ
[`,s]wk1≡[]Sub τ = []-ren[]Sub-compose-Equiv (_ `,s _) suc τ

[^ext]wk1≈wk1[]Tm : ∀ (M : Tm) → [ ^ext σ ] (wk1 M) ≡ wk1 ([ σ ] M)
[^ext]wk1≈wk1[]Tm M = trans ([`,s]wk1≡[]Tm M) (sym (ren[]-[]-compose suc _ M))

[^ext]^ext≈^ext[]Sub : [ ^ext σ ] (^ext τ) ≈ ^ext ([ σ ] τ)
[^ext]^ext≈^ext[]Sub {τ = τ} = ≈-trans []-distrib-`,s (`,s-≈-cong ([^ext]wk1≈wk1[]Tm ∘ τ) refl)

record AppSubCompose X ⦃ AppSubX : AppSub X ⦄  ⦃ AppSubXOutput : AppSub (AppSubResult ⦃ AppSubX ⦄) ⦄ : Set where
  field
    []-compose : ∀ σ τ (x : X) →
                 -------------------------------------------------
                  [ σ ] [ τ ] x ≡ AppSubResultMap ([ [ σ ] τ ] x)
open AppSubCompose ⦃...⦄

instance
  AppSubComposeVar : AppSubCompose ℕ
  []-compose ⦃ AppSubComposeVar ⦄ _ _ _ = refl

  AppSubComposeTm : AppSubCompose Tm
  []-compose ⦃ AppSubComposeTm ⦄ σ τ (`! x)   = []-compose σ τ x
  []-compose ⦃ AppSubComposeTm ⦄ σ τ `zero    = refl
  []-compose ⦃ AppSubComposeTm ⦄ σ τ `suc     = refl
  []-compose ⦃ AppSubComposeTm ⦄ σ τ (`rec A) = refl
  []-compose ⦃ AppSubComposeTm ⦄ σ τ (`λ M)   = cong `λ_
    (begin [ ^ext σ ] [ ^ext τ ] M ≡⟨ []-compose (^ext σ) (^ext τ) M ⟩
           [ [ ^ext σ ] ^ext τ ] M ≡⟨ [≈]⇒≡ M [^ext]^ext≈^ext[]Sub ⟩
           [ ^ext ([ σ ] τ) ] M    ∎)
    where
      open ≡-Reasoning
  []-compose ⦃ AppSubComposeTm ⦄ σ τ (M `$ N) = cong₂ _`$_ ([]-compose σ τ M) ([]-compose σ τ N)

  AppSubComposeRen : AppSubCompose Ren
  []-compose ⦃ AppSubComposeRen ⦄ σ τ δ = refl

[]Sub-compose-Equiv : ∀ σ τ (σ' : Sub) →
                      ---------------------------------
                       [ σ ] [ τ ] σ' ≈ [ [ σ ] τ ] σ'
[]Sub-compose-Equiv σ τ σ' = []-compose σ τ ∘ σ'

record CompatibleSubRen X ⦃ AppRenX : AppRen X ⦄ ⦃ AppSubX : AppSub X ⦄ : Set where
  field
    compatible-Sub-Ren : ∀ δ (x : X) →
                         ------------------------------------------------
                          [ ren2sub δ ] x ≡ AppSubResultMap (ren[ δ ] x)
open CompatibleSubRen ⦃...⦄

instance
  CompatibleSubRenVar : CompatibleSubRen ℕ
  compatible-Sub-Ren ⦃ CompatibleSubRenVar ⦄ δ x = refl

  CompatibleSubRenTm : CompatibleSubRen Tm
  compatible-Sub-Ren ⦃ CompatibleSubRenTm ⦄ δ (`! x)   = compatible-Sub-Ren δ x
  compatible-Sub-Ren ⦃ CompatibleSubRenTm ⦄ δ `zero    = refl
  compatible-Sub-Ren ⦃ CompatibleSubRenTm ⦄ δ `suc     = refl
  compatible-Sub-Ren ⦃ CompatibleSubRenTm ⦄ δ (`rec A) = refl
  compatible-Sub-Ren ⦃ CompatibleSubRenTm ⦄ δ (`λ M)   = cong `λ_ (trans (sym ([≈]⇒≡ M (ren2sub-^ext δ))) (compatible-Sub-Ren (^ext δ) M))
  compatible-Sub-Ren ⦃ CompatibleSubRenTm ⦄ δ (M `$ N) = cong₂ _`$_ (compatible-Sub-Ren δ M) (compatible-Sub-Ren δ N)

  CompatibleSubRenRen : CompatibleSubRen Ren
  compatible-Sub-Ren ⦃ CompatibleSubRenRen ⦄ δ ε = refl

compatible-Sub-RenSub-Equiv : ∀ δ (σ : Sub) →
                              ------------------------------
                               [ ren2sub δ ] σ ≈ ren[ δ ] σ
compatible-Sub-RenSub-Equiv δ = compatible-Sub-Ren δ ∘_

data _⊢_≋_`:_ : Ctx → Tm → Tm → Ty → Set where
  `β-`→    : ∀ {M N} →
              Γ `, A ⊢ M `: B →
              Γ ⊢ N `: A →
             ---------------------------------
              Γ ⊢ (`λ M) `$ N ≋ [ N 1] M `: B

  `β-`N₀   : ∀ {M N} →
              Γ ⊢ M `: A →
              Γ ⊢ N `: `N `→ A `→ A →
             ----------------------------------------
              Γ ⊢ `rec A `$ M `$ N `$ `zero ≋ M `: A

  `β-`N₁   : ∀ {M N L} →
              Γ ⊢ M `: A →
              Γ ⊢ N `: `N `→ A `→ A →
              Γ ⊢ L `: `N →
             ------------------------------------------------------------------------------
              Γ ⊢ `rec A `$ M `$ N `$ (`suc `$ L) ≋ N `$ L `$ (`rec A `$ M `$ N `$ L) `: A

  `η-`→    : ∀ {M} →
              Γ ⊢ M `: A `→ B →
             ------------------------------------
              Γ ⊢ `λ wk1 M `$ `! 0 ≋ M `: A `→ B

  `ξ-`!    : ∀ {x} →
              x `: A ∈ Γ →
             -------------------------
              Γ ⊢ `! x ≋ `! x `: A

  `ξ-`zero : -------------------------
              Γ ⊢ `zero ≋ `zero `: `N

  `ξ-`suc  : -----------------------------
              Γ ⊢ `suc ≋ `suc `: `N `→ `N

  `ξ-`rec  : -------------------------------------------------------
              Γ ⊢ `rec A ≋ `rec A `: A `→ (`N `→ A `→ A) `→ `N `→ A

  `ξ-`λ_   : ∀ {M M'} →
              Γ `, A ⊢ M ≋ M' `: B →
             ----------------------------
              Γ ⊢ `λ M ≋ `λ M' `: A `→ B

  `ξ-_`$_  : ∀ {M M' N N'} →
              Γ ⊢ M ≋ M' `: A `→ B →
              Γ ⊢ N ≋ N' `: A →
             ----------------------------
              Γ ⊢ M `$ N ≋ M' `$ N' `: B

  `sym     : ∀ {M M'} →
              Γ ⊢ M ≋ M' `: A →
             -------------------
              Γ ⊢ M' ≋ M `: A

  `trans   : ∀ {M M' M''} →
              Γ ⊢ M ≋ M' `: A →
              Γ ⊢ M' ≋ M'' `: A →
             ---------------------
              Γ ⊢ M ≋ M'' `: A

≋-refl : ∀ {M} → Γ ⊢ M `: A → Γ ⊢ M ≋ M `: A
≋-refl (`! x∈Γ)   = `ξ-`! x∈Γ
≋-refl `zero      = `ξ-`zero
≋-refl `suc       = `ξ-`suc
≋-refl `rec       = `ξ-`rec
≋-refl (`λ ⊢M)    = `ξ-`λ ≋-refl ⊢M
≋-refl (⊢M `$ ⊢N) = `ξ- ≋-refl ⊢M `$ ≋-refl ⊢N

≋-IsPartialEquivalence : IsPartialEquivalence (Γ ⊢_≋_`: A)
≋-IsPartialEquivalence = record
                         { sym = `sym
                         ; trans = `trans
                         }

≋-PartialSetoid : Ctx → Ty → PartialSetoid _ _
≋-PartialSetoid Γ A = record
                      { Carrier = Tm
                      ; _≈_ = Γ ⊢_≋_`: A
                      ; isPartialEquivalence = ≋-IsPartialEquivalence
                      }

module ≋-Reasoning Γ A = PartialSetoid-Reasoning (≋-PartialSetoid Γ A)

≋-[] : ∀ {M M' σ} →
        Γ ⊢s σ `: Δ →
        Δ ⊢ M ≋ M' `: A →
       -----------------------------
        Γ ⊢ [ σ ] M ≋ [ σ ] M' `: A
≋-[] {M = (`λ M) `$ N} {σ = σ} ⊢σ (`β-`→ ⊢M ⊢N) =
  begin (`λ [ ^ext σ ] M) `$ [ σ ] N         ≈⟨ `β-`→ (⊢[ ⊢^ext ⊢σ ] ⊢M) (⊢[ ⊢σ ] ⊢N) ⟩
        [ [ σ ] N 1] [ ^ext σ ] M            ≡⟨ []-compose (-`,s [ σ ] N) (^ext σ) M ⟩
        [ [ [ σ ] N 1] ^ext σ ] M            ≡⟨ [≈]⇒≡ M []-distrib-`,s ⟩
        [ [ [ σ ] N 1] wk1 σ `,s [ σ ] N ] M ≡⟨ [≈]⇒≡ M (`,s-≈-cong ([`,s]wk1≡[]Sub σ) refl) ⟩
        [ [ ^id ] σ `,s [ σ ] N ] M          ≡⟨ [≈]⇒≡ M (`,s-≈-cong [id]Sub⇒≈ refl) ⟩
        [ [ σ ] idSub `,s [ σ ] N ] M        ≡˘⟨ [≈]⇒≡ M []-distrib-`,s ⟩
        [ [ σ ] (-`,s N) ] M                 ≡˘⟨ []-compose σ (-`,s N) M ⟩
        [ σ ] [ N 1] M                       ∎
  where
    open ≋-Reasoning _ _
≋-[] ⊢σ (`β-`N₀ ⊢M ⊢N) = `β-`N₀ (⊢[ ⊢σ ] ⊢M) (⊢[ ⊢σ ] ⊢N)
≋-[] ⊢σ (`β-`N₁ ⊢M ⊢N ⊢L) = `β-`N₁ (⊢[ ⊢σ ] ⊢M) (⊢[ ⊢σ ] ⊢N) (⊢[ ⊢σ ] ⊢L)
≋-[] {M' = M} {σ = σ} ⊢σ (`η-`→ ⊢M) =
  begin `λ [ ^ext σ ] wk1 M `$ `! 0 ≈⟨ ≋-refl (`λ ⊢[ ⊢^ext ⊢σ ] ⊢wk1 ⊢M `$ `! here) ⟩
        `λ [ ^ext σ ] wk1 M `$ `! 0 ≡⟨ cong (λ x → `λ x `$ _) ([]-ren[]-compose (^ext σ) suc M) ⟩
        `λ [ wk1 σ ] M `$ `! 0      ≡˘⟨ cong (λ x → `λ x `$ _) (ren[]-[]-compose suc σ M) ⟩
        `λ wk1 [ σ ] M `$ `! 0      ≈⟨ `η-`→ (⊢[ ⊢σ ] ⊢M) ⟩
        [ σ ] M                     ∎
  where
    open ≋-Reasoning _ _
≋-[] ⊢σ (`ξ-`! x∈Δ) = ≋-refl (⊢σ .get x∈Δ)
≋-[] ⊢σ `ξ-`zero = `ξ-`zero
≋-[] ⊢σ `ξ-`suc = `ξ-`suc
≋-[] ⊢σ `ξ-`rec = `ξ-`rec
≋-[] ⊢σ (`ξ-`λ M≋M') = `ξ-`λ (≋-[] (⊢^ext ⊢σ) M≋M')
≋-[] ⊢σ (`ξ- M≋M' `$ N≋N') = `ξ- ≋-[] ⊢σ M≋M' `$ ≋-[] ⊢σ N≋N'
≋-[] ⊢σ (`sym M≋M') = `sym (≋-[] ⊢σ M≋M')
≋-[] ⊢σ (`trans M≋M' M'≋M'') = `trans (≋-[] ⊢σ M≋M') (≋-[] ⊢σ M'≋M'')

≋-ren[] : ∀ {M M' δ} →
            Γ ⊢r δ `: Δ →
            Δ ⊢ M ≋ M' `: A →
           -----------------------------
            Γ ⊢ ren[ δ ] M ≋ ren[ δ ] M' `: A
≋-ren[] {M = M} {M'} {δ} ⊢δ
  rewrite sym (compatible-Sub-Ren δ M)
        | sym (compatible-Sub-Ren δ M') = ≋-[] (⊢ren2sub ⊢δ)

infix 25 _⊢_⇇_
infix 25 _⊢_⇉_
data _⊢_⇇_ : Ctx → Nf → Ty → Set
data _⊢_⇉_ : Ctx → Ne → Ty → Set

data _⊢_⇇_ where
  `zero : ----------------
           Γ ⊢ `zero ⇇ `N

  `suc  :  Γ ⊢ U ⇇ `N →
          -----------------
           Γ ⊢ `suc U ⇇ `N

  `λ_   :  Γ `, A ⊢ U ⇇ B →
          -------------------
           Γ ⊢ `λ U ⇇ A `→ B

  `⇑    :  Γ ⊢ R ⇉ A →
          --------------
           Γ ⊢ `⇑ R ⇇ A

data _⊢_⇉_ where
  `!_   :  x `: A ∈ Γ →
          --------------
           Γ ⊢ `! x ⇉ A

  `rec  :  Γ ⊢ U ⇇ A →
           Γ ⊢ V ⇇ `N `→ A `→ A →
           Γ ⊢ R ⇉ `N →
          ----------------------
           Γ ⊢ `rec A U V R ⇉ A

  _`$_  :  Γ ⊢ R ⇉ A `→ B →
           Γ ⊢ U ⇇ A →
          ------------------
           Γ ⊢ R `$ U ⇉ B

instance
  ⊢ClassNf : ⊢Class Nf Ty
  ⊢Judgement ⦃ ⊢ClassNf ⦄ = _⊢_⇇_

  ⊢ClassNe : ⊢Class Ne Ty
  ⊢Judgement ⦃ ⊢ClassNe ⦄ = _⊢_⇉_

record IntoTm (X : Set) : Set where
  field
    embed : X → Tm
open IntoTm ⦃...⦄

record ⊢IntoTm X ⦃ IntoTmX : IntoTm X ⦄ ⦃ ⊢ClassX : ⊢Class X Ty ⦄ : Set where
  field
    ⊢embed : ∀ {x : X} → ⊢Judgement Γ x A → Γ ⊢ embed x `: A
open ⊢IntoTm ⦃...⦄

instance
  IntoTmNf : IntoTm Nf
  IntoTmNe : IntoTm Ne

  embed ⦃ IntoTmNf ⦄ `zero    = `zero
  embed ⦃ IntoTmNf ⦄ (`suc U) = `suc `$ embed U
  embed ⦃ IntoTmNf ⦄ (`λ U)   = `λ embed U
  embed ⦃ IntoTmNf ⦄ (`⇑ R)   = embed R

  embed ⦃ IntoTmNe ⦄ (`! x)         = `! x
  embed ⦃ IntoTmNe ⦄ (`rec A U V R) = `rec A `$ embed U `$ embed V `$ embed R
  embed ⦃ IntoTmNe ⦄ (R `$ U)       = embed R `$ embed U

  ⊢IntoTmNf : ⊢IntoTm Nf
  ⊢IntoTmNe : ⊢IntoTm Ne

  ⊢embed ⦃ ⊢IntoTmNf ⦄ `zero     = `zero
  ⊢embed ⦃ ⊢IntoTmNf ⦄ (`suc ⊢U) = `suc `$ ⊢embed ⊢U
  ⊢embed ⦃ ⊢IntoTmNf ⦄ (`λ ⊢U)   = `λ ⊢embed ⊢U
  ⊢embed ⦃ ⊢IntoTmNf ⦄ (`⇑ ⊢R)   = ⊢embed ⊢R

  ⊢embed ⦃ ⊢IntoTmNe ⦄ (`! x∈Γ)        = `! x∈Γ
  ⊢embed ⦃ ⊢IntoTmNe ⦄ (`rec ⊢U ⊢V ⊢R) = `rec `$ ⊢embed ⊢U `$ ⊢embed ⊢V `$ ⊢embed ⊢R
  ⊢embed ⦃ ⊢IntoTmNe ⦄ (⊢R `$ ⊢U)      = ⊢embed ⊢R `$ ⊢embed ⊢U

infixr 37 `λ_﹫_
infixr 36 `suc∙_
infixr 36 `rec_∙_
infixr 36 `rec_∙_∙_
infixr 36 `rec_∙_∙_∙_
infix  37 `#_

data Dom : Set
data DomNe : Set
data DomNf : Set

Env = ℕ → Dom

data Dom where
  `λ_﹫_     : Tm → Env → Dom

  `zero     : Dom
  `suc      : Dom
  `suc∙_    : Dom → Dom
  `rec      : Ty → Dom
  `rec_∙_   : Ty → Dom → Dom
  `rec_∙_∙_ : Ty → Dom → Dom → Dom

  `⇑        : Ty → DomNe → Dom

data DomNe where
  `#_         : ℕ → DomNe

  _`$_        : DomNe → DomNf → DomNe

  `rec_∙_∙_∙_ : Ty → Dom → Dom → DomNe → DomNe

data DomNf where
  `⇓ : Ty → Dom → DomNf

variable
  ρ ρ' ρ'' ρ₀ ρ₁ ρ₂ ρ₃ ω ω' ω'' ω₀ ω₁ ω₂ ω₃ : Env
  l l' l'' l₀ l₁ l₂ l₃ m m' m'' m₀ m₁ m₂ m₃ n n' n'' n₀ n₁ n₂ n₃ : Dom
  u u' u'' u₀ u₁ u₂ u₃ v v' v'' v₀ v₁ v₂ v₃ w w' w'' w₀ w₁ w₂ w₃ : DomNf
  r r' r'' r₀ r₁ r₂ r₃ s s' s'' s₀ s₁ s₂ s₃ t t' t'' t₀ t₁ t₂ t₃ : DomNe

infixl 30 _`,E_
_`,E_ : Env → Dom → Env
_`,E_ ρ m = λ where
  zero    → m
  (suc x) → ρ x

dropE : Env → Env
dropE = _∘ suc

infix 25 Tm⟦_⟧_↘_
infix 25 ∥_∙_∥↘_
infix 25 ∥rec_∙_∙_∙_∥↘_

record Evaluation (X : Set) (Y : Set) : Set₁ where
  infix 25 ⟦_⟧_↘_
  field
    ⟦_⟧_↘_ : X → Env → Y → Set

open Evaluation ⦃...⦄

data Tm⟦_⟧_↘_ : Tm → Env → Dom → Set
data ∥_∙_∥↘_ : Dom → Dom → Dom → Set
data ∥rec_∙_∙_∙_∥↘_ : Ty → Dom → Dom → Dom → Dom → Set

instance
  EvaluationTm : Evaluation Tm Dom
  ⟦_⟧_↘_ ⦃ EvaluationTm ⦄ = Tm⟦_⟧_↘_

data Tm⟦_⟧_↘_ where
  `!-    : --------------------
            Tm⟦ `! x ⟧ ρ ↘ ρ x

  `λ-    : -------------------------
            Tm⟦ `λ M ⟧ ρ ↘ `λ M ﹫ ρ

  _`$_&_ :  ⟦ M ⟧ ρ ↘ m →
            ⟦ N ⟧ ρ ↘ n →
            ∥ m ∙ n ∥↘ l →
           --------------------
            Tm⟦ M `$ N ⟧ ρ ↘ l

  `zero  : -----------------------
            Tm⟦ `zero ⟧ ρ ↘ `zero

  `suc   : ---------------------
            Tm⟦ `suc ⟧ ρ ↘ `suc

  `rec   : -------------------------
            Tm⟦ `rec A ⟧ ρ ↘ `rec A

data ∥_∙_∥↘_ where
  `λ-       :  ⟦ M ⟧ ρ `,E n ↘ l →
              ---------------------
               ∥ `λ M ﹫ ρ ∙ n ∥↘ l

  `suc      : -----------------------
               ∥ `suc ∙ n ∥↘ `suc∙ n

  `rec      : ----------------------------
               ∥ `rec A ∙ n ∥↘ `rec A ∙ n

  `rec-∙-   : --------------------------------------
               ∥ `rec A ∙ n ∙ n' ∥↘ `rec A ∙ n ∙ n'

  `rec-∙-∙- :  ∥rec A ∙ n ∙ n' ∙ m ∥↘ l →
              ----------------------------
               ∥ `rec A ∙ n ∙ n' ∙ m ∥↘ l

  `⇑        : -------------------------------------------
               ∥ `⇑ (A `→ B) r ∙ n ∥↘ `⇑ B (r `$ `⇓ A n)

data ∥rec_∙_∙_∙_∥↘_ where
  `zero  : -----------------------------
            ∥rec A ∙ n ∙ n' ∙ `zero ∥↘ n

  `suc∙- :  ∥rec A ∙ n ∙ n' ∙ m ∥↘ l →
            ∥ n' ∙ m ∥↘ l' →
            ∥ l' ∙ l ∥↘ l'' →
           ----------------------------------
            ∥rec A ∙ n ∙ n' ∙ `suc∙ m ∥↘ l''

  `⇑     : --------------------------------------------------------
            ∥rec A ∙ n ∙ n' ∙ `⇑ B r ∥↘ `⇑ A (`rec A ∙ n ∙ n' ∙ r)

instance
  EvaluationSub : Evaluation Sub Env
  ⟦_⟧_↘_ ⦃ EvaluationSub ⦄ σ ρ ρ' = ∀ x → ⟦ σ x ⟧ ρ ↘ ρ' x

infix 25 Rnf_#_↘_
infix 25 Rne_#_↘_

data Rnf_#_↘_ : DomNf → ℕ → Nf → Set
data Rne_#_↘_ : DomNe → ℕ → Ne → Set

data Rnf_#_↘_ where
  `λ-   :  ∥ m ∙ `⇑ A (`# z) ∥↘ n →
           Rnf `⇓ B n # suc z ↘ U →
          ------------------------------
           Rnf `⇓ (A `→ B) m # z ↘ `λ U

  `zero : -----------------------------
           Rnf `⇓ `N `zero # z ↘ `zero

  `suc  :  Rnf `⇓ `N m # z ↘ U →
          ----------------------------------
           Rnf `⇓ `N (`suc∙ m) # z ↘ `suc U

  `⇑`N  :  Rne r # z ↘ R →
          -------------------------------
           Rnf `⇓ `N (`⇑ A r) # z ↘ `⇑ R

data Rne_#_↘_ where
  `!-  : -------------------------------
          Rne `# x # z ↘ `! (z ∸ 1 ∸ x)

  _`$_ :  Rne r # z ↘ R →
          Rnf u # z ↘ U →
         -------------------------
          Rne r `$ u # z ↘ R `$ U

  `rec :  Rnf `⇓ A n # z ↘ U →
          Rnf `⇓ A n' # z ↘ U' →
          Rne r # z ↘ R →
         ---------------------------------------------
          Rne `rec A ∙ n ∙ n' ∙ r # z ↘ `rec A U U' R

Relation : Set → Set₁
Relation A = A → A → Set

_≣_∈_ : ∀ {A : Set} → A → A → Relation A → Set
x ≣ y ∈ f = f x y

PER⊥ : Relation DomNe
PER⊥ r r' = ∀ z → ∃[ R ] Rne r # z ↘ R × Rne r' # z ↘ R

PER⊤ : Relation DomNf
PER⊤ u u' = ∀ z → ∃[ U ] Rnf u # z ↘ U × Rnf u' # z ↘ U

data PER`N : Relation Dom where
  `zero  : -----------------------
            `zero ≣ `zero ∈ PER`N

  `suc∙_ :  m ≣ m' ∈ PER`N →
           ----------------------------
            `suc∙ m ≣ `suc∙ m' ∈ PER`N

  `⇑     :  r ≣ r' ∈ PER⊥ →
           ---------------------------
            `⇑ A r ≣ `⇑ A' r' ∈ PER`N

PER`→ : Relation Dom → Relation Dom → Relation Dom
PER`→ RI RO m m' =
  ∀ n n' →
   n ≣ n' ∈ RI →
   ∃[ l ] ∃[ l' ]
     ∥ m ∙ n ∥↘ l ×
     ∥ m' ∙ n' ∥↘ l' ×
     l ≣ l' ∈ RO

PER-Ty : Ty → Relation Dom
PER-Ty `N       = PER`N
PER-Ty (A `→ B) = PER`→ (PER-Ty A) (PER-Ty B)

PER⊥Var : ∀ x →
          --------------------
           `# x ≣ `# x ∈ PER⊥
PER⊥Var _ _ = _ , `!- , `!-

PER⊥⇒PER`N :  r ≣ r' ∈ PER⊥ →
             ----------------------------
              `⇑ `N r ≣ `⇑ `N r' ∈ PER`N
PER⊥⇒PER`N = `⇑

PER`N⇒PER⊤ :  m ≣ m' ∈ PER`N →
             ---------------------------
              `⇓ `N m ≣ `⇓ `N m' ∈ PER⊤
PER`N⇒PER⊤ `zero        z                   = _ , `zero , `zero
PER`N⇒PER⊤ (`suc∙ m≣m') z
  with _ , Rnfm , Rnfm' ← PER`N⇒PER⊤ m≣m' z = _ , `suc Rnfm , `suc Rnfm'
PER`N⇒PER⊤ (`⇑ r≣r')    z
  with _ , Rner , Rner' ← r≣r' z            = _ , `⇑`N Rner , `⇑`N Rner'

PER⊥⇒PER-Ty : ∀ A →
               r ≣ r' ∈ PER⊥ →
              -----------------------------
               `⇑ A r ≣ `⇑ A r' ∈ PER-Ty A
PER-Ty⇒PER⊤ : ∀ A →
               m ≣ m' ∈ PER-Ty A →
              -------------------------
               `⇓ A m ≣ `⇓ A m' ∈ PER⊤

PER⊥⇒PER-Ty `N                      = PER⊥⇒PER`N
PER⊥⇒PER-Ty (A `→ B) r≡r' n n' n≣n' = _ , _ , `⇑ , `⇑ , PER⊥⇒PER-Ty B helper
  where
    helper : _ ≣ _ ∈ PER⊥
    helper z
      with _ , Rner , Rner' ← r≡r' z
         | _ , Rnfn , Rnfn' ← PER-Ty⇒PER⊤ A n≣n' z = _ , Rner `$ Rnfn , Rner' `$ Rnfn'

PER-Ty⇒PER⊤ `N                                         = PER`N⇒PER⊤
PER-Ty⇒PER⊤ (A `→ B) m≡m' z
  with _ , _ , m∙z↘l , m'∙z↘l' , l≣l' ← m≡m' _ _ (PER⊥⇒PER-Ty A (PER⊥Var z))
    with _ , Rnfl , Rnfl' ← PER-Ty⇒PER⊤ B l≣l' (suc z) = _ , `λ- m∙z↘l Rnfl , `λ- m'∙z↘l' Rnfl'

PER`· : Relation Env
PER`· ρ ρ' = ⊤

PER`, : Relation Env → Relation Dom → Relation Env
PER`, RT RH ρ ρ' = dropE ρ ≣ dropE ρ' ∈ RT × ρ 0 ≣ ρ' 0 ∈ RH

PER-Ctx : Ctx → Relation Env
PER-Ctx `·       = PER`·
PER-Ctx (Γ `, A) = PER`, (PER-Ctx Γ) (PER-Ty A)

_⊨_≋_`:_ : Ctx → Tm → Tm → Ty → Set
Γ ⊨ M ≋ M' `: A =
  ∀ ρ ρ' →
   ρ ≣ ρ' ∈ PER-Ctx Γ →
   ∃[ m ] ∃[ m' ]
     ⟦ M ⟧ ρ ↘ m ×
     ⟦ M' ⟧ ρ' ↘ m' ×
     m ≣ m' ∈ PER-Ty A

_⊨s_≋_`:_ : Ctx → Sub → Sub → Ctx → Set
Γ ⊨s σ ≋ σ' `: Δ =
  ∀ ρ ρ' →
   ρ ≣ ρ' ∈ PER-Ctx Γ →
   ∃[ ω ] ∃[ ω' ]
     ⟦ σ ⟧ ρ ↘ ω ×
     ⟦ σ' ⟧ ρ' ↘ ω' ×
     ω ≣ ω' ∈ PER-Ctx Δ

⊨[_]_ :  Γ ⊨s σ ≋ σ' `: Δ →
         Δ ⊨ M ≋ M' `: A →
        ------------------------------
         Γ ⊨ [ σ ] M ≋ [ σ' ] M' `: A
(⊨[ σ≋σ' ] M≋M') ρ ρ' ρ≣ρ' = {!σ≋σ' _ _ ρ≣ρ'!}

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
