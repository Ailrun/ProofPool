{-# OPTIONS --overlapping-instances #-}
module NbE.STLC where

open import Data.Bool
open import Data.Nat hiding (less-than-or-equal)
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Function using (_$_)
open import Level using (Level)
open import Relation.Nullary.Negation
open import Relation.Nullary.Decidable as Dec
open import Relation.Binary.Bundles
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality hiding ([_])
import Relation.Binary.Reasoning.Setoid as Setoid-Reasoning
open import Relation.Binary.Structures

data Ty : Set where
  `N : Ty
  _`→_ : Ty → Ty → Ty

infixr 40 _`→_

_Ty≟_ : ∀ (A A' : Ty) → Dec (A ≡ A')
`N       Ty≟ `N         = yes refl
`N       Ty≟ (A' `→ B') = no λ ()
(A `→ B) Ty≟ `N         = no λ ()
(A `→ B) Ty≟ (A' `→ B') = Dec.map′ (λ{ (refl , refl) → refl }) (λ{ refl → refl , refl }) ((A Ty≟ A') Dec.×-dec (B Ty≟ B'))

data Ctx : Set where
  `· : Ctx
  _`,_ : Ctx → Ty → Ctx

infixl 30 _`,_

pattern `·, A = `· `, A

variable
  Γ Γ' Γ'' Γ₀ Γ₁ Γ₂ Γ₃ Δ Δ' Δ'' Δ₀ Δ₁ Δ₂ Δ₃ Ψ Ψ' Ψ'' Ψ₀ Ψ₁ Ψ₂ Ψ₃ : Ctx
  A A' A'' A₀ A₁ A₂ A₃ B B' B'' B₀ B₁ B₂ B₃ C C' C'' C₀ C₁ C₂ C₃ : Ty

_`,,_ : Ctx → Ctx → Ctx
Γ `,, `· = Γ
Γ `,, (Δ `, A) = (Γ `,, Δ) `, A

infixl 30 _`,,_

`,,-identityʳ : `· `,, Γ ≡ Γ
`,,-identityʳ {`·}     = refl
`,,-identityʳ {Γ `, A} = cong (_`, A) `,,-identityʳ

_Ctx≟_ : ∀ (Γ Γ' : Ctx) → Dec (Γ ≡ Γ')
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

Γ≢Γ,,Δ,A : ¬ Γ ≡ Γ `,, Γ' `, A
Γ≢Γ,,Δ,A {Γ = Γ `, B} {Γ' = Γ' `, C} eq
  with eq' , refl ← `,-injective eq
    rewrite `,,-associative Γ (`·, B) (Γ' `, C) = Γ≢Γ,,Δ,A eq'

data _Include_ : Ctx → Ty → Set

IncludeSyntax : Ctx → Ty → Set
IncludeSyntax = _Include_

syntax IncludeSyntax Γ A = A ∈ Γ

data _Include_ where
  here  : --------------
           A ∈ Γ `, A

  there :  A ∈ Γ →
          --------------
           A ∈ Γ `, B

data _⊢Tm:_ : Ctx → Ty → Set where
  `!_   :  A ∈ Γ →
          ----------
           Γ ⊢Tm: A

  `zero : -----------
           Γ ⊢Tm: `N

  `suc  : -----------------
           Γ ⊢Tm: `N `→ `N

  `rec  : ---------------------------------------
           Γ ⊢Tm: A `→ (`N `→ A `→ A) `→ `N `→ A

  `λ_   :  Γ `, A ⊢Tm: B →
          -----------------
           Γ ⊢Tm: A `→ B

  _`$_  :  Γ ⊢Tm: A `→ B →
           Γ ⊢Tm: A →
          -----------------
           Γ ⊢Tm: B

infixr 37 `!_
infixl 36 _`$_
infixr 35 `λ_

data _Ctx≤_ : Ctx → Ctx → Set where
  `id :  Γ Ctx≤ Γ
  `wk :  Γ Ctx≤ Δ →
        ---------------
         Γ `, A Ctx≤ Δ

data _⊢Wk:_ : Ctx → Ctx → Set where
  `·   :  Γ ⊢Wk: `·
  `wk  :  Γ ⊢Wk: Δ →
         ---------------
          Γ `, A ⊢Wk: Δ
  `ext :  Γ ⊢Wk: Δ →
         --------------------
          Γ `, A ⊢Wk: Δ `, A

data _⊢Sub:_ : Ctx → Ctx → Set where
  `·   :  Γ ⊢Sub: `·
  _`,_ :  Γ ⊢Sub: Δ →
          Γ ⊢Tm: A →
         ----------------
          Γ ⊢Sub: Δ `, A

record CtxEmpty (F : Ctx → Ctx → Set) : Set where
  field
    ^· : F Γ `·

record CtxExt (F : Ctx → Ctx → Set) : Set where
  field
    ^ext : F Γ Δ → F (Γ `, A) (Δ `, A)

record CtxId (F : Ctx → Ctx → Set) : Set where
  field
    ^id : F Γ Γ

open CtxEmpty ⦃...⦄
open CtxExt ⦃...⦄
open CtxId ⦃...⦄
instance
  CtxEmpty≤ : CtxEmpty _Ctx≤_
  ^· ⦃ CtxEmpty≤ ⦄ {`·}     = `id
  ^· ⦃ CtxEmpty≤ ⦄ {Γ `, x} = `wk ^·

  CtxId≤ : CtxId _Ctx≤_
  ^id ⦃ CtxId≤ ⦄ = `id

  CtxEmptyWk : CtxEmpty _⊢Wk:_
  ^· ⦃ CtxEmptyWk ⦄ = `·

  CtxExtWk : CtxExt _⊢Wk:_
  ^ext ⦃ CtxExtWk ⦄ = `ext

  CtxIdWk : CtxId _⊢Wk:_
  ^id ⦃ CtxIdWk ⦄ {Γ = `·}     = ^·
  ^id ⦃ CtxIdWk ⦄ {Γ = _ `, _} = ^ext ^id

  CtxEmptySub : CtxEmpty _⊢Sub:_
  ^· ⦃ CtxEmptySub ⦄ = `·

idWk : Γ ⊢Wk: Γ
idWk = ^id

Γ≰Γ,,Δ,A : Δ ≡ Γ `,, Γ' `, A → ¬ Γ Ctx≤ Δ
Γ≰Γ,,Δ,A                                eq `id      = Γ≢Γ,,Δ,A eq
Γ≰Γ,,Δ,A {Γ = Γ `, B} {Γ' = Γ'} {A = A} eq (`wk Γ≤)
  rewrite `,,-associative Γ (`·, B) (Γ' `, A)       = Γ≰Γ,,Δ,A eq Γ≤

Ctx≤-Irrelevant : Irrelevant _Ctx≤_
Ctx≤-Irrelevant `id       `id        = refl
Ctx≤-Irrelevant `id       (`wk Γ≤Δ') with () ← Γ≰Γ,,Δ,A refl Γ≤Δ'
Ctx≤-Irrelevant (`wk Γ≤Δ) `id        with () ← Γ≰Γ,,Δ,A refl Γ≤Δ
Ctx≤-Irrelevant (`wk Γ≤Δ) (`wk Γ≤Δ') = cong `wk (Ctx≤-Irrelevant Γ≤Δ Γ≤Δ')

_Ctx≤?_ : ∀ Γ Δ → Dec (Γ Ctx≤ Δ)
`·       Ctx≤? `·       = yes `id
`·       Ctx≤? (_ `, _) = no λ ()
(Γ `, A) Ctx≤? Δ
  with Γ Ctx≤? Δ
...  | yes Γ≤Δ = yes (`wk Γ≤Δ)
...  | no ¬Γ≤Δ
    with (Γ `, A) Ctx≟ Δ
...    | yes refl = yes `id
...    | no  ¬Γ≡Δ = no λ{ `id → ¬Γ≡Δ refl ; (`wk Γ≤Δ) → ¬Γ≤Δ Γ≤Δ }

record AppCtx≤ (F : Ctx → Set) : Set where
  infixr 40 ctx≤[_]_
  field
    ctx≤[_]_ : Γ Ctx≤ Δ → F Δ → F Γ

  infixr 40 ctx≤1_
  ctx≤1_ : F Γ → F (Γ `, A)
  ctx≤1_ = ctx≤[ `wk `id ]_

record FromCtx≤ (F : Ctx → Ctx → Set) : Set where
  field
    fromCtx≤ : Γ Ctx≤ Δ → F Γ Δ

record AppWk (F : Ctx → Set) : Set where
  infixr 40 wk[_]_
  field
    wk[_]_ : Γ ⊢Wk: Δ → F Δ → F Γ

  infixr 40 wk1_
  wk1_ : F Γ → F (Γ `, A)
  wk1_ = wk[ `wk ^id ]_

record FromWk (F : Ctx → Ctx → Set) : Set where
  field
    fromWk : Γ ⊢Wk: Δ → F Γ Δ

open AppCtx≤ ⦃...⦄
open FromCtx≤ ⦃...⦄
open AppWk ⦃...⦄
open FromWk ⦃...⦄
instance
  AppWkWk : AppWk (_⊢Wk: Ψ)
  wk[_]_ ⦃ AppWkWk ⦄ `·       `·       = `·
  wk[_]_ ⦃ AppWkWk ⦄ (`wk δ)  γ        = `wk (wk[ δ ] γ)
  wk[_]_ ⦃ AppWkWk ⦄ (`ext δ) `·       = `·
  wk[_]_ ⦃ AppWkWk ⦄ (`ext δ) (`wk γ)  = `wk (wk[ δ ] γ)
  wk[_]_ ⦃ AppWkWk ⦄ (`ext δ) (`ext γ) = `ext (wk[ δ ] γ)

  AppWkVar : AppWk (_Include A)
  wk[_]_ ⦃ AppWkVar ⦄ (`wk δ)  x         = there (wk[ δ ] x)
  wk[_]_ ⦃ AppWkVar ⦄ (`ext δ) here      = here
  wk[_]_ ⦃ AppWkVar ⦄ (`ext δ) (there x) = there (wk[ δ ] x)

  AppWkTm : AppWk (_⊢Tm: A)
  wk[_]_ ⦃ AppWkTm ⦄ δ (`! x)   = `! wk[ δ ] x
  wk[_]_ ⦃ AppWkTm ⦄ δ `zero    = `zero
  wk[_]_ ⦃ AppWkTm ⦄ δ `suc     = `suc
  wk[_]_ ⦃ AppWkTm ⦄ δ `rec     = `rec
  wk[_]_ ⦃ AppWkTm ⦄ δ (`λ M)   = `λ wk[ ^ext δ ] M
  wk[_]_ ⦃ AppWkTm ⦄ δ (M `$ N) = wk[ δ ] M `$ wk[ δ ] N

  AppWkSub : AppWk (_⊢Sub: Ψ)
  wk[_]_ ⦃ AppWkSub ⦄ δ `·       = `·
  wk[_]_ ⦃ AppWkSub ⦄ δ (σ `, M) = wk[ δ ] σ `, wk[ δ ] M

  CtxExtSub : CtxExt _⊢Sub:_
  ^ext ⦃ CtxExtSub ⦄ σ = wk1 σ `, `! here

  CtxIdSub : CtxId _⊢Sub:_
  ^id ⦃ CtxIdSub ⦄ {Γ = `·}     = ^·
  ^id ⦃ CtxIdSub ⦄ {Γ = _ `, _} = ^ext ^id

  FromWkSub : FromWk _⊢Sub:_
  fromWk ⦃ FromWkSub ⦄ `·       = `·
  fromWk ⦃ FromWkSub ⦄ (`wk δ)  = wk1 (fromWk δ)
  fromWk ⦃ FromWkSub ⦄ (`ext δ) = ^ext (fromWk δ)

  FromCtx≤Wk : FromCtx≤ _⊢Wk:_
  fromCtx≤ ⦃ FromCtx≤Wk ⦄ `id       = ^id
  fromCtx≤ ⦃ FromCtx≤Wk ⦄ (`wk Γ≤Δ) = `wk (fromCtx≤ Γ≤Δ)

  FromCtx≤Sub : FromCtx≤ _⊢Sub:_
  fromCtx≤ ⦃ FromCtx≤Sub ⦄ Γ≤Δ = fromWk (fromCtx≤ Γ≤Δ)

  AppCtx≤Ctx≤ : AppCtx≤ (_Ctx≤ Ψ)
  ctx≤[_]_ ⦃ AppCtx≤Ctx≤ ⦄ `id       Δ≤Ψ = Δ≤Ψ
  ctx≤[_]_ ⦃ AppCtx≤Ctx≤ ⦄ (`wk Γ≤Δ) Δ≤Ψ = `wk (ctx≤[ Γ≤Δ ] Δ≤Ψ)

  AppCtx≤Gen : ∀ {F : Ctx → Set} → ⦃ AppWk F ⦄ → AppCtx≤ F
  ctx≤[_]_ ⦃ AppCtx≤Gen ⦄ Γ≤Δ = wk[ fromCtx≤ Γ≤Δ ]_

idSub : Γ ⊢Sub: Γ
idSub = ^id

record AppSub (F : Ctx → Set) : Set₁ where
  infixr 40 [_]_
  field
    AppSubOutput : Ctx → Set
    AppSubOutputMap : F Γ → AppSubOutput Γ
    [_]_ : Γ ⊢Sub: Δ → F Δ → AppSubOutput Γ

  infixr 40 [_1]_
  [_1]_ : Γ ⊢Tm: A → F (Γ `, A) → AppSubOutput Γ
  [_1]_ L = [ ^id `, L ]_

open AppSub ⦃...⦄
instance
  AppSubWk : AppSub (_⊢Wk: Ψ)
  AppSubOutput ⦃ AppSubWk {Ψ} ⦄ = _⊢Sub: Ψ
  AppSubOutputMap ⦃ AppSubWk ⦄ = fromWk
  [_]_ ⦃ AppSubWk ⦄ σ        `·       = `·
  [_]_ ⦃ AppSubWk ⦄ (σ `, M) (`wk δ)  = [ σ ] δ
  [_]_ ⦃ AppSubWk ⦄ (σ `, M) (`ext δ) = [ σ ] δ `, M

  AppSubVar : AppSub (_Include A)
  AppSubOutput ⦃ AppSubVar {A} ⦄ = _⊢Tm: A
  AppSubOutputMap ⦃ AppSubVar ⦄ = `!_
  [_]_ ⦃ AppSubVar ⦄ (σ `, M) here      = M
  [_]_ ⦃ AppSubVar ⦄ (σ `, M) (there x) = [ σ ] x

  AppSubTm : AppSub (_⊢Tm: A) 
  AppSubOutput ⦃ AppSubTm {A} ⦄ = _⊢Tm: A
  AppSubOutputMap ⦃ AppSubTm ⦄ M = M
  [_]_ ⦃ AppSubTm ⦄ σ (`! x)   = [ σ ] x
  [_]_ ⦃ AppSubTm ⦄ σ `zero    = `zero
  [_]_ ⦃ AppSubTm ⦄ σ `suc     = `suc
  [_]_ ⦃ AppSubTm ⦄ σ `rec     = `rec
  [_]_ ⦃ AppSubTm ⦄ σ (`λ M)   = `λ [ ^ext σ ] M
  [_]_ ⦃ AppSubTm ⦄ σ (M `$ N) = [ σ ] M `$ [ σ ] N

  AppSubSub : AppSub (_⊢Sub: Ψ)
  AppSubOutput ⦃ AppSubSub {Ψ} ⦄ = _⊢Sub: Ψ
  AppSubOutputMap ⦃ AppSubSub ⦄ σ = σ
  [_]_ ⦃ AppSubSub ⦄ σ `·       = `·
  [_]_ ⦃ AppSubSub ⦄ σ (τ `, M) = [ σ ] τ `, [ σ ] M

wk[]-idWk⇒id : ∀ (δ : Γ ⊢Wk: Δ) →
               -------------------
                wk[ δ ] ^id ≡ δ
wk[]-idWk⇒id `·       = refl
wk[]-idWk⇒id (`wk δ)  = cong `wk (wk[]-idWk⇒id δ)
wk[]-idWk⇒id (`ext δ) = cong `ext (wk[]-idWk⇒id δ)

[]-idWk⇒id : ∀ (σ : Γ ⊢Sub: Δ) →
             -------------------
              [ σ ] idWk ≡ σ
[]-idWk⇒id `·       = refl
[]-idWk⇒id (σ `, M) = cong (_`, _) ([]-idWk⇒id σ)

record AppIdWk⇒Id F ⦃ AppWkF : AppWk F ⦄ : Set where
  field
    wk[idWk]⇒id : ∀ (x : F Γ) →
                  -----------------
                   wk[ ^id ] x ≡ x

record AppWkCompose F ⦃ AppWkF : AppWk F ⦄ : Set where
  field
    wk[]-compose : ∀ (δ : Γ ⊢Wk: Δ) (ε : Δ ⊢Wk: Ψ) (x : F Ψ) →
                   --------------------------------------------
                    wk[ δ ] wk[ ε ] x ≡ wk[ wk[ δ ] ε ] x

record AppSubWkCompose F ⦃ AppWkF : AppWk F ⦄ ⦃ AppSubF : AppSub F ⦄ ⦃ AppWkFOutput : AppWk (AppSubOutput ⦃ AppSubF ⦄) ⦄ : Set where
  field
    wk[]-[]-compose : ∀ (δ : Γ ⊢Wk: Δ) (σ : Δ ⊢Sub: Ψ) (x : F Ψ) →
                      ---------------------------------------------
                       wk[ δ ] [ σ ] x ≡ [ wk[ δ ] σ ] x

record AppWkSubCompose F ⦃ AppWkF : AppWk F ⦄ ⦃ AppSubF : AppSub F ⦄ : Set where
  field
    []-wk[]-compose : ∀ (σ : Γ ⊢Sub: Δ) (δ : Δ ⊢Wk: Ψ) (x : F Ψ) →
                      ---------------------------------------------
                       [ σ ] wk[ δ ] x ≡ [ [ σ ] δ ] x

record AppSubCompose F ⦃ AppSubF : AppSub F ⦄  ⦃ AppSubFOutput : AppSub (AppSubOutput ⦃ AppSubF ⦄) ⦄ : Set where
  field
    []-compose : ∀ (σ : Γ ⊢Sub: Δ) (τ : Δ ⊢Sub: Ψ) (x : F Ψ) →
                 -------------------------------------------------------------------------------------------------
                  [ σ ] [ τ ] x ≡ AppSubOutputMap ⦃ AppSubFOutput ⦄ ([_]_ ⦃ AppSubF ⦄ ([_]_ ⦃ AppSubSub ⦄ σ τ) x)

record CompatibleSubWk F ⦃ AppWkF : AppWk F ⦄ ⦃ AppSubF : AppSub F ⦄ : Set where
  field
    compatible-Sub-Wk : ∀ (δ : Γ ⊢Wk: Δ) (x : F Δ) →
                        ----------------------------------------------
                         [ fromWk δ ] x ≡ AppSubOutputMap (wk[ δ ] x)

open AppIdWk⇒Id ⦃...⦄
open AppWkCompose ⦃...⦄
open AppSubWkCompose ⦃...⦄
open AppWkSubCompose ⦃...⦄
open AppSubCompose ⦃...⦄
open CompatibleSubWk ⦃...⦄
instance
  AppIdWk⇒IdWk : AppIdWk⇒Id (_⊢Wk: Δ)
  wk[idWk]⇒id ⦃ AppIdWk⇒IdWk ⦄ {Γ = `·}      `·       = refl
  wk[idWk]⇒id ⦃ AppIdWk⇒IdWk ⦄ {Γ = Γ' `, A} `·       = refl
  wk[idWk]⇒id ⦃ AppIdWk⇒IdWk ⦄ {Γ = Γ' `, A} (`wk δ)  = cong `wk (wk[idWk]⇒id δ)
  wk[idWk]⇒id ⦃ AppIdWk⇒IdWk ⦄ {Γ = Γ' `, A} (`ext δ) = cong `ext (wk[idWk]⇒id δ)

  AppIdWk⇒IdVar : AppIdWk⇒Id (_Include A)
  wk[idWk]⇒id ⦃ AppIdWk⇒IdVar ⦄ here      = refl
  wk[idWk]⇒id ⦃ AppIdWk⇒IdVar ⦄ (there x) = cong there (wk[idWk]⇒id x)

  AppIdWk⇒IdTm : AppIdWk⇒Id (_⊢Tm: A)
  wk[idWk]⇒id ⦃ AppIdWk⇒IdTm ⦄ (`! x)   = cong `!_ (wk[idWk]⇒id x)
  wk[idWk]⇒id ⦃ AppIdWk⇒IdTm ⦄ `zero    = refl
  wk[idWk]⇒id ⦃ AppIdWk⇒IdTm ⦄ `suc     = refl
  wk[idWk]⇒id ⦃ AppIdWk⇒IdTm ⦄ `rec     = refl
  wk[idWk]⇒id ⦃ AppIdWk⇒IdTm ⦄ (`λ M)   = cong `λ_ (wk[idWk]⇒id M)
  wk[idWk]⇒id ⦃ AppIdWk⇒IdTm ⦄ (M `$ N) = cong₂ _`$_ (wk[idWk]⇒id M) (wk[idWk]⇒id N)

  AppIdWk⇒IdSub : AppIdWk⇒Id (_⊢Sub: Δ)
  wk[idWk]⇒id ⦃ AppIdWk⇒IdSub ⦄ `· = refl
  wk[idWk]⇒id ⦃ AppIdWk⇒IdSub ⦄ (σ `, M) = cong₂ _`,_ (wk[idWk]⇒id σ) (wk[idWk]⇒id M)

  AppWkComposeWk : AppWkCompose (_⊢Wk: Ψ')
  wk[]-compose ⦃ AppWkComposeWk ⦄ `·       `·       `·       = refl
  wk[]-compose ⦃ AppWkComposeWk ⦄ (`wk δ)  ε        φ        = cong `wk (wk[]-compose δ ε φ)
  wk[]-compose ⦃ AppWkComposeWk ⦄ (`ext δ) `·       `·       = refl
  wk[]-compose ⦃ AppWkComposeWk ⦄ (`ext δ) (`wk ε)  φ        = cong `wk (wk[]-compose δ ε φ)
  wk[]-compose ⦃ AppWkComposeWk ⦄ (`ext δ) (`ext ε) `·       = refl
  wk[]-compose ⦃ AppWkComposeWk ⦄ (`ext δ) (`ext ε) (`wk φ)  = cong `wk (wk[]-compose δ ε φ)
  wk[]-compose ⦃ AppWkComposeWk ⦄ (`ext δ) (`ext ε) (`ext φ) = cong `ext (wk[]-compose δ ε φ)

  AppWkComposeVar : AppWkCompose (_Include A)
  wk[]-compose ⦃ AppWkComposeVar ⦄ `·       `·       ()
  wk[]-compose ⦃ AppWkComposeVar ⦄ (`wk δ)  ε        x         = cong there (wk[]-compose δ ε x)
  wk[]-compose ⦃ AppWkComposeVar ⦄ (`ext δ) (`wk ε)  x         = cong there (wk[]-compose δ ε x)
  wk[]-compose ⦃ AppWkComposeVar ⦄ (`ext δ) (`ext ε) here      = refl
  wk[]-compose ⦃ AppWkComposeVar ⦄ (`ext δ) (`ext ε) (there x) = cong there (wk[]-compose δ ε x)

  AppWkComposeTm : AppWkCompose (_⊢Tm: A)
  wk[]-compose ⦃ AppWkComposeTm ⦄ δ ε (`! x)   = cong `!_ (wk[]-compose δ ε x)
  wk[]-compose ⦃ AppWkComposeTm ⦄ δ ε `zero    = refl
  wk[]-compose ⦃ AppWkComposeTm ⦄ δ ε `suc     = refl
  wk[]-compose ⦃ AppWkComposeTm ⦄ δ ε `rec     = refl
  wk[]-compose ⦃ AppWkComposeTm ⦄ δ ε (`λ M)   = cong `λ_ (wk[]-compose (^ext δ) (^ext ε) M)
  wk[]-compose ⦃ AppWkComposeTm ⦄ δ ε (M `$ N) = cong₂ _`$_ (wk[]-compose δ ε M) (wk[]-compose δ ε N)

  AppWkComposeSub : AppWkCompose (_⊢Sub: Ψ')
  wk[]-compose ⦃ AppWkComposeSub ⦄ δ ε `·       = refl
  wk[]-compose ⦃ AppWkComposeSub ⦄ δ ε (σ `, M) = cong₂ _`,_ (wk[]-compose δ ε σ) (wk[]-compose δ ε M)

  AppSubWkComposeWk : AppSubWkCompose (_⊢Wk: Ψ')
  wk[]-[]-compose ⦃ AppSubWkComposeWk ⦄ δ σ        `·       = refl
  wk[]-[]-compose ⦃ AppSubWkComposeWk ⦄ δ (σ `, M) (`wk ε)  = wk[]-[]-compose δ σ ε
  wk[]-[]-compose ⦃ AppSubWkComposeWk ⦄ δ (σ `, M) (`ext ε) = cong (_`, _) (wk[]-[]-compose δ σ ε)

  AppSubWkComposeVar : AppSubWkCompose (_Include A)
  wk[]-[]-compose ⦃ AppSubWkComposeVar ⦄ δ (σ `, M) here      = refl
  wk[]-[]-compose ⦃ AppSubWkComposeVar ⦄ δ (σ `, M) (there x) = wk[]-[]-compose δ σ x

  AppSubWkComposeTm : AppSubWkCompose (_⊢Tm: A)
  wk[]-[]-compose ⦃ AppSubWkComposeTm ⦄ δ σ (`! x)   = wk[]-[]-compose δ σ x
  wk[]-[]-compose ⦃ AppSubWkComposeTm ⦄ δ σ `zero    = refl
  wk[]-[]-compose ⦃ AppSubWkComposeTm ⦄ δ σ `suc     = refl
  wk[]-[]-compose ⦃ AppSubWkComposeTm ⦄ δ σ `rec     = refl
  wk[]-[]-compose ⦃ AppSubWkComposeTm ⦄ δ σ (`λ M)   = cong `λ_
    (begin wk[ `ext δ ] [ ^ext σ ] M                     ≡⟨ wk[]-[]-compose (^ext δ) (^ext σ) M ⟩
           [ wk[ `ext δ ] wk1 σ `, `! here ] M           ≡⟨ cong ([_] M) (cong (_`, _) (wk[]-compose (`ext δ) (`wk ^id) σ)) ⟩
           [ wk[ wk[ `ext δ ] `wk ^id ] σ `, `! here ] M ≡⟨⟩
           [ wk[ wk[ `wk δ ] ^id ] σ `, `! here ] M      ≡⟨ cong ([_] M) (cong (_`, _) (cong (wk[_] σ) (wk[]-idWk⇒id (`wk δ)))) ⟩
           [ wk[ `wk δ ] σ `, `! here ] M                ≡˘⟨ cong ([_] M) (cong (_`, _) (cong (wk[_] σ) (wk[idWk]⇒id (`wk δ)))) ⟩
           [ wk[ wk[ ^id ] `wk δ ] σ `, `! here ] M      ≡˘⟨ cong ([_] M) (cong (_`, _) (wk[]-compose (`wk ^id) δ σ)) ⟩
           [ wk1 wk[ δ ] σ `, `! here ] M                ∎)
    where
      open ≡-Reasoning
  wk[]-[]-compose ⦃ AppSubWkComposeTm ⦄ δ σ (M `$ N) = cong₂ _`$_ (wk[]-[]-compose δ σ M) (wk[]-[]-compose δ σ N)

  AppSubWkComposeSub : AppSubWkCompose (_⊢Sub: Ψ')
  wk[]-[]-compose ⦃ AppSubWkComposeSub ⦄ δ σ `·       = refl
  wk[]-[]-compose ⦃ AppSubWkComposeSub ⦄ δ σ (τ `, M) = cong₂ _`,_ (wk[]-[]-compose δ σ τ) (wk[]-[]-compose δ σ M)

  AppWkSubComposeWk : AppWkSubCompose (_⊢Wk: Ψ')
  []-wk[]-compose ⦃ AppWkSubComposeWk ⦄ σ        `·       `·       = refl
  []-wk[]-compose ⦃ AppWkSubComposeWk ⦄ (σ `, M) (`wk δ)  ε        = []-wk[]-compose σ δ ε
  []-wk[]-compose ⦃ AppWkSubComposeWk ⦄ (σ `, M) (`ext δ) `·       = refl
  []-wk[]-compose ⦃ AppWkSubComposeWk ⦄ (σ `, M) (`ext δ) (`wk ε)  = []-wk[]-compose σ δ ε
  []-wk[]-compose ⦃ AppWkSubComposeWk ⦄ (σ `, M) (`ext δ) (`ext ε) = cong (_`, _) ([]-wk[]-compose σ δ ε)

  AppWkSubComposeVar : AppWkSubCompose (_Include A)
  []-wk[]-compose ⦃ AppWkSubComposeVar ⦄ (σ `, M) (`wk δ)  x         = []-wk[]-compose σ δ x
  []-wk[]-compose ⦃ AppWkSubComposeVar ⦄ (σ `, M) (`ext δ) here      = refl
  []-wk[]-compose ⦃ AppWkSubComposeVar ⦄ (σ `, M) (`ext δ) (there x) = []-wk[]-compose σ δ x

  AppWkSubComposeTm : AppWkSubCompose (_⊢Tm: A)
  []-wk[]-compose ⦃ AppWkSubComposeTm ⦄ σ δ (`! x) = []-wk[]-compose σ δ x
  []-wk[]-compose ⦃ AppWkSubComposeTm ⦄ σ δ `zero = refl
  []-wk[]-compose ⦃ AppWkSubComposeTm ⦄ σ δ `suc = refl
  []-wk[]-compose ⦃ AppWkSubComposeTm ⦄ σ δ `rec = refl
  []-wk[]-compose ⦃ AppWkSubComposeTm ⦄ σ δ (`λ M) = cong `λ_
    (begin [ ^ext σ ] wk[ ^ext δ ] M ≡⟨ []-wk[]-compose (^ext σ) (^ext δ) M ⟩
           [ [ wk1 σ ] δ `, `! here ] M ≡˘⟨ cong ([_] M) (cong (_`, _) (wk[]-[]-compose (`wk ^id) σ δ)) ⟩
           [ ^ext ([ σ ] δ) ] M ∎)
    where
      open ≡-Reasoning
  []-wk[]-compose ⦃ AppWkSubComposeTm ⦄ σ δ (M `$ N) = cong₂ _`$_ ([]-wk[]-compose σ δ M) ([]-wk[]-compose σ δ N)

  AppWkSubComposeSub : AppWkSubCompose (_⊢Sub: Ψ')
  []-wk[]-compose ⦃ AppWkSubComposeSub ⦄ σ δ `· = refl
  []-wk[]-compose ⦃ AppWkSubComposeSub ⦄ σ δ (τ `, M) = cong₂ _`,_ ([]-wk[]-compose σ δ τ) ([]-wk[]-compose σ δ M)

  CompatibleSubWkVar : CompatibleSubWk (_Include A)
  compatible-Sub-Wk ⦃ CompatibleSubWkVar ⦄ (`wk δ) x          =
    begin [ wk1 (fromWk δ) ] x           ≡˘⟨ wk[]-[]-compose (`wk ^id) (fromWk δ) x ⟩
          wk[ `wk ^id ] [ fromWk δ ] x   ≡⟨ cong wk1_ (compatible-Sub-Wk δ x) ⟩
          `! there (wk[ ^id ] wk[ δ ] x) ≡⟨ cong `!_ (cong there (wk[idWk]⇒id (wk[ δ ] x))) ⟩
          `! there (wk[ δ ] x)           ∎
    where
      open ≡-Reasoning
  compatible-Sub-Wk ⦃ CompatibleSubWkVar ⦄ (`ext δ) here      = refl
  compatible-Sub-Wk ⦃ CompatibleSubWkVar ⦄ (`ext δ) (there x) =
    begin [ wk1 (fromWk δ) ] x           ≡˘⟨ wk[]-[]-compose (`wk ^id) (fromWk δ) x ⟩
          wk[ `wk ^id ] [ fromWk δ ] x   ≡⟨ cong wk1_ (compatible-Sub-Wk δ x) ⟩
          `! there (wk[ ^id ] wk[ δ ] x) ≡⟨ cong `!_ (cong there (wk[idWk]⇒id (wk[ δ ] x))) ⟩
          `! there (wk[ δ ] x)           ∎
    where
      open ≡-Reasoning

  CompatibleSubWkTm : CompatibleSubWk (_⊢Tm: A)
  compatible-Sub-Wk ⦃ CompatibleSubWkTm ⦄ δ (`! x)   = compatible-Sub-Wk δ x
  compatible-Sub-Wk ⦃ CompatibleSubWkTm ⦄ δ `zero    = refl
  compatible-Sub-Wk ⦃ CompatibleSubWkTm ⦄ δ `suc     = refl
  compatible-Sub-Wk ⦃ CompatibleSubWkTm ⦄ δ `rec     = refl
  compatible-Sub-Wk ⦃ CompatibleSubWkTm ⦄ δ (`λ M)   = cong `λ_ (compatible-Sub-Wk (`ext δ) M)
  compatible-Sub-Wk ⦃ CompatibleSubWkTm ⦄ δ (M `$ N) = cong₂ _`$_ (compatible-Sub-Wk δ M) (compatible-Sub-Wk δ N)

  CompatibleSubWkSub : CompatibleSubWk (_⊢Sub: Ψ)
  compatible-Sub-Wk ⦃ CompatibleSubWkSub ⦄ δ `· = refl
  compatible-Sub-Wk ⦃ CompatibleSubWkSub ⦄ δ (σ `, M) = cong₂ _`,_ (compatible-Sub-Wk δ σ) (compatible-Sub-Wk δ M)

  AppSubComposeVar : AppSubCompose (_Include A)
  []-compose ⦃ AppSubComposeVar ⦄ σ (τ `, M) here      = refl
  []-compose ⦃ AppSubComposeVar ⦄ σ (τ `, M) (there x) = []-compose σ τ x

  AppSubComposeTm : AppSubCompose (_⊢Tm: A)
  []-compose ⦃ AppSubComposeTm ⦄ σ τ (`! x) = []-compose σ τ x
  []-compose ⦃ AppSubComposeTm ⦄ σ τ `zero = refl
  []-compose ⦃ AppSubComposeTm ⦄ σ τ `suc = refl
  []-compose ⦃ AppSubComposeTm ⦄ σ τ `rec = refl
  []-compose ⦃ AppSubComposeTm ⦄ σ τ (`λ M) = cong `λ_
    (begin [ ^ext σ ] [ ^ext τ ] M               ≡⟨ []-compose (^ext σ) (^ext τ) M ⟩
           [ [ ^ext σ ] wk1 τ `, `! here ] M     ≡⟨ cong ([_] M) (cong (_`, _) ([]-wk[]-compose (^ext σ) (`wk ^id) τ)) ⟩
           [ [ [ wk1 σ ] idWk ] τ `, `! here ] M ≡⟨ cong ([_] M) (cong (_`, _) (cong ([_] τ) ([]-idWk⇒id (wk1 σ)))) ⟩
           [ [ wk1 σ ] τ `, `! here ] M          ≡˘⟨ cong ([_] M) (cong (_`, _) (wk[]-[]-compose (`wk ^id) σ τ)) ⟩
           [ ^ext ([ σ ] τ) ] M                  ∎)
    where
      open ≡-Reasoning
  []-compose ⦃ AppSubComposeTm ⦄ σ τ (M `$ N) = cong₂ _`$_ ([]-compose σ τ M) ([]-compose σ τ N)

idSub≡fromWk-idWk : ∀ {Γ} →
                    idSub {Γ = Γ} ≡ fromWk idWk
idSub≡fromWk-idWk {`·}     = refl
idSub≡fromWk-idWk {Γ `, A} = cong (_`, `! here) (cong wk1_ idSub≡fromWk-idWk)

[idSub]⇒id : ∀ {F}
               ⦃ AppWkF : AppWk F ⦄
               ⦃ AppSubF : AppSub F ⦄
               ⦃ AppIdWk⇒IdF : AppIdWk⇒Id F ⦄
               ⦃ CompatibleSubWkF : CompatibleSubWk F ⦄
               (x : F Γ) →
             -------------------------------
              [ ^id ] x ≡ AppSubOutputMap x
[idSub]⇒id x =
  begin [ ^id ] x                     ≡⟨ cong ([_] x) idSub≡fromWk-idWk ⟩
        [ fromWk ^id ] x              ≡⟨ compatible-Sub-Wk idWk x ⟩
        AppSubOutputMap (wk[ ^id ] x) ≡⟨ cong AppSubOutputMap (wk[idWk]⇒id x) ⟩
        AppSubOutputMap x             ∎
  where
    open ≡-Reasoning

[]-idSub⇒id : ∀ (σ : Γ ⊢Sub: Δ) →
              --------------------
               [ σ ] idSub ≡ σ
[]-idSub⇒id `·       = refl
[]-idSub⇒id (σ `, M) = cong (_`, _)
  (begin [ σ `, M ] wk1 idSub         ≡⟨ []-wk[]-compose (σ `, M) (`wk ^id) idSub ⟩
         [ [ σ `, M ] `wk ^id ] idSub ≡⟨ cong ([_] idSub) ([]-idWk⇒id σ) ⟩
         [ σ ] idSub                  ≡⟨ []-idSub⇒id σ ⟩
         σ ∎)
  where
    open ≡-Reasoning

ctx≤[]-fromCtx≤-commute : ∀ (Γ''≤Γ' : Γ'' Ctx≤ Γ') (Γ'≤Γ : Γ' Ctx≤ Γ) → fromCtx≤ (ctx≤[ Γ''≤Γ' ] Γ'≤Γ) ≡ ctx≤[ Γ''≤Γ' ] (fromCtx≤ Γ'≤Γ)
ctx≤[]-fromCtx≤-commute `id          Γ'≤Γ = sym (wk[idWk]⇒id (fromCtx≤ Γ'≤Γ))
ctx≤[]-fromCtx≤-commute (`wk Γ''≤Γ') Γ'≤Γ = cong `wk (ctx≤[]-fromCtx≤-commute Γ''≤Γ' Γ'≤Γ)

data Equiv : (Γ : Ctx) → (A : Ty) → Γ ⊢Tm: A → Γ ⊢Tm: A → Set

syntax Equiv Γ A M M' = Γ ⊢ M ≋ M' `: A

data Equiv where
  `β-`→    : ∀ {M : Γ `, A ⊢Tm: B}
               {N : Γ ⊢Tm: A} →
             -----------------------------------
              Γ ⊢ (`λ M) `$ N ≋ [ N 1] M `: B

  `β-`N₀   : ∀ {M N} →
             --------------------------------------
              Γ ⊢ `rec `$ M `$ N `$ `zero ≋ M `: A

  `β-`N₁   : ∀ {M N L} →
             --------------------------------------------------------------------------
              Γ ⊢ `rec `$ M `$ N `$ (`suc `$ L) ≋ N `$ L `$ (`rec `$ M `$ N `$ L) `: A

  `η-`→    : ∀ {M} →
             ---------------------------------------------------
              Γ ⊢ `λ wk1 M `$ `! here ≋ M `: A `→ B

  `ξ-`!    : ∀ {x} →
             -------------------------
              Γ ⊢ `! x ≋ `! x `: A

  `ξ-`zero : -------------------------
              Γ ⊢ `zero ≋ `zero `: `N

  `ξ-`suc  : -----------------------------
              Γ ⊢ `suc ≋ `suc `: `N `→ `N

  `ξ-`rec  : ---------------------------------------------------
              Γ ⊢ `rec ≋ `rec `: A `→ (`N `→ A `→ A) `→ `N `→ A

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

Equiv-refl : ∀ {M} → Γ ⊢ M ≋ M `: A
Equiv-refl {M = `! x}   = `ξ-`!
Equiv-refl {M = `zero}  = `ξ-`zero
Equiv-refl {M = `suc}   = `ξ-`suc
Equiv-refl {M = `rec}   = `ξ-`rec
Equiv-refl {M = `λ M}   = `ξ-`λ Equiv-refl
Equiv-refl {M = M `$ N} = `ξ- Equiv-refl `$ Equiv-refl

Equiv-IsEquivalence : IsEquivalence (Equiv Γ A)
Equiv-IsEquivalence = record
                      { refl = Equiv-refl
                      ; sym = `sym
                      ; trans = `trans
                      }

Equiv-Setoid : Ctx → Ty → Setoid _ _
Equiv-Setoid Γ A = record
                   { Carrier = Γ ⊢Tm: A
                   ; _≈_ = Equiv Γ A
                   ; isEquivalence = Equiv-IsEquivalence
                   }

module Equiv-Reasoning Γ A = Setoid-Reasoning (Equiv-Setoid Γ A)

Equiv-Sub : ∀ {M M' σ} →
             Γ ⊢ M ≋ M' `: A →
            -----------------------------
             Δ ⊢ [ σ ] M ≋ [ σ ] M' `: A
Equiv-Sub {M = (`λ M) `$ N} {M' = _}  {σ} `β-`→                =
  begin (`λ [ ^ext σ ] M) `$ [ σ ] N              ≈⟨ `β-`→ ⟩
        [ ^id `, [ σ ] N ] [ ^ext σ ] M           ≡⟨ []-compose (^id `, [ σ ] N) (^ext σ) M ⟩
        [ [ ^id `, [ σ ] N ] wk1 σ `, [ σ ] N ] M ≡⟨ cong ([_] M) (cong (_`, [ σ ] N) ([]-wk[]-compose (^id `, [ σ ] N) (`wk ^id) σ)) ⟩
        [ [ [ idSub ] idWk ] σ `, [ σ ] N ] M     ≡⟨ cong ([_] M) (cong (_`, [ σ ] N) (cong ([_] σ) ([]-idWk⇒id idSub))) ⟩
        [ [ idSub ] σ `, [ σ ] N ] M              ≡⟨ cong ([_] M) (cong (_`, [ σ ] N) ([idSub]⇒id σ)) ⟩
        [ σ `, [ σ ] N ] M                        ≡˘⟨ cong ([_] M) (cong (_`, [ σ ] N) ([]-idSub⇒id σ)) ⟩
        [ [ σ ] idSub `, [ σ ] N ] M              ≡˘⟨ []-compose σ (^id `, N) M ⟩
        [ σ ] [ ^id `, N ] M                      ∎
  where
    open Equiv-Reasoning _ _
Equiv-Sub                                 `β-`N₀               = `β-`N₀
Equiv-Sub                                 `β-`N₁               = `β-`N₁
Equiv-Sub                   {M' = M'} {σ} `η-`→                =
  begin `λ [ ^ext σ ] wk1 M' `$ `! here     ≡⟨ cong `λ_ (cong (_`$ _) ([]-wk[]-compose (^ext σ) (`wk ^id) M')) ⟩
        `λ [ [ wk1 σ ] idWk ] M' `$ `! here ≡⟨ cong `λ_ (cong (_`$ _) (cong ([_] M') ([]-idWk⇒id (wk1 σ)))) ⟩
        `λ [ wk1 σ ] M' `$ `! here          ≡˘⟨ cong `λ_ (cong (_`$ _) (wk[]-[]-compose (`wk ^id) σ M')) ⟩
        `λ wk1 [ σ ] M' `$ `! here          ≈⟨ `η-`→ ⟩
        [ σ ] M'                            ∎
  where
    open Equiv-Reasoning _ _
Equiv-Sub                                 `ξ-`!                = Equiv-refl
Equiv-Sub                                 `ξ-`zero             = `ξ-`zero
Equiv-Sub                                 `ξ-`suc              = `ξ-`suc
Equiv-Sub                                 `ξ-`rec              = `ξ-`rec
Equiv-Sub                                 (`ξ-`λ M≋M')         = `ξ-`λ (Equiv-Sub M≋M')
Equiv-Sub                                 (`ξ- M≋M' `$ N≋N')   = `ξ- Equiv-Sub M≋M' `$ Equiv-Sub N≋N'
Equiv-Sub                                 (`sym M≋M')          = `sym (Equiv-Sub M≋M')
Equiv-Sub                                 (`trans M≋M' M'≋M'') = `trans (Equiv-Sub M≋M') (Equiv-Sub M'≋M'')

Equiv-Wk : ∀ {M M' δ} →
             Γ ⊢ M ≋ M' `: A →
            -----------------------------
             Δ ⊢ wk[ δ ] M ≋ wk[ δ ] M' `: A
Equiv-Wk {M = M} {M'} {δ}
  rewrite sym (compatible-Sub-Wk δ M)
        | sym (compatible-Sub-Wk δ M') = Equiv-Sub

Equiv-Ctx≤ : ∀ {M M' Γ≤Δ} →
              Γ ⊢ M ≋ M' `: A →
             -----------------------------------------
              Δ ⊢ ctx≤[ Γ≤Δ ] M ≋ ctx≤[ Γ≤Δ ] M' `: A
Equiv-Ctx≤ = Equiv-Wk

data Nf : Ctx → Ty → Set
data Ne : Ctx → Ty → Set

syntax Nf Γ A = Γ ⊢⇇: A
syntax Ne Γ A = Γ ⊢⇉: A

data Nf where
  `zero : ----------
           Γ ⊢⇇: `N

  `suc  :  Γ ⊢⇇: `N →
          ------------
           Γ ⊢⇇: `N

  `λ_   :  Γ `, A ⊢⇇: B →
          ----------------
           Γ ⊢⇇: A `→ B

  `⇑    :  Γ ⊢⇉: A →
          -----------
           Γ ⊢⇇: A

data Ne where
  `!_   :  A ∈ Γ →
          ---------
           Γ ⊢⇉: A

  `rec  :  Γ ⊢⇇: A →
           Γ ⊢⇇: `N `→ A `→ A →
           Γ ⊢⇉: `N →
          ----------------------
           Γ ⊢⇉: A

  _`$_  :  Γ ⊢⇉: A `→ B →
           Γ ⊢⇇: A →
          ----------------
           Γ ⊢⇉: B

record IntoTm (F : Ctx → Ty → Set) : Set where
  field
    embed : F Γ A → Γ ⊢Tm: A

open IntoTm ⦃...⦄
instance
  IntoTmNf : IntoTm Nf
  IntoTmNe : IntoTm Ne

  embed ⦃ IntoTmNf ⦄ `zero    = `zero
  embed ⦃ IntoTmNf ⦄ (`suc v) = `suc `$ embed v
  embed ⦃ IntoTmNf ⦄ (`λ v)   = `λ embed v
  embed ⦃ IntoTmNf ⦄ (`⇑ u)   = embed u

  embed ⦃ IntoTmNe ⦄ (`! x)       = `! x
  embed ⦃ IntoTmNe ⦄ (`rec z s u) = `rec `$ embed z `$ embed s `$ embed u
  embed ⦃ IntoTmNe ⦄ (u `$ v)     = embed u `$ embed v

Nf* : Ty → Set
Nf* A = ∀ Γ → Γ ⊢⇇: A

Ne* : Ty → Set
Ne* A = ∀ Γ → Γ ⊢⇉: A ⊎ ⊤

Ne*! : Ctx → ∀ A → Ne* A
Ne*! Γ A Γ'
  with Γ' Ctx≤? (Γ `, A)
...  | yes Γ'≤Γ,A = inj₁ (`! ctx≤[ Γ'≤Γ,A ] here)
...  | no  _      = inj₂ tt

Ne*rec : Nf* A → Nf* (`N `→ A `→ A) → Ne* `N → Ne* A
Ne*rec z* s* u* Γ = Data.Sum.map₁ (`rec (z* Γ) (s* Γ)) (u* Γ)

_Ne*$_ : Ne* (A `→ B) → Nf* A → Ne* B
(u* Ne*$ v*) Γ = Data.Sum.map₁ (_`$ v* Γ) (u* Γ)

data Nat : Set where
  `zero : Nat
  `suc  : Nat → Nat
  `⇑    : Ne* `N → Nat

↓Nat : Nat → Nf* `N
↓Nat `zero    Γ = `zero
↓Nat (`suc n) Γ = `suc (↓Nat n Γ)
↓Nat (`⇑ x*)  Γ
  with x* Γ
... | inj₁ n    = `⇑ n
... | inj₂ _    = `zero

record Interpret {ℓ : Level} (T : Set) : Set (Level.suc ℓ) where
  field
    InterpretUniv : Set ℓ
    ⟦_⟧ : T → InterpretUniv

record Reflect (T : Set) (Output : T → Set) : Set where
  field
    ↑[_] : ∀ (t : T) → Output t

record Reify (T : Set) (Output : T → Set) : Set where
  field
    ↓[_] : ∀ (t : T) → Output t

open Interpret ⦃...⦄
open Reflect ⦃...⦄
open Reify ⦃...⦄
instance
  InterpretTy : Interpret Ty
  InterpretUniv ⦃ InterpretTy ⦄ = Set
  ⟦_⟧ ⦃ InterpretTy ⦄ `N       = Nat
  ⟦_⟧ ⦃ InterpretTy ⦄ (A `→ B) = ⟦ A ⟧ → ⟦ B ⟧

  InterpretCtx : Interpret Ctx
  InterpretUniv ⦃ InterpretCtx ⦄ = Set
  ⟦_⟧ ⦃ InterpretCtx ⦄ `·       = ⊤
  ⟦_⟧ ⦃ InterpretCtx ⦄ (Γ `, A) = ⟦ Γ ⟧ × ⟦ A ⟧

  InterpretVar : Interpret (A ∈ Γ)
  InterpretUniv ⦃ InterpretVar {A} {Γ} ⦄ = ⟦ Γ ⟧ → ⟦ A ⟧
  ⟦_⟧ ⦃ InterpretVar ⦄ here      (ρ , a) = a
  ⟦_⟧ ⦃ InterpretVar ⦄ (there x) (ρ , a) = ⟦ x ⟧ ρ

  interleaved mutual
    ReflectTy : Reflect Ty (λ A → Ne* A → ⟦ A ⟧)
    ReifyTy : Reify Ty (λ A → ⟦ A ⟧ → Nf* A)

    ↑[_] ⦃ ReflectTy ⦄ `N       u*   = `⇑ u*
    ↑[_] ⦃ ReflectTy ⦄ (A `→ B) u* a = ↑[ B ] (u* Ne*$ ↓[ A ] a)

    ↓[_] ⦃ ReifyTy ⦄ `N       v = ↓Nat v
    ↓[_] ⦃ ReifyTy ⦄ (A `→ B) v Γ = `λ (↓[ B ] (v (↑[ A ] (Ne*! Γ A))) (Γ `, A))

  ReflectCtx : Reflect Ctx ⟦_⟧
  ↑[_] ⦃ ReflectCtx ⦄ `· = tt
  ↑[_] ⦃ ReflectCtx ⦄ (Γ `, A) = ↑[ Γ ] , (↑[ A ] (Ne*! Γ A))

⟦rec⟧ : ∀ A → ⟦ A `→ (`N `→ A `→ A) `→ `N `→ A ⟧
⟦rec⟧ A z s `zero    = z
⟦rec⟧ A z s (`suc n) = s n (⟦rec⟧ A z s n)
⟦rec⟧ A z s (`⇑ u*)   = ↑[ A ] (Ne*rec (↓[ A ] z) (↓[ `N `→ A `→ A ] s) u*)

instance
  InterpretTm : Interpret (Γ ⊢Tm: A)
  InterpretUniv ⦃ InterpretTm {Γ} {A} ⦄ = ⟦ Γ ⟧ → ⟦ A ⟧
  ⟦_⟧ ⦃ InterpretTm ⦄ (`! x)   ρ       = ⟦ x ⟧ ρ
  ⟦_⟧ ⦃ InterpretTm ⦄ `zero    ρ       = `zero
  ⟦_⟧ ⦃ InterpretTm ⦄ `suc     ρ n     = `suc n
  ⟦_⟧ ⦃ InterpretTm ⦄ `rec     ρ z s n = ⟦rec⟧ _ z s n
  ⟦_⟧ ⦃ InterpretTm ⦄ (`λ M)   ρ a     = ⟦ M ⟧ (ρ , a)
  ⟦_⟧ ⦃ InterpretTm ⦄ (M `$ N) ρ       = ⟦ M ⟧ ρ (⟦ N ⟧ ρ)

  InterpretWk : Interpret (Γ ⊢Wk: Δ)
  InterpretUniv ⦃ InterpretWk {Γ} {Δ} ⦄ = ⟦ Γ ⟧ → ⟦ Δ ⟧
  ⟦_⟧ ⦃ InterpretWk ⦄ `·       ρ       = tt
  ⟦_⟧ ⦃ InterpretWk ⦄ (`wk δ)  (ρ , a) = ⟦ δ ⟧ ρ
  ⟦_⟧ ⦃ InterpretWk ⦄ (`ext δ) (ρ , a) = ⟦ δ ⟧ ρ , a

  InterpretSub : Interpret (Γ ⊢Sub: Δ)
  InterpretUniv ⦃ InterpretSub {Γ} {Δ} ⦄ = ⟦ Γ ⟧ → ⟦ Δ ⟧
  ⟦_⟧ ⦃ InterpretSub ⦄ `·       ρ = tt
  ⟦_⟧ ⦃ InterpretSub ⦄ (σ `, M) ρ = ⟦ σ ⟧ ρ , ⟦ M ⟧ ρ

nbe : Γ ⊢Tm: A → Γ ⊢⇇: A
nbe M = ↓[ _ ] (⟦ M ⟧ ↑[ _ ]) _

open import Axiom.Extensionality.Propositional using (Extensionality)

postulate
  fun-ext : ∀ {a b} → Extensionality a b

⟦idWk⟧-id : ∀ (ρ : ⟦ Γ ⟧) →
            ----------------------------------------------
             ⟦ idWk ⟧ ρ ≡ ρ
⟦idWk⟧-id {`·}     tt      = refl
⟦idWk⟧-id {Γ `, A} (ρ , a) = cong (_, a) (⟦idWk⟧-id ρ)

meaning-preserving-Wk-Var : ∀ (δ : Γ ⊢Wk: Δ)
                              (x : A ∈ Δ)
                              (ρ : ⟦ Γ ⟧) →
                            ----------------------------------------------
                             ⟦ wk[ δ ] x ⟧ ρ ≡ ⟦ x ⟧ (⟦ δ ⟧ ρ)
meaning-preserving-Wk-Var (`wk δ)  x         (ρ , a) = meaning-preserving-Wk-Var δ x ρ
meaning-preserving-Wk-Var (`ext δ) here      ρ       = refl
meaning-preserving-Wk-Var (`ext δ) (there x) (ρ , a) = meaning-preserving-Wk-Var δ x ρ

meaning-preserving-Wk : ∀ (δ : Γ ⊢Wk: Δ)
                          (M : Δ ⊢Tm: A)
                          (ρ : ⟦ Γ ⟧) →
                        ----------------------------------------------
                         ⟦ wk[ δ ] M ⟧ ρ ≡ ⟦ M ⟧ (⟦ δ ⟧ ρ)
meaning-preserving-Wk δ (`! x)   ρ    = meaning-preserving-Wk-Var δ x ρ
meaning-preserving-Wk δ `zero    ρ    = refl
meaning-preserving-Wk δ `suc     ρ    = refl
meaning-preserving-Wk δ `rec     ρ    = refl
meaning-preserving-Wk δ (`λ M)   ρ    = fun-ext (λ a → meaning-preserving-Wk (`ext δ) M (ρ , a))
meaning-preserving-Wk δ (M `$ N) ρ
  rewrite meaning-preserving-Wk δ M ρ
        | meaning-preserving-Wk δ N ρ = refl

meaning-preserving-Wk-Sub : ∀ (δ : Γ ⊢Wk: Δ)
                              (σ : Δ ⊢Sub: Ψ)
                              (ρ : ⟦ Γ ⟧) →
                            -----------------------------------
                             ⟦ wk[ δ ] σ ⟧ ρ ≡ ⟦ σ ⟧ (⟦ δ ⟧ ρ)
meaning-preserving-Wk-Sub δ `·       ρ = refl
meaning-preserving-Wk-Sub δ (σ `, M) ρ = cong₂ _,_ (meaning-preserving-Wk-Sub δ σ ρ) (meaning-preserving-Wk δ M ρ)

⟦idSub⟧-id : ∀ (ρ : ⟦ Γ ⟧) →
             ----------------------------------------------
              ⟦ idSub ⟧ ρ ≡ ρ
⟦idSub⟧-id {`·}     tt      = refl
⟦idSub⟧-id {Γ `, A} (ρ , a) = cong (_, a)
  (begin ⟦ wk1 idSub ⟧ (ρ , a)  ≡⟨ meaning-preserving-Wk-Sub (`wk ^id) ^id (ρ , a) ⟩
         ⟦ idSub ⟧ (⟦ idWk ⟧ ρ) ≡⟨ cong ⟦ idSub ⟧ (⟦idWk⟧-id ρ) ⟩
         ⟦ idSub ⟧ ρ            ≡⟨ ⟦idSub⟧-id ρ ⟩
         ρ                      ∎)
  where
    open ≡-Reasoning

meaning-preserving-Sub-Var : ∀ (σ : Γ ⊢Sub: Δ)
                               (x : A ∈ Δ)
                               (ρ : ⟦ Γ ⟧) →
                             ----------------------------------------------
                              ⟦ [ σ ] x ⟧ ρ ≡ ⟦ x ⟧ (⟦ σ ⟧ ρ)
meaning-preserving-Sub-Var (σ `, M) here      ρ = refl
meaning-preserving-Sub-Var (σ `, M) (there x) ρ = meaning-preserving-Sub-Var σ x ρ

meaning-preserving-Sub : ∀ (σ : Γ ⊢Sub: Δ)
                          (M : Δ ⊢Tm: A)
                          (ρ : ⟦ Γ ⟧) →
                        ----------------------------------------
                         ⟦ [ σ ] M ⟧ ρ ≡ ⟦ M ⟧ (⟦ σ ⟧ ρ)
meaning-preserving-Sub σ (`! x)   ρ    = meaning-preserving-Sub-Var σ x ρ
meaning-preserving-Sub σ `zero    ρ    = refl
meaning-preserving-Sub σ `suc     ρ    = refl
meaning-preserving-Sub σ `rec     ρ    = refl
meaning-preserving-Sub σ (`λ M)   ρ    = fun-ext λ a →
  begin ⟦ [ ^ext σ ] M ⟧ (ρ , a)       ≡⟨ meaning-preserving-Sub (^ext σ) M (ρ , a) ⟩
        ⟦ M ⟧ (⟦ wk1 σ ⟧ (ρ , a) , a)  ≡⟨ cong ⟦ M ⟧ (cong (_, a) (meaning-preserving-Wk-Sub (`wk ^id) σ (ρ , a))) ⟩
        ⟦ M ⟧ (⟦ σ ⟧ (⟦ idWk ⟧ ρ) , a) ≡⟨ cong ⟦ M ⟧ (cong (_, a) (cong ⟦ σ ⟧ (⟦idWk⟧-id ρ))) ⟩
        ⟦ M ⟧ (⟦ σ ⟧ ρ , a)            ∎
  where
    open ≡-Reasoning
meaning-preserving-Sub σ (M `$ N) ρ
  rewrite meaning-preserving-Sub σ M ρ
        | meaning-preserving-Sub σ N ρ = refl

completeness-helper : ∀ {M M'} →
                       Γ ⊢ M ≋ M' `: A →
                      -------------------
                       ⟦ M ⟧ ≡ ⟦ M' ⟧
completeness-helper {M = (`λ M) `$ N} `β-`→ = fun-ext λ ρ →
  begin ⟦ M ⟧ (ρ , ⟦ N ⟧ ρ)    ≡˘⟨ cong ⟦ M ⟧ (cong (_, ⟦ N ⟧ ρ) (⟦idSub⟧-id ρ)) ⟩
        ⟦ M ⟧ (⟦ ^id `, N ⟧ ρ) ≡˘⟨ meaning-preserving-Sub (^id `, N) M ρ ⟩
        ⟦ [ ^id `, N ] M ⟧ ρ   ∎
  where
    open ≡-Reasoning
completeness-helper `β-`N₀                  = refl
completeness-helper `β-`N₁                  = refl
completeness-helper {M' = M'} `η-`→         = fun-ext λ ρ → fun-ext λ a → cong (_$ a)
  (begin ⟦ wk1 M' ⟧ (ρ , a)  ≡⟨ meaning-preserving-Wk (`wk ^id) M' (ρ , a) ⟩
         ⟦ M' ⟧ (⟦ idWk ⟧ ρ) ≡⟨ cong ⟦ M' ⟧ (⟦idWk⟧-id ρ) ⟩
         ⟦ M' ⟧ ρ            ∎)
  where
    open ≡-Reasoning
completeness-helper `ξ-`!                   = refl
completeness-helper `ξ-`zero                = refl
completeness-helper `ξ-`suc                 = refl
completeness-helper `ξ-`rec                 = refl
completeness-helper (`ξ-`λ M≋M')
  rewrite completeness-helper M≋M'          = refl
completeness-helper (`ξ- M≋M' `$ N≋N')
  rewrite completeness-helper M≋M'
        | completeness-helper N≋N'          = refl
completeness-helper (`sym M'≋M)             = sym (completeness-helper M'≋M)
completeness-helper (`trans M≋M' M'≋M'')    = trans (completeness-helper M≋M') (completeness-helper M'≋M'')

completeness : ∀ {M M'} →
                Γ ⊢ M ≋ M' `: A →
               -------------------
                nbe M ≡ nbe M'
completeness M≋M'
  rewrite completeness-helper M≋M' = refl

gluing-nat : ∀ Γ → Γ ⊢Tm: `N → Nat → Set

syntax gluing-nat Γ M a = Γ ⊢ M ®Nat a

gluing-nat Γ M `zero    = Γ ⊢ M ≋ `zero `: `N
gluing-nat Γ M (`suc n) = ∃[ M' ] Γ ⊢ M ≋ `suc `$ M' `: `N × Γ ⊢ M' ®Nat n
gluing-nat Γ M (`⇑ u*)  = ∀ {Γ'} (Γ'≤Γ : Γ' Ctx≤ Γ) → ∃[ u ] u* Γ' ≡ inj₁ u × Γ' ⊢ ctx≤[ Γ'≤Γ ] M ≋ embed u `: `N

gluing : ∀ Γ A → Γ ⊢Tm: A → ⟦ A ⟧ → Set

syntax gluing Γ A M a = Γ ⊢ M `: A ® a

gluing Γ `N       M n = Γ ⊢ M ®Nat n
gluing Γ (A `→ B) M f = ∀ {Γ'} (Γ'≤Γ : Γ' Ctx≤ Γ) → ∀ {N : Γ' ⊢Tm: A} {a} → Γ' ⊢ N `: A ® a → Γ' ⊢ ctx≤[ Γ'≤Γ ] M `$ N `: B ® f a

gluing-nat-respects-Equiv : ∀ {M M' a} →
                             Γ ⊢ M ®Nat a →
                             Γ ⊢ M ≋ M' `: `N →
                            --------------------
                             Γ ⊢ M' ®Nat a
gluing-nat-respects-Equiv {a = `zero}  equiv                M≋M'      = `trans (`sym M≋M') equiv
gluing-nat-respects-Equiv {a = `suc a} (M' , equiv , natM') M≋M'      = M' , `trans (`sym M≋M') equiv , natM'
gluing-nat-respects-Equiv {a = `⇑ x}   ⊥M                   M≋M' Γ'≤Γ
  with u , eq , equiv ← ⊥M Γ'≤Γ                                       = u , eq , `trans (`sym (Equiv-Ctx≤ {Γ≤Δ = Γ'≤Γ} M≋M')) equiv

gluing-respects-Equiv : ∀ {M M' a} →
                         Γ ⊢ M `: A ® a →
                         Γ ⊢ M ≋ M' `: A →
                        -------------------
                         Γ ⊢ M' `: A ® a
gluing-respects-Equiv {A = `N}                     = gluing-nat-respects-Equiv
gluing-respects-Equiv {A = A `→ B} gM M≋M' Γ'≤Γ gN = gluing-respects-Equiv (gM Γ'≤Γ gN) (`ξ- (Equiv-Wk M≋M') `$ Equiv-refl)

kripke-nat : ∀ {M n} (Γ'≤Γ : Γ' Ctx≤ Γ) →
              Γ ⊢ M ®Nat n →
             ----------------------------
              Γ' ⊢ ctx≤[ Γ'≤Γ ] M ®Nat n
kripke-nat         {n = `zero}  Γ'≤Γ equiv                             = Equiv-Ctx≤ {Γ≤Δ = Γ'≤Γ} equiv
kripke-nat         {n = `suc n} Γ'≤Γ (M' , equiv , natM')              = ctx≤[ Γ'≤Γ ] M' , Equiv-Ctx≤ {Γ≤Δ = Γ'≤Γ} equiv , kripke-nat Γ'≤Γ natM'
kripke-nat {M = M} {n = `⇑ x}   Γ'≤Γ ⊥M                   {Γ''} Γ''≤Γ'
  with u , eq , equiv ← ⊥M (ctx≤[ Γ''≤Γ' ] Γ'≤Γ)                       = u , eq ,
    (begin ctx≤[ Γ''≤Γ' ] ctx≤[ Γ'≤Γ ] M        ≡⟨ wk[]-compose (fromCtx≤ Γ''≤Γ') (fromCtx≤ Γ'≤Γ) _ ⟩
           wk[ ctx≤[ Γ''≤Γ' ] fromCtx≤ Γ'≤Γ ] M ≡˘⟨ cong (wk[_] _) (ctx≤[]-fromCtx≤-commute Γ''≤Γ' Γ'≤Γ) ⟩
           ctx≤[ ctx≤[ Γ''≤Γ' ] Γ'≤Γ ] M        ≈⟨ equiv ⟩
           embed u                              ∎)
  where
    open Equiv-Reasoning _ _

kripke : ∀ {M a} (Γ'≤Γ : Γ' Ctx≤ Γ) →
          Γ ⊢ M `: A ® a →
         -------------------------------
          Γ' ⊢ ctx≤[ Γ'≤Γ ] M `: A ® a
kripke {A = `N}                                     = kripke-nat
kripke {A = A `→ B} {M = M} Γ'≤Γ gM {Γ''} Γ''≤Γ' gN
  rewrite wk[]-compose (fromCtx≤ Γ''≤Γ') (fromCtx≤ Γ'≤Γ) M
        | sym (ctx≤[]-fromCtx≤-commute Γ''≤Γ' Γ'≤Γ) = gM (ctx≤[ Γ''≤Γ' ] Γ'≤Γ) gN

gluing-bot : ∀ Γ A → Γ ⊢Tm: A → Ne* A → Set
syntax gluing-bot Γ A M u* = Γ ⊢ M `: A ®⊥ u*
Γ ⊢ M `: A ®⊥ u* = ∀ {Γ'} (Γ'≤Γ : Γ' Ctx≤ Γ) → ∃[ u ] u* Γ' ≡ inj₁ u × Γ' ⊢ ctx≤[ Γ'≤Γ ] M ≋ embed u `: A

gluing-top : ∀ Γ A → Γ ⊢Tm: A → ⟦ A ⟧ → Set
syntax gluing-top Γ A M a = Γ ⊢ M `: A ®⊤ a
Γ ⊢ M `: A ®⊤ a = ∀ {Γ'} (Γ'≤Γ : Γ' Ctx≤ Γ) → Γ' ⊢ ctx≤[ Γ'≤Γ ] M ≋ embed (↓[ A ] a Γ') `: A

gluing-bot-app : ∀ {M u* N a} → Γ ⊢ M `: A `→ B ®⊥ u* → Γ ⊢ N `: A ®⊤ a → Γ ⊢ M `$ N `: B ®⊥ (u* Ne*$ ↓[ A ] a)
gluing-bot-app {a = a} ⊥A→B ⊤A {Γ'} Γ'≤Γ
  with u , eq , equivA→B ← ⊥A→B Γ'≤Γ
     | equivA ← ⊤A Γ'≤Γ
    rewrite eq                       = u `$ ↓[ _ ] a _ , refl , `ξ- equivA→B `$ equivA

kripke-bot : ∀ {M u} (Γ'≤Γ : Γ' Ctx≤ Γ) →
              Γ ⊢ M `: A ®⊥ u →
             -------------------------------
              Γ' ⊢ ctx≤[ Γ'≤Γ ] M `: A ®⊥ u
kripke-bot {M = M} Γ'≤Γ ⊥M {Γ''} Γ''≤Γ'
  with u , eq , equivA ← ⊥M (ctx≤[ Γ''≤Γ' ] Γ'≤Γ)
    rewrite wk[]-compose (fromCtx≤ Γ''≤Γ') (fromCtx≤ Γ'≤Γ) M
          | ctx≤[]-fromCtx≤-commute Γ''≤Γ' Γ'≤Γ = u , eq , equivA

var-bot : Γ `, A ⊢ `! here `: A ®⊥ Ne*! Γ A
var-bot {Γ = Γ} {A = A} {Γ' = Γ'} Γ'≤Γ,A
  with eq ← dec-yes-irr (Γ' Ctx≤? Γ `, A) Ctx≤-Irrelevant Γ'≤Γ,A
    rewrite eq = `! ctx≤[ Γ'≤Γ,A ] here , refl , Equiv-refl

var-nat : Γ `, `N ⊢ `! here ®Nat `⇑ (Ne*! Γ `N)
var-nat {Γ = Γ} {Γ' = Γ'} Γ'≤Γ,N
  with eq ← dec-yes-irr (Γ' Ctx≤? Γ `, `N) Ctx≤-Irrelevant Γ'≤Γ,N
    rewrite eq = `! ctx≤[ Γ'≤Γ,N ] here , refl , Equiv-refl

realizability-nat-top : ∀ {M n} → Γ ⊢ M ®Nat n → Γ ⊢ M `: `N ®⊤ n
realizability-nat-top {M = M} {n = `zero}  equiv                Γ'≤Γ = Equiv-Ctx≤ {Γ≤Δ = Γ'≤Γ} equiv
realizability-nat-top {M = M} {n = `suc n} (M' , equiv , natM') Γ'≤Γ = `trans (Equiv-Ctx≤ {Γ≤Δ = Γ'≤Γ} equiv) (`ξ- `ξ-`suc `$ realizability-nat-top natM' Γ'≤Γ)
realizability-nat-top {M = M} {n = `⇑ x}   ⊥M                   Γ'≤Γ
  with u , eq , equiv ← ⊥M Γ'≤Γ
    rewrite eq                                                       = equiv

realizability-bot : ∀ {M u} → Γ ⊢ M `: A ®⊥ u → Γ ⊢ M `: A ® ↑[ A ] u
realizability-top : ∀ {M a} → Γ ⊢ M `: A ® a → Γ ⊢ M `: A ®⊤ a

realizability-bot {A = `N}     ⊥N           = ⊥N
realizability-bot {A = A `→ B} ⊥A→B Γ'≤Γ gA = realizability-bot (gluing-bot-app (kripke-bot Γ'≤Γ ⊥A→B) (realizability-top gA))

realizability-top {A = `N}                             = realizability-nat-top
realizability-top {A = A `→ B} {M = M} {a = a} gA Γ'≤Γ =
  begin ctx≤[ Γ'≤Γ ] M                                     ≈˘⟨ `η-`→ ⟩
        `λ wk1 (ctx≤[ Γ'≤Γ ] M) `$ `! here                 ≈⟨ `ξ-`λ (`ξ- helper `$ Equiv-refl) ⟩
        `λ wk[ `ext ^id ] ctx≤[ `wk Γ'≤Γ ] M `$ `! here    ≈⟨ `ξ-`λ (realizability-top (gA (`wk Γ'≤Γ) (realizability-bot (var-bot {A = A}))) `id) ⟩
        `λ embed (↓[ B ] (a (↑[ A ] (Ne*! _ A))) (_ `, A)) ∎
  where
    helper : _
    helper =
      begin wk1 (ctx≤[ Γ'≤Γ ] M)                       ≡⟨ wk[]-compose _ _ M ⟩
            wk[ wk[ `wk ^id ] fromCtx≤ Γ'≤Γ ] M        ≡⟨⟩
            wk[ wk[ ^id ] fromCtx≤ (`wk Γ'≤Γ) ] M      ≡⟨⟩
            wk[ wk[ `ext ^id ] fromCtx≤ (`wk Γ'≤Γ) ] M ≡˘⟨ wk[]-compose (`ext ^id) (fromCtx≤ (`wk Γ'≤Γ)) M ⟩
            wk[ `ext ^id ] ctx≤[ `wk Γ'≤Γ ] M          ∎
      where
        open Equiv-Reasoning _ _

    open Equiv-Reasoning _ _

gluing-Sub : ∀ Γ Δ → Γ ⊢Sub: Δ → ⟦ Δ ⟧ → Set
syntax gluing-Sub Γ Δ σ ρ = Γ ⊢s σ `: Δ ® ρ
Γ ⊢s `·     `: `·     ® tt      = ⊤
Γ ⊢s σ `, M `: Δ `, A ® (ρ , a) = Γ ⊢s σ `: Δ ® ρ × Γ ⊢ M `: A ® a

kripke-Sub : ∀ {σ ρ} (Γ'≤Γ : Γ' Ctx≤ Γ) →
              Γ ⊢s σ `: Δ ® ρ →
             -------------------------------
              Γ' ⊢s ctx≤[ Γ'≤Γ ] σ `: Δ ® ρ
kripke-Sub {Γ = Γ} {Δ = `·}     {σ = `·}     {ρ = tt}    Γ'≤Γ tt        = tt
kripke-Sub {Γ = Γ} {Δ = Δ `, x} {σ = σ `, M} {ρ = ρ , a} Γ'≤Γ (gσ , ga) = kripke-Sub Γ'≤Γ gσ , kripke {M = M} Γ'≤Γ ga

SoundnessTyping : ∀ Γ A (M : Γ ⊢Tm: A) → Set
syntax SoundnessTyping Γ A M = Γ ⊨ M `: A
SoundnessTyping Γ A M = ∀ Δ σ ρ → Δ ⊢s σ `: Γ ® ρ → Δ ⊢ [ σ ] M `: A ® ⟦ M ⟧ ρ

soundness-fundamental-Var : ∀ x → Γ ⊨ `! x `: A
soundness-fundamental-Var {Γ = Γ `, B} here      Δ (σ `, M) (ρ , a) (gσ , ga) = ga
soundness-fundamental-Var {Γ = Γ `, B} (there x) Δ (σ `, M) (ρ , a) (gσ , ga) = soundness-fundamental-Var x Δ σ ρ gσ

soundness-fundamental-rec : SoundnessTyping Γ (A `→ (`N `→ A `→ A) `→ `N `→ A) `rec
soundness-fundamental-rec Δ σ ρ gσ Γ'≤Δ {Z} {z} gz {Γz} Γz≤Γ' {S} {s} gs {Γs} Γs≤Γz {N} {`zero}  natM                 = gluing-respects-Equiv (kripke {M = ctx≤[ Γz≤Γ' ] Z} Γs≤Γz (kripke {M = Z} Γz≤Γ' gz))
  (begin ctx≤[ Γs≤Γz ] ctx≤[ Γz≤Γ' ] Z                                            ≈˘⟨ `β-`N₀ ⟩
         `rec `$ ctx≤[ Γs≤Γz ] ctx≤[ Γz≤Γ' ] Z `$ ctx≤[ Γs≤Γz ] S `$ `zero        ≈˘⟨ (`ξ- Equiv-refl `$ Equiv-Wk {δ = idWk} natM) ⟩
         `rec `$ ctx≤[ Γs≤Γz ] ctx≤[ Γz≤Γ' ] Z `$ ctx≤[ Γs≤Γz ] S `$ wk[ idWk ] N ≡⟨ cong (_ `$_) (wk[idWk]⇒id N) ⟩
         `rec `$ ctx≤[ Γs≤Γz ] ctx≤[ Γz≤Γ' ] Z `$ ctx≤[ Γs≤Γz ] S `$ N            ∎)
  where
    open Equiv-Reasoning _ _
soundness-fundamental-rec Δ σ ρ gσ Γ'≤Δ {Z} {z} gz {Γz} Γz≤Γ' {S} {s} gs {Γs} Γs≤Γz {N} {`suc n} (N' , equiv , natM') = gluing-respects-Equiv (gs Γs≤Γz natM' `id (soundness-fundamental-rec Δ σ ρ gσ Γ'≤Δ gz Γz≤Γ' gs Γs≤Γz natM'))
  (begin wk[ ^id ] ctx≤[ Γs≤Γz ] S `$ wk[ ^id ] N' `$ subrecexp                   ≡⟨ cong (_`$ subrecexp) (cong (_ `$_) (wk[idWk]⇒id N')) ⟩
         wk[ ^id ] ctx≤[ Γs≤Γz ] S `$ N' `$ subrecexp                             ≡⟨ cong (_`$ subrecexp) (cong (_`$ _) (wk[idWk]⇒id (ctx≤[ Γs≤Γz ] S))) ⟩
         ctx≤[ Γs≤Γz ] S `$ N' `$ subrecexp                                       ≈˘⟨ `β-`N₁ ⟩
         `rec `$ ctx≤[ Γs≤Γz ] ctx≤[ Γz≤Γ' ] Z `$ ctx≤[ Γs≤Γz ] S `$ (`suc `$ N') ≈˘⟨ `ξ- Equiv-refl `$ equiv ⟩
         `rec `$ ctx≤[ Γs≤Γz ] ctx≤[ Γz≤Γ' ] Z `$ ctx≤[ Γs≤Γz ] S `$ N            ∎)
  where
    subrecexp = `rec `$ ctx≤[ Γs≤Γz ] ctx≤[ Γz≤Γ' ] Z `$ ctx≤[ Γs≤Γz ] S `$ N'
    open Equiv-Reasoning Γs _
soundness-fundamental-rec {A = A} Δ σ ρ gσ Γ'≤Δ {Z} {z} gz {Γz} Γz≤Γ' {S} {s} gs {Γs} Γs≤Γz {N} {`⇑ u*}  ⊥N = realizability-bot helper
  where
    recexp = `rec `$ ctx≤[ Γs≤Γz ] ctx≤[ Γz≤Γ' ] Z `$ ctx≤[ Γs≤Γz ] S `$ N

    helper : Γs ⊢ recexp `: _ ®⊥ Ne*rec (↓[ _ ] z) (↓[ _ ] s) u*
    helper {Γ' = Δ} Δ≤Γs
      with u , eq , equiv ← ⊥N Δ≤Γs
        rewrite eq  = `rec (↓[ _ ] z _) (↓[ _ ] s _) u , refl , `ξ- `ξ- `ξ- `ξ-`rec `$ equiv-z `$ equiv-s `$ equiv
      where
        equiv-z : _ ⊢ ctx≤[ Δ≤Γs ] ctx≤[ Γs≤Γz ] ctx≤[ Γz≤Γ' ] Z ≋ embed (↓[ _ ] z _) `: _
        equiv-z =
          begin ctx≤[ Δ≤Γs ] ctx≤[ Γs≤Γz ] ctx≤[ Γz≤Γ' ] Z ≡⟨ wk[]-compose (fromCtx≤ Δ≤Γs) (fromCtx≤ Γs≤Γz) (ctx≤[ Γz≤Γ' ] Z) ⟩
                wk[ ctx≤[ Δ≤Γs ] fromCtx≤ Γs≤Γz ] ctx≤[ Γz≤Γ' ] Z ≡˘⟨ cong (wk[_] _) (ctx≤[]-fromCtx≤-commute Δ≤Γs Γs≤Γz) ⟩
                ctx≤[ ctx≤[ Δ≤Γs ] Γs≤Γz ] ctx≤[ Γz≤Γ' ] Z ≡⟨ wk[]-compose (fromCtx≤ (ctx≤[ Δ≤Γs ] Γs≤Γz)) (fromCtx≤ Γz≤Γ') Z ⟩
                wk[ ctx≤[ ctx≤[ Δ≤Γs ] Γs≤Γz ] fromCtx≤ Γz≤Γ' ] Z ≡˘⟨ cong (wk[_] Z) (ctx≤[]-fromCtx≤-commute (ctx≤[ Δ≤Γs ] Γs≤Γz) Γz≤Γ') ⟩
                ctx≤[ ctx≤[ ctx≤[ Δ≤Γs ] Γs≤Γz ] Γz≤Γ' ] Z ≈⟨ realizability-top gz (ctx≤[ ctx≤[ Δ≤Γs ] Γs≤Γz ] Γz≤Γ') ⟩
                embed (↓[ _ ] z _) ∎
          where
            open Equiv-Reasoning _ _

        equiv-s-core : _ ⊢ wk[ `wk ^id ] ctx≤[ ctx≤[ ctx≤[ `wk `id ] Δ≤Γs ] Γs≤Γz ] S `$ `! there here `$ `! here ≋ embed (↓[ _ ] (s (`⇑ (Ne*! _ `N)) (↑[ _ ] (Ne*! _ _))) _) `: A
        equiv-s-core =
          begin wk[ `wk ^id ] ctx≤[ ctx≤[ ctx≤[ `wk `id ] Δ≤Γs ] Γs≤Γz ] S `$ `! there here `$ `! here ≡˘⟨ cong (_`$ `! here) (cong (_`$ _) (wk[idWk]⇒id (wk[ `wk ^id ] ctx≤[ ctx≤[ ctx≤[ `wk `id ] Δ≤Γs ] Γs≤Γz ] S))) ⟩
                wk[ ^id ] wk[ `wk ^id ] ctx≤[ ctx≤[ ctx≤[ `wk `id ] Δ≤Γs ] Γs≤Γz ] S `$ `! there here `$ `! here ≈⟨ realizability-top (gs (ctx≤[ ctx≤[ `wk ^id ] Δ≤Γs ] Γs≤Γz) {`! here} (λ {Δ'} Δ'≤Δ,N → var-nat Δ'≤Δ,N) (`wk ^id) (realizability-bot (var-bot {A = A}))) `id ⟩
                embed (↓[ _ ] (s (`⇑ (Ne*! _ `N)) (↑[ _ ] (Ne*! _ _))) _) ∎
          where
            open Equiv-Reasoning _ _

        equiv-s : _ ⊢ ctx≤[ Δ≤Γs ] ctx≤[ Γs≤Γz ] S ≋ embed (↓[ _ ] s _) `: _
        equiv-s =
          begin ctx≤[ Δ≤Γs ] ctx≤[ Γs≤Γz ] S                                                       ≡⟨ wk[]-compose (fromCtx≤ Δ≤Γs) (fromCtx≤ Γs≤Γz) S ⟩
                wk[ ctx≤[ Δ≤Γs ] fromCtx≤ Γs≤Γz ] S                                                ≡˘⟨ cong (wk[_] _) (ctx≤[]-fromCtx≤-commute Δ≤Γs Γs≤Γz) ⟩
                ctx≤[ ctx≤[ Δ≤Γs ] Γs≤Γz ] S                                                       ≈˘⟨ `η-`→ ⟩
                `λ (wk1 ctx≤[ ctx≤[ Δ≤Γs ] Γs≤Γz ] S) `$ `! here                                   ≈˘⟨ `ξ-`λ `η-`→ ⟩
                `λ `λ wk1 wk1 ctx≤[ ctx≤[ Δ≤Γs ] Γs≤Γz ] S `$ `! there here `$ `! here             ≡⟨ cong `λ_ (cong `λ_ (cong (_`$ `! here) (cong (_`$ `! there here) (cong (wk1_) map-fun)))) ⟩
                `λ `λ wk1 ctx≤[ ctx≤[ ctx≤[ `wk `id ] Δ≤Γs ] Γs≤Γz ] S `$ `! there here `$ `! here ≈⟨ `ξ-`λ (`ξ-`λ equiv-s-core) ⟩
                `λ `λ embed (↓[ _ ] (s (`⇑ (Ne*! _ `N)) (↑[ _ ] (Ne*! _ _))) _)                    ≡⟨⟩
                embed (↓[ _ ] s _)                                                                 ∎
          where
            map-fun : wk1 ctx≤[ ctx≤[ Δ≤Γs ] Γs≤Γz ] S ≡ ctx≤[ ctx≤[ ctx≤[ `wk `id ] Δ≤Γs ] Γs≤Γz ] S
            map-fun =
              begin wk1 ctx≤[ ctx≤[ Δ≤Γs ] Γs≤Γz ] S                    ≡⟨ wk[]-compose (`wk ^id) (fromCtx≤ (ctx≤[ Δ≤Γs ] Γs≤Γz)) S ⟩
                    wk[ wk1 fromCtx≤ (ctx≤[ Δ≤Γs ] Γs≤Γz) ] S           ≡⟨ cong (wk[_] S) (cong (wk1_) (ctx≤[]-fromCtx≤-commute Δ≤Γs Γs≤Γz)) ⟩
                    wk[ wk1 ctx≤[ Δ≤Γs ] fromCtx≤ Γs≤Γz ] S             ≡⟨ cong (wk[_] S) (wk[]-compose (`wk ^id) (fromCtx≤ Δ≤Γs) (fromCtx≤ Γs≤Γz)) ⟩
                    wk[ wk[ wk1 fromCtx≤ Δ≤Γs ] fromCtx≤ Γs≤Γz ] S      ≡˘⟨ cong (wk[_] S) (cong (wk[_] fromCtx≤ Γs≤Γz) (ctx≤[]-fromCtx≤-commute (`wk `id) Δ≤Γs)) ⟩
                    wk[ ctx≤[ ctx≤[ `wk `id ] Δ≤Γs ] fromCtx≤ Γs≤Γz ] S ≡˘⟨ cong (wk[_] S) (ctx≤[]-fromCtx≤-commute (ctx≤[ `wk `id ] Δ≤Γs) Γs≤Γz) ⟩
                    ctx≤[ ctx≤[ ctx≤[ `wk `id ] Δ≤Γs ] Γs≤Γz ] S        ∎
              where
                open ≡-Reasoning

            open Equiv-Reasoning _ _

soundness-fundamental : ∀ M → Γ ⊨ M `: A
soundness-fundamental (`! x)   Δ σ ρ gσ                          = soundness-fundamental-Var x Δ σ ρ gσ
soundness-fundamental `zero    Δ σ ρ gσ                          = Equiv-refl
soundness-fundamental `suc     Δ σ ρ gσ Γ'≤Δ {N} ga              = N , Equiv-refl , ga
soundness-fundamental `rec     Δ σ ρ gσ                          = soundness-fundamental-rec Δ σ ρ gσ
soundness-fundamental (`λ M)   Δ σ ρ gσ Γ'≤Δ {N} ga              = gluing-respects-Equiv (soundness-fundamental M _ ([Γ'≤Δ]σ `, N) (ρ , _) (kripke-Sub Γ'≤Δ gσ , ga))
  (begin [ [Γ'≤Δ]σ `, N ] M                                    ≡˘⟨ cong ([_] M) (cong (_`, _) ([idSub]⇒id [Γ'≤Δ]σ)) ⟩
         [ [ ^id ] [Γ'≤Δ]σ `, N ] M                            ≡˘⟨ cong ([_] M) (cong (_`, _) (cong ([_] [Γ'≤Δ]σ) ([]-idWk⇒id ^id))) ⟩
         [ [ [ ^id ] idWk ] [Γ'≤Δ]σ `, N ] M                   ≡˘⟨ cong ([_] M) (cong (_`, _) ([]-wk[]-compose idN (`wk ^id) [Γ'≤Δ]σ)) ⟩
         [ [ idN ] (wk1 [Γ'≤Δ]σ) `, N ] M                      ≡˘⟨ []-compose idN (^ext [Γ'≤Δ]σ) M ⟩
         [ idN ] [ ^ext [Γ'≤Δ]σ ] M                            ≡⟨ cong ([ idN ]_) (cong ([_] M) (cong (_`, _) (wk[]-compose (`wk ^id) wkΓ'≤Δ σ))) ⟩
         [ idN ] [ wk[ wk1 wkΓ'≤Δ ] σ `, `! here ] M           ≡⟨ cong ([ idN ]_) (cong ([_] M) (cong (_`, _) (cong (wk[_] σ) (wk[idWk]⇒id (`wk wkΓ'≤Δ))))) ⟩
         [ idN ] [ wk[ `wk wkΓ'≤Δ ] σ `, `! here ] M           ≡˘⟨ cong ([ idN ]_) (cong ([_] M) (cong (_`, _) (cong (wk[_] σ) (wk[]-idWk⇒id (`wk wkΓ'≤Δ))))) ⟩
         [ idN ] [ wk[ wk[ `wk wkΓ'≤Δ ] ^id ] σ `, `! here ] M ≡˘⟨ cong ([ idN ]_) (cong ([_] M) (cong (_`, _) (wk[]-compose (^ext wkΓ'≤Δ) (`wk ^id) σ))) ⟩
         [ idN ] [ wk[ ^ext wkΓ'≤Δ ] wk1 σ `, `! here ] M      ≡˘⟨ cong ([ idN ]_) (wk[]-[]-compose (^ext wkΓ'≤Δ) (^ext σ) M) ⟩
         [ idN ] wk[ ^ext wkΓ'≤Δ ] [ ^ext σ ] M                ≈˘⟨ `β-`→ ⟩
         (`λ wk[ ^ext wkΓ'≤Δ ] [ ^ext σ ] M) `$ N              ∎)
  where
    idN = ^id `, N
    [Γ'≤Δ]σ = ctx≤[ Γ'≤Δ ] σ
    wkΓ'≤Δ = fromCtx≤ Γ'≤Δ
    open Equiv-Reasoning _ _
soundness-fundamental (M `$ N) Δ σ ρ gσ
  with ⊨M ← soundness-fundamental M Δ σ ρ gσ
     | ⊨N ← soundness-fundamental N Δ σ ρ gσ
    with gM$N ← ⊨M `id ⊨N                                        = subst (λ x → gluing Δ _ (x `$ [ σ ] N) (⟦ M ⟧ ρ (⟦ N ⟧ ρ))) (wk[idWk]⇒id ([ σ ] M)) gM$N

initial-env : Γ ⊢s ^id `: Γ ® ↑[ Γ ]
initial-env {`·}     = tt
initial-env {Γ `, A} = kripke-Sub (`wk `id) initial-env , realizability-bot (var-bot {A = A})

soundness : ∀ {M} →
            Γ ⊢ M ≋ embed (nbe M) `: A
soundness {M = M} =
  begin M                   ≡˘⟨ [idSub]⇒id M ⟩
        [ ^id ] M           ≡˘⟨ wk[idWk]⇒id ([ ^id ] M) ⟩
        wk[ ^id ] [ ^id ] M ≈⟨ realizability-top (soundness-fundamental M _ _ _ initial-env) `id ⟩
        embed (nbe M)       ∎
  where
    open Equiv-Reasoning _ _
