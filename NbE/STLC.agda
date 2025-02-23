{-# OPTIONS --overlapping-instances #-}
module NbE.STLC where

open import Data.Bool
open import Data.Nat
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
  `N   : Ty
  _`→_ : Ty → Ty → Ty
infixr 40 _`→_

_Ty≟_ : ∀ (A A' : Ty) →
        ----------------
         Dec (A ≡ A')
`N       Ty≟ `N         = yes refl
`N       Ty≟ (A' `→ B') = no λ ()
(A `→ B) Ty≟ `N         = no λ ()
(A `→ B) Ty≟ (A' `→ B') = Dec.map′ (λ{ (refl , refl) → refl }) (λ{ refl → refl , refl }) ((A Ty≟ A') Dec.×-dec (B Ty≟ B'))

data Ctx : Set where
  `·   : Ctx
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
  `id : ----------
         Γ Ctx≤ Γ

  `wk :  Γ Ctx≤ Δ →
        ---------------
         Γ `, A Ctx≤ Δ

data _⊢Wk:_ : Ctx → Ctx → Set where
  `·   : -----------
          Γ ⊢Wk: `·

  `wk  :  Γ ⊢Wk: Δ →
         ---------------
          Γ `, A ⊢Wk: Δ

  `ext :  Γ ⊢Wk: Δ →
         --------------------
          Γ `, A ⊢Wk: Δ `, A

data _⊢Sub:_ : Ctx → Ctx → Set where
  `·   : ------------
          Γ ⊢Sub: `·

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

Γ≰Γ,,Δ,A :  Δ ≡ Γ `,, Γ' `, A →
           ---------------------
            ¬ Γ Ctx≤ Δ
Γ≰Γ,,Δ,A                                eq `id      = Γ≢Γ,,Δ,A eq
Γ≰Γ,,Δ,A {Γ = Γ `, B} {Γ' = Γ'} {A = A} eq (`wk Γ≤)
  rewrite `,,-associative Γ (`·, B) (Γ' `, A)       = Γ≰Γ,,Δ,A eq Γ≤

Ctx≤-Irrelevant : Irrelevant _Ctx≤_
Ctx≤-Irrelevant `id       `id        = refl
Ctx≤-Irrelevant `id       (`wk Γ≤Δ') with () ← Γ≰Γ,,Δ,A refl Γ≤Δ'
Ctx≤-Irrelevant (`wk Γ≤Δ) `id        with () ← Γ≰Γ,,Δ,A refl Γ≤Δ
Ctx≤-Irrelevant (`wk Γ≤Δ) (`wk Γ≤Δ') = cong `wk (Ctx≤-Irrelevant Γ≤Δ Γ≤Δ')

_Ctx≤?_ : ∀ Γ Δ →
          ----------------
           Dec (Γ Ctx≤ Δ)
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
             --------------------
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
    (begin wk[ ^ext δ ] [ ^ext σ ] M                ≡⟨ wk[]-[]-compose (^ext δ) (^ext σ) M ⟩
           [ wk[ ^ext δ ] wk1 σ `, `! here ] M      ≡⟨ cong (λ x → [ x `, _ ] M) (wk[]-compose (^ext δ) (`wk ^id) σ) ⟩
           [ wk[ wk[ `wk δ ] ^id ] σ `, `! here ] M ≡⟨ cong (λ x → [ x `, _ ] M) (cong (wk[_] σ) (wk[]-idWk⇒id (`wk δ))) ⟩
           [ wk[ `wk δ ] σ `, `! here ] M           ≡˘⟨ cong (λ x → [ x `, _ ] M) (cong (wk[_] σ) (wk[idWk]⇒id (`wk δ))) ⟩
           [ wk[ wk[ ^id ] `wk δ ] σ `, `! here ] M ≡˘⟨ cong (λ x → [ x `, _ ] M) (wk[]-compose (`wk ^id) δ σ) ⟩
           [ ^ext (wk[ δ ] σ) ] M                   ∎)
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
  []-wk[]-compose ⦃ AppWkSubComposeTm ⦄ σ δ (`! x)   = []-wk[]-compose σ δ x
  []-wk[]-compose ⦃ AppWkSubComposeTm ⦄ σ δ `zero    = refl
  []-wk[]-compose ⦃ AppWkSubComposeTm ⦄ σ δ `suc     = refl
  []-wk[]-compose ⦃ AppWkSubComposeTm ⦄ σ δ `rec     = refl
  []-wk[]-compose ⦃ AppWkSubComposeTm ⦄ σ δ (`λ M)   = cong `λ_
    (begin [ ^ext σ ] wk[ ^ext δ ] M    ≡⟨ []-wk[]-compose (^ext σ) (^ext δ) M ⟩
           [ [ wk1 σ ] δ `, `! here ] M ≡˘⟨ cong (λ x → [ x `, _ ] M) (wk[]-[]-compose (`wk ^id) σ δ) ⟩
           [ ^ext ([ σ ] δ) ] M         ∎)
    where
      open ≡-Reasoning
  []-wk[]-compose ⦃ AppWkSubComposeTm ⦄ σ δ (M `$ N) = cong₂ _`$_ ([]-wk[]-compose σ δ M) ([]-wk[]-compose σ δ N)

  AppWkSubComposeSub : AppWkSubCompose (_⊢Sub: Ψ')
  []-wk[]-compose ⦃ AppWkSubComposeSub ⦄ σ δ `·       = refl
  []-wk[]-compose ⦃ AppWkSubComposeSub ⦄ σ δ (τ `, M) = cong₂ _`,_ ([]-wk[]-compose σ δ τ) ([]-wk[]-compose σ δ M)

  CompatibleSubWkVar : CompatibleSubWk (_Include A)
  compatible-Sub-Wk ⦃ CompatibleSubWkVar ⦄ (`wk δ) x          =
    begin [ wk1 (fromWk δ) ] x           ≡˘⟨ wk[]-[]-compose (`wk ^id) (fromWk δ) x ⟩
          wk1 [ fromWk δ ] x             ≡⟨ cong wk1_ (compatible-Sub-Wk δ x) ⟩
          `! there (wk[ ^id ] wk[ δ ] x) ≡⟨ cong `!_ (cong there (wk[idWk]⇒id (wk[ δ ] x))) ⟩
          `! there (wk[ δ ] x)           ∎
    where
      open ≡-Reasoning
  compatible-Sub-Wk ⦃ CompatibleSubWkVar ⦄ (`ext δ) here      = refl
  compatible-Sub-Wk ⦃ CompatibleSubWkVar ⦄ (`ext δ) (there x) =
    begin [ wk1 (fromWk δ) ] x           ≡˘⟨ wk[]-[]-compose (`wk ^id) (fromWk δ) x ⟩
          wk1 [ fromWk δ ] x             ≡⟨ cong wk1_ (compatible-Sub-Wk δ x) ⟩
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
  compatible-Sub-Wk ⦃ CompatibleSubWkSub ⦄ δ `·       = refl
  compatible-Sub-Wk ⦃ CompatibleSubWkSub ⦄ δ (σ `, M) = cong₂ _`,_ (compatible-Sub-Wk δ σ) (compatible-Sub-Wk δ M)

  AppSubComposeVar : AppSubCompose (_Include A)
  []-compose ⦃ AppSubComposeVar ⦄ σ (τ `, M) here      = refl
  []-compose ⦃ AppSubComposeVar ⦄ σ (τ `, M) (there x) = []-compose σ τ x

  AppSubComposeTm : AppSubCompose (_⊢Tm: A)
  []-compose ⦃ AppSubComposeTm ⦄ σ τ (`! x)   = []-compose σ τ x
  []-compose ⦃ AppSubComposeTm ⦄ σ τ `zero    = refl
  []-compose ⦃ AppSubComposeTm ⦄ σ τ `suc     = refl
  []-compose ⦃ AppSubComposeTm ⦄ σ τ `rec     = refl
  []-compose ⦃ AppSubComposeTm ⦄ σ τ (`λ M)   = cong `λ_
    (begin [ ^ext σ ] [ ^ext τ ] M               ≡⟨ []-compose (^ext σ) (^ext τ) M ⟩
           [ [ ^ext σ ] wk1 τ `, `! here ] M     ≡⟨ cong (λ x → [ x `, _ ] M) ([]-wk[]-compose (^ext σ) (`wk ^id) τ) ⟩
           [ [ [ wk1 σ ] idWk ] τ `, `! here ] M ≡⟨ cong (λ x → [ x `, _ ] M) (cong ([_] τ) ([]-idWk⇒id (wk1 σ))) ⟩
           [ [ wk1 σ ] τ `, `! here ] M          ≡˘⟨ cong (λ x → [ x `, _ ] M) (wk[]-[]-compose (`wk ^id) σ τ) ⟩
           [ ^ext ([ σ ] τ) ] M                  ∎)
    where
      open ≡-Reasoning
  []-compose ⦃ AppSubComposeTm ⦄ σ τ (M `$ N) = cong₂ _`$_ ([]-compose σ τ M) ([]-compose σ τ N)

idSub≡fromWk-idWk : ∀ {Γ} →
                    -----------------------------
                     idSub {Γ = Γ} ≡ fromWk idWk
idSub≡fromWk-idWk {`·}     = refl
idSub≡fromWk-idWk {Γ `, A} = cong (_`, `! here) (cong wk1_ idSub≡fromWk-idWk)

[idSub]⇒id : ∀ {F}
               ⦃ AppWkF : AppWk F ⦄
               ⦃ AppSubF : AppSub F ⦄
               ⦃ AppIdWk⇒IdF : AppIdWk⇒Id F ⦄
               ⦃ CompatibleSubWkF : CompatibleSubWk F ⦄
               (x : F Γ) →
             -------------------------------------------
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

ctx≤[]-fromCtx≤-commute : ∀ (Γ''≤Γ' : Γ'' Ctx≤ Γ')
                            (Γ'≤Γ : Γ' Ctx≤ Γ) →
                          -----------------------------------------------------------------
                           fromCtx≤ (ctx≤[ Γ''≤Γ' ] Γ'≤Γ) ≡ ctx≤[ Γ''≤Γ' ] (fromCtx≤ Γ'≤Γ)
ctx≤[]-fromCtx≤-commute `id          Γ'≤Γ = sym (wk[idWk]⇒id (fromCtx≤ Γ'≤Γ))
ctx≤[]-fromCtx≤-commute (`wk Γ''≤Γ') Γ'≤Γ = cong `wk (ctx≤[]-fromCtx≤-commute Γ''≤Γ' Γ'≤Γ)

ctx≤[]-compose : ∀ {F}
                   ⦃ AppWkF : AppWk F ⦄
                   ⦃ AppWkComposeF : AppWkCompose F ⦄
                   (Γ''≤Γ' : Γ'' Ctx≤ Γ')
                   (Γ'≤Γ : Γ' Ctx≤ Γ)
                   (x : F Γ) →
                 ---------------------------------------------------------------
                  ctx≤[ Γ''≤Γ' ] ctx≤[ Γ'≤Γ ] x ≡ ctx≤[ ctx≤[ Γ''≤Γ' ] Γ'≤Γ ] x
ctx≤[]-compose Γ''≤Γ' Γ'≤Γ x =
  begin ctx≤[ Γ''≤Γ' ] ctx≤[ Γ'≤Γ ] x        ≡⟨ wk[]-compose (fromCtx≤ Γ''≤Γ') (fromCtx≤ Γ'≤Γ) x ⟩
        wk[ ctx≤[ Γ''≤Γ' ] fromCtx≤ Γ'≤Γ ] x ≡˘⟨ cong (wk[_] x) (ctx≤[]-fromCtx≤-commute Γ''≤Γ' Γ'≤Γ) ⟩
        ctx≤[ ctx≤[ Γ''≤Γ' ] Γ'≤Γ ] x        ∎
  where
    open ≡-Reasoning

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

Equiv-Sub : ∀ {M M'} σ →
             Γ ⊢ M ≋ M' `: A →
            -----------------------------
             Δ ⊢ [ σ ] M ≋ [ σ ] M' `: A
Equiv-Sub {M = (`λ M) `$ N} {M' = _}  σ `β-`→                =
  begin (`λ [ ^ext σ ] M) `$ [ σ ] N          ≈⟨ `β-`→ ⟩
        [ [ σ ] N 1] [ ^ext σ ] M             ≡⟨ []-compose (^id `, [ σ ] N) (^ext σ) M ⟩
        [ [ [ σ ] N 1] wk1 σ `, [ σ ] N ] M   ≡⟨ cong (λ x → [ x `, [ σ ] N ] M) ([]-wk[]-compose (^id `, [ σ ] N) (`wk ^id) σ) ⟩
        [ [ [ idSub ] idWk ] σ `, [ σ ] N ] M ≡⟨ cong (λ x → [ [ x ] σ `, [ σ ] N ] M) ([]-idWk⇒id idSub) ⟩
        [ [ idSub ] σ `, [ σ ] N ] M          ≡⟨ cong (λ x → [ x `, [ σ ] N ] M) ([idSub]⇒id σ) ⟩
        [ σ `, [ σ ] N ] M                    ≡˘⟨ cong (λ x → [ x `, [ σ ] N ] M) ([]-idSub⇒id σ) ⟩
        [ [ σ ] idSub `, [ σ ] N ] M          ≡˘⟨ []-compose σ (^id `, N) M ⟩
        [ σ ] [ ^id `, N ] M                  ∎
  where
    open Equiv-Reasoning _ _
Equiv-Sub                             σ `β-`N₀               = `β-`N₀
Equiv-Sub                             σ `β-`N₁               = `β-`N₁
Equiv-Sub                   {M' = M'} σ `η-`→                =
  begin `λ [ ^ext σ ] wk1 M' `$ `! here     ≡⟨ cong (λ x → `λ x `$ _) ([]-wk[]-compose (^ext σ) (`wk ^id) M') ⟩
        `λ [ [ wk1 σ ] idWk ] M' `$ `! here ≡⟨ cong (λ x → `λ [ x ] M' `$ _) ([]-idWk⇒id (wk1 σ)) ⟩
        `λ [ wk1 σ ] M' `$ `! here          ≡˘⟨ cong (λ x → `λ x `$ _) (wk[]-[]-compose (`wk ^id) σ M') ⟩
        `λ wk1 [ σ ] M' `$ `! here          ≈⟨ `η-`→ ⟩
        [ σ ] M'                            ∎
  where
    open Equiv-Reasoning _ _
Equiv-Sub                             σ `ξ-`!                = Equiv-refl
Equiv-Sub                             σ `ξ-`zero             = `ξ-`zero
Equiv-Sub                             σ `ξ-`suc              = `ξ-`suc
Equiv-Sub                             σ `ξ-`rec              = `ξ-`rec
Equiv-Sub                             σ (`ξ-`λ M≋M')         = `ξ-`λ (Equiv-Sub (^ext σ) M≋M')
Equiv-Sub                             σ (`ξ- M≋M' `$ N≋N')   = `ξ- Equiv-Sub σ M≋M' `$ Equiv-Sub σ N≋N'
Equiv-Sub                             σ (`sym M≋M')          = `sym (Equiv-Sub σ M≋M')
Equiv-Sub                             σ (`trans M≋M' M'≋M'') = `trans (Equiv-Sub σ M≋M') (Equiv-Sub σ M'≋M'')

Equiv-Wk : ∀ {M M'} δ →
            Γ ⊢ M ≋ M' `: A →
           -----------------------------
            Δ ⊢ wk[ δ ] M ≋ wk[ δ ] M' `: A
Equiv-Wk {M = M} {M'} δ
  rewrite sym (compatible-Sub-Wk δ M)
        | sym (compatible-Sub-Wk δ M') = Equiv-Sub (fromWk δ)

Equiv-Ctx≤ : ∀ {M M'} Γ≤Δ →
              Γ ⊢ M ≋ M' `: A →
             -----------------------------------------
              Δ ⊢ ctx≤[ Γ≤Δ ] M ≋ ctx≤[ Γ≤Δ ] M' `: A
Equiv-Ctx≤ Γ≤Δ = Equiv-Wk (fromCtx≤ Γ≤Δ)

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
↓Nat (`⇑ u*)  Γ
  with u* Γ
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

module Completeness (fun-ext : ∀ {a b} → Extensionality a b) where
  module MeaningPreservation where
    meaning-preserving-Wk-Var : ∀ (δ : Γ ⊢Wk: Δ)
                                  (x : A ∈ Δ)
                                  (ρ : ⟦ Γ ⟧) →
                                -----------------------------------
                                 ⟦ wk[ δ ] x ⟧ ρ ≡ ⟦ x ⟧ (⟦ δ ⟧ ρ)
    meaning-preserving-Wk-Var (`wk δ)  x         (ρ , a) = meaning-preserving-Wk-Var δ x ρ
    meaning-preserving-Wk-Var (`ext δ) here      ρ       = refl
    meaning-preserving-Wk-Var (`ext δ) (there x) (ρ , a) = meaning-preserving-Wk-Var δ x ρ

    meaning-preserving-Wk : ∀ (δ : Γ ⊢Wk: Δ)
                              (M : Δ ⊢Tm: A)
                              (ρ : ⟦ Γ ⟧) →
                            -----------------------------------
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

    meaning-preserving-Sub-Var : ∀ (σ : Γ ⊢Sub: Δ)
                                   (x : A ∈ Δ)
                                   (ρ : ⟦ Γ ⟧) →
                                 ----------------------------------------------
                                  ⟦ [ σ ] x ⟧ ρ ≡ ⟦ x ⟧ (⟦ σ ⟧ ρ)
    meaning-preserving-Sub-Var (σ `, M) here      ρ = refl
    meaning-preserving-Sub-Var (σ `, M) (there x) ρ = meaning-preserving-Sub-Var σ x ρ

    ⟦idWk⟧-id : ∀ (ρ : ⟦ Γ ⟧) →
                ----------------
                 ⟦ idWk ⟧ ρ ≡ ρ
    ⟦idWk⟧-id {`·}     tt      = refl
    ⟦idWk⟧-id {Γ `, A} (ρ , a) = cong (_, a) (⟦idWk⟧-id ρ)

    meaning-preserving-Sub : ∀ (σ : Γ ⊢Sub: Δ)
                               (M : Δ ⊢Tm: A)
                               (ρ : ⟦ Γ ⟧) →
                             ---------------------------------
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

    ⟦idSub⟧-id : ∀ (ρ : ⟦ Γ ⟧) →
                 -----------------
                  ⟦ idSub ⟧ ρ ≡ ρ
    ⟦idSub⟧-id {`·}     tt      = refl
    ⟦idSub⟧-id {Γ `, A} (ρ , a) = cong (_, a)
      (begin ⟦ wk1 idSub ⟧ (ρ , a)  ≡⟨ meaning-preserving-Wk-Sub (`wk ^id) ^id (ρ , a) ⟩
             ⟦ idSub ⟧ (⟦ idWk ⟧ ρ) ≡⟨ cong ⟦ idSub ⟧ (⟦idWk⟧-id ρ) ⟩
             ⟦ idSub ⟧ ρ            ≡⟨ ⟦idSub⟧-id ρ ⟩
             ρ                      ∎)
      where
        open ≡-Reasoning

  open MeaningPreservation

  completeness-helper : ∀ {M M'} →
                         Γ ⊢ M ≋ M' `: A →
                        -------------------
                         ⟦ M ⟧ ≡ ⟦ M' ⟧
  completeness-helper {M = (`λ M) `$ N} `β-`→ = fun-ext λ ρ →
    begin ⟦ M ⟧ (ρ , ⟦ N ⟧ ρ)    ≡˘⟨ cong ⟦ M ⟧ (cong (_, ⟦ N ⟧ ρ) (⟦idSub⟧-id ρ)) ⟩
          ⟦ M ⟧ (⟦ ^id `, N ⟧ ρ) ≡˘⟨ meaning-preserving-Sub (^id `, N) M ρ ⟩
          ⟦ [ N 1] M ⟧ ρ         ∎
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

module Soundness where
  module GluingModel where
    gluingTm⊥ : ∀ Γ A → Γ ⊢Tm: A → Ne* A → Set
    syntax gluingTm⊥ Γ A M u* = Γ ⊢ M `: A ®⊥ u*
    Γ ⊢ M `: A ®⊥ u* = ∀ {Γ'} (Γ'≤Γ : Γ' Ctx≤ Γ) → ∃[ u ] u* Γ' ≡ inj₁ u × Γ' ⊢ ctx≤[ Γ'≤Γ ] M ≋ embed u `: A

    gluingTm⊤ : ∀ Γ A → Γ ⊢Tm: A → ⟦ A ⟧ → Set
    syntax gluingTm⊤ Γ A M a = Γ ⊢ M `: A ®⊤ a
    Γ ⊢ M `: A ®⊤ a = ∀ {Γ'} (Γ'≤Γ : Γ' Ctx≤ Γ) → Γ' ⊢ ctx≤[ Γ'≤Γ ] M ≋ embed (↓[ A ] a Γ') `: A

    gluingNat : ∀ Γ → Γ ⊢Tm: `N → Nat → Set
    syntax gluingNat Γ M a = Γ ⊢ M ®Nat a
    gluingNat Γ M `zero    = Γ ⊢ M ≋ `zero `: `N
    gluingNat Γ M (`suc n) = ∃[ M' ] Γ ⊢ M ≋ `suc `$ M' `: `N × Γ ⊢ M' ®Nat n
    gluingNat Γ M (`⇑ u*)  = Γ ⊢ M `: `N ®⊥ u*

    gluingTm : ∀ Γ A → Γ ⊢Tm: A → ⟦ A ⟧ → Set
    syntax gluingTm Γ A M a = Γ ⊢ M `: A ® a
    gluingTm Γ `N       M n = Γ ⊢ M ®Nat n
    gluingTm Γ (A `→ B) M f = ∀ {Γ'} (Γ'≤Γ : Γ' Ctx≤ Γ) → ∀ {N : Γ' ⊢Tm: A} {a} → Γ' ⊢ N `: A ® a → Γ' ⊢ ctx≤[ Γ'≤Γ ] M `$ N `: B ® f a

    gluingSub : ∀ Γ Δ → Γ ⊢Sub: Δ → ⟦ Δ ⟧ → Set
    syntax gluingSub Γ Δ σ ρ = Γ ⊢s σ `: Δ ® ρ
    Γ ⊢s `·     `: `·     ® tt      = ⊤
    Γ ⊢s σ `, M `: Δ `, A ® (ρ , a) = Γ ⊢s σ `: Δ ® ρ × Γ ⊢ M `: A ® a

  open GluingModel

  module KripkeProperty where
    kripkeGluingNat : ∀ {M n} (Γ'≤Γ : Γ' Ctx≤ Γ) →
                       Γ ⊢ M ®Nat n →
                      ----------------------------
                       Γ' ⊢ ctx≤[ Γ'≤Γ ] M ®Nat n
    kripkeGluingNat         {n = `zero}  Γ'≤Γ equiv                             = Equiv-Ctx≤ Γ'≤Γ equiv
    kripkeGluingNat         {n = `suc n} Γ'≤Γ (M' , equiv , natM')              = ctx≤[ Γ'≤Γ ] M' , Equiv-Ctx≤ Γ'≤Γ equiv , kripkeGluingNat Γ'≤Γ natM'
    kripkeGluingNat {M = M} {n = `⇑ x}   Γ'≤Γ ⊥M                   {Γ''} Γ''≤Γ'
      with u , eq , equiv ← ⊥M (ctx≤[ Γ''≤Γ' ] Γ'≤Γ)                            = u , eq ,
        (begin ctx≤[ Γ''≤Γ' ] ctx≤[ Γ'≤Γ ] M ≡⟨ ctx≤[]-compose Γ''≤Γ' Γ'≤Γ M ⟩
               ctx≤[ ctx≤[ Γ''≤Γ' ] Γ'≤Γ ] M ≈⟨ equiv ⟩
               embed u                       ∎)
      where
        open Equiv-Reasoning _ _

    kripkeGluingTm : ∀ {M a} (Γ'≤Γ : Γ' Ctx≤ Γ) →
                      Γ ⊢ M `: A ® a →
                     -------------------------------
                      Γ' ⊢ ctx≤[ Γ'≤Γ ] M `: A ® a
    kripkeGluingTm {A = `N}                                     = kripkeGluingNat
    kripkeGluingTm {A = A `→ B} {M = M} Γ'≤Γ gM {Γ''} Γ''≤Γ' gN
      rewrite ctx≤[]-compose Γ''≤Γ' Γ'≤Γ M                      = gM (ctx≤[ Γ''≤Γ' ] Γ'≤Γ) gN

    kripkeGluingTm⊥ : ∀ {M u} (Γ'≤Γ : Γ' Ctx≤ Γ) →
                       Γ ⊢ M `: A ®⊥ u →
                      -------------------------------
                       Γ' ⊢ ctx≤[ Γ'≤Γ ] M `: A ®⊥ u
    kripkeGluingTm⊥ {M = M} Γ'≤Γ ⊥M Γ''≤Γ'
      with u , eq , equivA ← ⊥M (ctx≤[ Γ''≤Γ' ] Γ'≤Γ)
        rewrite ctx≤[]-compose Γ''≤Γ' Γ'≤Γ M = u , eq , equivA

    kripkeGluingSub : ∀ {σ ρ} (Γ'≤Γ : Γ' Ctx≤ Γ) →
                       Γ ⊢s σ `: Δ ® ρ →
                      -------------------------------
                       Γ' ⊢s ctx≤[ Γ'≤Γ ] σ `: Δ ® ρ
    kripkeGluingSub {Δ = `·}     {σ = `·}     {ρ = tt}    Γ'≤Γ tt        = tt
    kripkeGluingSub {Δ = Δ `, x} {σ = σ `, M} {ρ = ρ , a} Γ'≤Γ (gσ , ga) = kripkeGluingSub Γ'≤Γ gσ , kripkeGluingTm {M = M} Γ'≤Γ ga

  open KripkeProperty

  module EquivRespect where
    gluingNat-respects-Equiv : ∀ {M M' a} →
                                 Γ ⊢ M ®Nat a →
                                 Γ ⊢ M ≋ M' `: `N →
                                --------------------
                                 Γ ⊢ M' ®Nat a
    gluingNat-respects-Equiv {a = `zero}  equiv                M≋M'      = `trans (`sym M≋M') equiv
    gluingNat-respects-Equiv {a = `suc a} (M' , equiv , natM') M≋M'      = M' , `trans (`sym M≋M') equiv , natM'
    gluingNat-respects-Equiv {a = `⇑ x}   ⊥M                   M≋M' Γ'≤Γ
      with u , eq , equiv ← ⊥M Γ'≤Γ                                       = u , eq , `trans (`sym (Equiv-Ctx≤ Γ'≤Γ M≋M')) equiv

    gluingTm-respects-Equiv : ∀ {M M' a} →
                               Γ ⊢ M `: A ® a →
                               Γ ⊢ M ≋ M' `: A →
                              -------------------
                               Γ ⊢ M' `: A ® a
    gluingTm-respects-Equiv {A = `N}                     = gluingNat-respects-Equiv
    gluingTm-respects-Equiv {A = A `→ B} gM M≋M' Γ'≤Γ gN = gluingTm-respects-Equiv (gM Γ'≤Γ gN) (`ξ- (Equiv-Ctx≤ Γ'≤Γ M≋M') `$ Equiv-refl)

  open EquivRespect

  gluingTm⊥-var : Γ `, A ⊢ `! here `: A ®⊥ Ne*! Γ A
  gluingTm⊥-var Γ'≤Γ,A
    with eq ← dec-yes-irr (_ Ctx≤? _) Ctx≤-Irrelevant Γ'≤Γ,A
      rewrite eq = `! ctx≤[ Γ'≤Γ,A ] here , refl , Equiv-refl

  gluingTm⊥-app : ∀ {M u* N a} →
                   Γ ⊢ M `: A `→ B ®⊥ u* →
                   Γ ⊢ N `: A ®⊤ a →
                  ---------------------------------------
                   Γ ⊢ M `$ N `: B ®⊥ (u* Ne*$ ↓[ A ] a)
  gluingTm⊥-app {a = a} ⊥A→B ⊤A {Γ'} Γ'≤Γ
    with u , eq , equivA→B ← ⊥A→B Γ'≤Γ
       | equivA ← ⊤A Γ'≤Γ
      rewrite eq                       = u `$ ↓[ _ ] a _ , refl , `ξ- equivA→B `$ equivA

  module GluingRealizability where
    realizability-nat-top : ∀ {M n} →
                             Γ ⊢ M ®Nat n →
                            ------------------
                             Γ ⊢ M `: `N ®⊤ n
    realizability-nat-top {M = M} {n = `zero}  equiv                Γ'≤Γ = Equiv-Ctx≤ Γ'≤Γ equiv
    realizability-nat-top {M = M} {n = `suc n} (M' , equiv , natM') Γ'≤Γ = `trans (Equiv-Ctx≤ Γ'≤Γ equiv) (`ξ- `ξ-`suc `$ realizability-nat-top natM' Γ'≤Γ)
    realizability-nat-top {M = M} {n = `⇑ x}   ⊥M                   Γ'≤Γ
      with u , eq , equiv ← ⊥M Γ'≤Γ
        rewrite eq                                                       = equiv

    realizability-bot : ∀ {M u} →
                         Γ ⊢ M `: A ®⊥ u →
                        -----------------------
                         Γ ⊢ M `: A ® ↑[ A ] u
    realizability-top : ∀ {M a} →
                         Γ ⊢ M `: A ® a →
                        ------------------
                         Γ ⊢ M `: A ®⊤ a

    gluingTm-var : Γ `, A ⊢ `! here `: A ® ↑[ A ] (Ne*! Γ A)
    gluingTm-var {A = A} = realizability-bot (gluingTm⊥-var {A = A})

    realizability-bot {A = `N}     ⊥N           = ⊥N
    realizability-bot {A = A `→ B} ⊥A→B Γ'≤Γ gA = realizability-bot (gluingTm⊥-app (kripkeGluingTm⊥ Γ'≤Γ ⊥A→B) (realizability-top gA))

    realizability-top {A = `N}                             = realizability-nat-top
    realizability-top {A = A `→ B} {M = M} {a = a} gA Γ'≤Γ =
      begin Γ'⊢M                                        ≈˘⟨ `η-`→ ⟩
            `λ wk1 Γ'⊢M `$ `! here                      ≡⟨ cong `λ_ (cong (_`$ _) (ctx≤[]-compose (`wk ^id) Γ'≤Γ M)) ⟩
            `λ Γ',A⊢M `$ `! here                        ≡˘⟨ cong `λ_ (cong (_`$ _) (wk[idWk]⇒id Γ',A⊢M)) ⟩
            `λ wk[ ^id ] Γ',A⊢M `$ `! here              ≈⟨ `ξ-`λ (realizability-top (gA (`wk Γ'≤Γ) (gluingTm-var {A = A})) ^id) ⟩
            `λ embed (↓[ B ] (a (↑[ A ] (Ne*! _ A))) _) ∎
      where
        Γ'⊢M = ctx≤[ Γ'≤Γ ] M
        Γ',A⊢M = ctx≤[ `wk Γ'≤Γ ] M
        open Equiv-Reasoning _ _

  open GluingRealizability

  initial-env-Sub : Γ ⊢s ^id `: Γ ® ↑[ Γ ]
  initial-env-Sub {`·}     = tt
  initial-env-Sub {Γ `, A} = kripkeGluingSub (`wk ^id) initial-env-Sub , gluingTm-var {A = A}

  SoundnessTyping : ∀ Γ A (M : Γ ⊢Tm: A) → Set
  syntax SoundnessTyping Γ A M = Γ ⊨ M `: A
  SoundnessTyping Γ A M = ∀ Δ σ ρ → Δ ⊢s σ `: Γ ® ρ → Δ ⊢ [ σ ] M `: A ® ⟦ M ⟧ ρ

  soundness-fundamental-var : ∀ x → Γ ⊨ `! x `: A
  soundness-fundamental-var {Γ = Γ `, B} here      Δ (σ `, M) (ρ , a) (gσ , ga) = ga
  soundness-fundamental-var {Γ = Γ `, B} (there x) Δ (σ `, M) (ρ , a) (gσ , ga) = soundness-fundamental-var x Δ σ ρ gσ

  soundness-fundamental-rec : SoundnessTyping Γ (A `→ (`N `→ A `→ A) `→ `N `→ A) `rec
  soundness-fundamental-rec         Δ σ ρ gσ Γ'≤Δ {Z} {z} gz {Γz} Γz≤Γ' {S} {s} gs {Γs} Γs≤Γz {N} {`zero}  equiv                = gluingTm-respects-Equiv (kripkeGluingTm {M = Γz⊢Z} Γs≤Γz (kripkeGluingTm {M = Z} Γz≤Γ' gz))
    (begin Γs⊢Z             ≈˘⟨ `β-`N₀ ⟩
           recbody `$ `zero ≈˘⟨ `ξ- Equiv-refl `$ equiv ⟩
           recbody `$ N     ∎)
    where
      Γz⊢Z = ctx≤[ Γz≤Γ' ] Z
      Γs⊢Z = ctx≤[ Γs≤Γz ] Γz⊢Z
      recbody = `rec `$ Γs⊢Z `$ ctx≤[ Γs≤Γz ] S
      open Equiv-Reasoning _ _
  soundness-fundamental-rec         Δ σ ρ gσ Γ'≤Δ {Z} {z} gz {Γz} Γz≤Γ' {S} {s} gs {Γs} Γs≤Γz {N} {`suc n} (N' , equiv , natM') = gluingTm-respects-Equiv (gs Γs≤Γz natM' ^id (soundness-fundamental-rec Δ σ ρ gσ Γ'≤Δ gz Γz≤Γ' gs Γs≤Γz natM'))
    (begin wk[ ^id ] (Γs⊢S `$ N') `$ subrecexp ≡⟨ cong (_`$ subrecexp) (wk[idWk]⇒id (Γs⊢S `$ N')) ⟩
           Γs⊢S `$ N' `$ subrecexp             ≈˘⟨ `β-`N₁ ⟩
           recbody `$ (`suc `$ N')             ≈˘⟨ `ξ- Equiv-refl `$ equiv ⟩
           recbody `$ N                        ∎)
    where
      Γs⊢S = ctx≤[ Γs≤Γz ] S
      recbody = `rec `$ ctx≤[ Γs≤Γz ] ctx≤[ Γz≤Γ' ] Z `$ Γs⊢S
      subrecexp = recbody `$ N'
      open Equiv-Reasoning Γs _
  soundness-fundamental-rec {A = A} Δ σ ρ gσ Γ'≤Δ {Z} {z} gz {Γz} Γz≤Γ' {S} {s} gs {Γs} Γs≤Γz {N} {`⇑ u*}  ⊥N                   = realizability-bot rec⊥
    where
      Γz⊢Z = ctx≤[ Γz≤Γ' ] Z
      Γs⊢Z = ctx≤[ Γs≤Γz ] Γz⊢Z
      Γs⊢S = ctx≤[ Γs≤Γz ] S
      recexp = `rec `$ Γs⊢Z `$ Γs⊢S `$ N
  
      rec⊥ : Γs ⊢ recexp `: _ ®⊥ Ne*rec (↓[ _ ] z) (↓[ _ ] s) u*
      rec⊥ Δ≤Γs
        with u , eq , equiv ← ⊥N Δ≤Γs
          rewrite eq = _ , refl , `ξ- `ξ- `ξ- `ξ-`rec `$ equiv-z `$ equiv-s `$ equiv
        where
          Δ≤Γz = ctx≤[ Δ≤Γs ] Γs≤Γz
          Δ⊢S = ctx≤[ Δ≤Γz ] S
          Δ,N≤Γz = ctx≤[ `wk Δ≤Γs ] Γs≤Γz
          Δ,N⊢S = ctx≤[ Δ,N≤Γz ] S
  
          equiv-z =
            begin ctx≤[ Δ≤Γs ] Γs⊢Z            ≡⟨ ctx≤[]-compose Δ≤Γs Γs≤Γz Γz⊢Z ⟩
                  ctx≤[ Δ≤Γz ] Γz⊢Z            ≡⟨ ctx≤[]-compose Δ≤Γz Γz≤Γ' Z ⟩
                  ctx≤[ ctx≤[ Δ≤Γz ] Γz≤Γ' ] Z ≈⟨ realizability-top gz (ctx≤[ Δ≤Γz ] Γz≤Γ') ⟩
                  embed (↓[ _ ] z _)           ∎
            where
              open Equiv-Reasoning _ _
  
          s`!1 = `! there here
          s`!0 = `! here
          gs#0#1 = gs Δ,N≤Γz (λ {Δ'} → gluingTm⊥-var {A = `N}) (`wk ^id) (gluingTm-var {A = A})
  
          equiv-s =
            begin ctx≤[ Δ≤Γs ] Γs⊢S                         ≡⟨ ctx≤[]-compose Δ≤Γs Γs≤Γz S ⟩
                  Δ⊢S                                       ≈˘⟨ `η-`→ ⟩
                  `λ wk1 Δ⊢S `$ `! here                     ≈˘⟨ `ξ-`λ `η-`→ ⟩
                  `λ `λ wk1 wk1 Δ⊢S `$ s`!1 `$ s`!0         ≡⟨ cong (λ x → `λ `λ wk1 x `$ s`!1 `$ s`!0) (ctx≤[]-compose (`wk ^id) Δ≤Γz S) ⟩
                  `λ `λ wk1 Δ,N⊢S `$ s`!1 `$ s`!0           ≡˘⟨ cong (λ x → `λ `λ x) (wk[idWk]⇒id (wk1 Δ,N⊢S `$ s`!1 `$ s`!0)) ⟩
                  `λ `λ wk[ ^id ] wk1 Δ,N⊢S `$ s`!1 `$ s`!0 ≈⟨ `ξ-`λ (`ξ-`λ (realizability-top gs#0#1 ^id)) ⟩
                  embed (↓[ _ ] s _)                        ∎
            where
              open Equiv-Reasoning _ _

  soundness-fundamental : ∀ M →
                          ------------
                           Γ ⊨ M `: A
  soundness-fundamental (`! x)   Δ σ ρ gσ                          = soundness-fundamental-var x Δ σ ρ gσ
  soundness-fundamental `zero    Δ σ ρ gσ                          = Equiv-refl
  soundness-fundamental `suc     Δ σ ρ gσ Γ'≤Δ {N} ga              = N , Equiv-refl , ga
  soundness-fundamental `rec     Δ σ ρ gσ                          = soundness-fundamental-rec Δ σ ρ gσ
  soundness-fundamental (`λ M)   Δ σ ρ gσ Γ'≤Δ {N} ga              = gluingTm-respects-Equiv (soundness-fundamental M _ (Γ'⊢σ `, N) (ρ , _) (kripkeGluingSub Γ'≤Δ gσ , ga))
    (begin [ Γ'⊢σ `, N ] M                                      ≡˘⟨ cong (λ x → [ x `, _ ] M) ([idSub]⇒id Γ'⊢σ) ⟩
           [ [ ^id ] Γ'⊢σ `, N ] M                              ≡˘⟨ cong (λ x → [ [ x ] Γ'⊢σ `, _ ] M) ([]-idWk⇒id ^id) ⟩
           [ [ [ ^id ] idWk ] Γ'⊢σ `, N ] M                     ≡˘⟨ cong (λ x → [ x `, _ ] M) ([]-wk[]-compose (^id `, N) (`wk ^id) Γ'⊢σ) ⟩
           [ [ N 1] (wk1 Γ'⊢σ) `, N ] M                         ≡˘⟨ []-compose (^id `, N) (^ext Γ'⊢σ) M ⟩
           [ N 1] [ ^ext Γ'⊢σ ] M                               ≡⟨ cong (λ x → [ N 1] [ x `, `! here ] M) (ctx≤[]-compose (`wk ^id) Γ'≤Δ σ) ⟩
           [ N 1] [ Γ',A⊢σ `, `! here ] M                       ≡˘⟨ cong (λ x → [ N 1] [ wk[ x ] σ `, `! here ] M) (wk[]-idWk⇒id (fromCtx≤ (`wk Γ'≤Δ))) ⟩
           [ N 1] [ wk[ ctx≤[ `wk Γ'≤Δ ] ^id ] σ `, `! here ] M ≡˘⟨ cong (λ x → [ N 1] [ x `, `! here ] M) (wk[]-compose Γ',A⊢Δ,A (`wk ^id) σ) ⟩
           [ N 1] [ wk[ Γ',A⊢Δ,A ] wk1 σ `, `! here ] M         ≡˘⟨ cong ([ N 1]_) (wk[]-[]-compose Γ',A⊢Δ,A (^ext σ) M) ⟩
           [ N 1] wk[ Γ',A⊢Δ,A ] [ ^ext σ ] M                   ≈˘⟨ `β-`→ ⟩
           (`λ wk[ Γ',A⊢Δ,A ] [ ^ext σ ] M) `$ N                ∎)
    where
      Γ',A⊢σ = ctx≤[ `wk Γ'≤Δ ] σ
      Γ'⊢σ = ctx≤[ Γ'≤Δ ] σ
      Γ',A⊢Δ,A = ^ext (fromCtx≤ Γ'≤Δ)
      open Equiv-Reasoning _ _
  soundness-fundamental (M `$ N) Δ σ ρ gσ
    with ⊨M ← soundness-fundamental M Δ σ ρ gσ
       | ⊨N ← soundness-fundamental N Δ σ ρ gσ
      with gM$N ← ⊨M ^id ⊨N                                        = subst (λ x → Δ ⊢ x `$ [ σ ] N `: _ ® ⟦ M ⟧ ρ (⟦ N ⟧ ρ)) (wk[idWk]⇒id ([ σ ] M)) gM$N

  soundness : ∀ {M} →
              ----------------------------
               Γ ⊢ M ≋ embed (nbe M) `: A
  soundness {M = M} =
    begin M                   ≡˘⟨ [idSub]⇒id M ⟩
          [ ^id ] M           ≡˘⟨ wk[idWk]⇒id ([ ^id ] M) ⟩
          wk[ ^id ] [ ^id ] M ≈⟨ realizability-top (soundness-fundamental M _ _ _ initial-env-Sub) `id ⟩
          embed (nbe M)       ∎
    where
      open Equiv-Reasoning _ _
