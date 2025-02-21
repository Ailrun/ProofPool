module NbE.STLC where

open import Data.Bool
open import Data.Nat hiding (less-than-or-equal)
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Level using (Level)
open import Relation.Nullary.Decidable as Dec
open import Relation.Binary.PropositionalEquality hiding ([_])

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

  CtxEmptyWk : CtxEmpty _⊢Wk:_
  ^· ⦃ CtxEmptyWk ⦄ = `·

  CtxExtWk : CtxExt _⊢Wk:_
  ^ext ⦃ CtxExtWk ⦄ = `ext

  CtxIdGen : ∀ {F : Ctx → Ctx → Set} → ⦃ CtxEmpty F ⦄ → ⦃ CtxExt F ⦄ → CtxId F
  ^id ⦃ CtxIdGen {F} ⦄ {Γ = `·}     = ^·
  ^id ⦃ CtxIdGen {F} ⦄ {Γ = _ `, _} = ^ext (^id ⦃ CtxIdGen {F} ⦄)

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

  CtxEmptySub : CtxEmpty _⊢Sub:_
  ^· ⦃ CtxEmptySub ⦄ = `·

  CtxExtSub : CtxExt _⊢Sub:_
  ^ext ⦃ CtxExtSub ⦄ σ = wk1 σ `, `! here

  FromWkGen : ∀ {F : Ctx → Ctx → Set} → ⦃ CtxId F ⦄ → ⦃ ∀ {Δ} → AppWk (λ Γ → F Γ Δ) ⦄ → FromWk F
  fromWk ⦃ FromWkGen {F} ⦃ CtxIdF ⦄ ⦄ δ = wk[ δ ] (^id ⦃ CtxIdF ⦄)

  FromCtx≤Wk : FromCtx≤ _⊢Wk:_
  fromCtx≤ ⦃ FromCtx≤Wk ⦄ `id       = ^id
  fromCtx≤ ⦃ FromCtx≤Wk ⦄ (`wk Γ≤Δ) = `wk (fromCtx≤ Γ≤Δ)

  AppCtx≤Gen : ∀ {F : Ctx → Set} → ⦃ AppWk F ⦄ → AppCtx≤ F
  ctx≤[_]_ ⦃ AppCtx≤Gen ⦄ Γ≤Δ = wk[ fromCtx≤ Γ≤Δ ]_

record AppSub (F : Ctx → Set) : Set₁ where
  infixr 40 [_]_
  field
    AppSubOutput : Ctx → Set
    [_]_ : Γ ⊢Sub: Δ → F Δ → AppSubOutput Γ

  infixr 40 [_1]_
  [_1]_ : Γ ⊢Tm: A → F (Γ `, A) → AppSubOutput Γ
  [_1]_ L = [ ^id `, L ]_

open AppSub ⦃...⦄
instance
  AppSubVar : AppSub (_Include A)
  AppSubOutput ⦃ AppSubVar {A} ⦄ = _⊢Tm: A
  [_]_ ⦃ AppSubVar ⦄ (σ `, M) here      = M
  [_]_ ⦃ AppSubVar ⦄ (σ `, M) (there x) = [ σ ] x

  AppSubTm : AppSub (_⊢Tm: A) 
  AppSubOutput ⦃ AppSubTm {A} ⦄ = _⊢Tm: A
  [_]_ ⦃ AppSubTm ⦄ σ (`! x)   = [ σ ] x
  [_]_ ⦃ AppSubTm ⦄ σ `zero    = `zero
  [_]_ ⦃ AppSubTm ⦄ σ `suc     = `suc
  [_]_ ⦃ AppSubTm ⦄ σ `rec     = `rec
  [_]_ ⦃ AppSubTm ⦄ σ (`λ M)   = `λ [ ^ext σ ] M
  [_]_ ⦃ AppSubTm ⦄ σ (M `$ N) = [ σ ] M `$ [ σ ] N

  AppSubSub : AppSub (_⊢Sub: Ψ)
  AppSubOutput ⦃ AppSubSub {Ψ} ⦄ = _⊢Sub: Ψ
  [_]_ ⦃ AppSubSub ⦄ σ `· = `·
  [_]_ ⦃ AppSubSub ⦄ σ (τ `, M) = [ σ ] τ `, [ σ ] M

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
Ne*rec z s u Γ = Data.Sum.map₁ (`rec (z Γ) (s Γ)) (u Γ)

_Ne*$_ : Ne* (A `→ B) → Nf* A → Ne* B
(u Ne*$ v) Γ = Data.Sum.map₁ (_`$ v Γ) (u Γ)

data Nat : Set where
  `zero : Nat
  `suc  : Nat → Nat
  `⇑    : Ne* `N → Nat

↓Nat : Nat → Nf* `N
↓Nat `zero    Γ = `zero
↓Nat (`suc n) Γ = `suc (↓Nat n Γ)
↓Nat (`⇑ x)   Γ
  with x Γ
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

    ↑[_] ⦃ ReflectTy ⦄ `N       u   = `⇑ u
    ↑[_] ⦃ ReflectTy ⦄ (A `→ B) u a = ↑[ B ] (u Ne*$ ↓[ A ] a)

    ↓[_] ⦃ ReifyTy ⦄ `N       v = ↓Nat v
    ↓[_] ⦃ ReifyTy ⦄ (A `→ B) v Γ = `λ (↓[ B ] (v (↑[ A ] (Ne*! Γ A))) (Γ `, A))

  ReflectCtx : Reflect Ctx ⟦_⟧
  ↑[_] ⦃ ReflectCtx ⦄ `· = tt
  ↑[_] ⦃ ReflectCtx ⦄ (Γ `, A) = ↑[ Γ ] , (↑[ A ] (Ne*! Γ A))

⟦rec⟧ : ∀ A → ⟦ A `→ (`N `→ A `→ A) `→ `N `→ A ⟧
⟦rec⟧ A z s `zero    = z
⟦rec⟧ A z s (`suc n) = s n (⟦rec⟧ A z s n)
⟦rec⟧ A z s (`⇑ u)   = ↑[ A ] (Ne*rec (↓[ A ] z) (↓[ `N `→ A `→ A ] s) u)

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

idWk : Γ ⊢Wk: Γ
idWk = ^id

id-Wk⇒id-env : ∀ (ρ : ⟦ Γ ⟧) →
               ----------------------------------------------
                ⟦ idWk ⟧ ρ ≡ ρ
id-Wk⇒id-env {`·}     tt      = refl
id-Wk⇒id-env {Γ `, A} (ρ , a) = cong (_, a) (id-Wk⇒id-env ρ)

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

idSub : Γ ⊢Sub: Γ
idSub = ^id

id-Sub⇒id-env : ∀ (ρ : ⟦ Γ ⟧) →
                ----------------------------------------------
                 ⟦ idSub ⟧ ρ ≡ ρ
id-Sub⇒id-env {`·}     tt      = refl
id-Sub⇒id-env {Γ `, A} (ρ , a) = cong (_, a)
                                 (begin ⟦ wk1 idSub ⟧ (ρ , a)  ≡⟨ meaning-preserving-Wk-Sub (`wk ^id) ^id (ρ , a) ⟩
                                        ⟦ idSub ⟧ (⟦ idWk ⟧ ρ) ≡⟨ cong ⟦ idSub ⟧ (id-Wk⇒id-env ρ) ⟩
                                        ⟦ idSub ⟧ ρ            ≡⟨ id-Sub⇒id-env ρ ⟩
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
                                               ⟦ M ⟧ (⟦ σ ⟧ (⟦ idWk ⟧ ρ) , a) ≡⟨ cong ⟦ M ⟧ (cong (_, a) (cong ⟦ σ ⟧ (id-Wk⇒id-env ρ))) ⟩
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
                                              begin ⟦ M ⟧ (ρ , ⟦ N ⟧ ρ)    ≡˘⟨ cong ⟦ M ⟧ (cong (_, ⟦ N ⟧ ρ) (id-Sub⇒id-env ρ)) ⟩
                                                    ⟦ M ⟧ (⟦ ^id `, N ⟧ ρ) ≡˘⟨ meaning-preserving-Sub (^id `, N) M ρ ⟩
                                                    ⟦ [ ^id `, N ] M ⟧ ρ   ∎
  where
    open ≡-Reasoning
completeness-helper `β-`N₀                  = refl
completeness-helper `β-`N₁                  = refl
completeness-helper {M' = M'} `η-`→         = fun-ext λ ρ → fun-ext λ a → cong (λ f → f a)
                                              (begin ⟦ wk1 M' ⟧ (ρ , a) ≡⟨ meaning-preserving-Wk (`wk ^id) M' (ρ , a) ⟩
                                                     ⟦ M' ⟧ (⟦ idWk ⟧ ρ) ≡⟨ cong ⟦ M' ⟧ (id-Wk⇒id-env ρ) ⟩
                                                     ⟦ M' ⟧ ρ ∎)
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

-- Gluing : ∀ Γ A → Γ ⊢Tm: A → Ty⟦ A ⟧ → Set

-- syntax Gluing Γ A M a = Γ ⊢ M `: A ® a

-- Gluing Γ `N       M n = ∀ Γ' → Γ Ctx≥ Γ' → Γ' ⊢ {!!} ≋ embedNf (↓Nat n Γ') `: `N
-- Gluing Γ (A `→ B) M f = ∀ Γ' → Γ Ctx≥ Γ' → ∀ {N : Γ' ⊢Tm: A} {a} → Γ' ⊢ N `: A ® a → Γ' ⊢ {!!} `$ N `: B ® f a

-- soundness : ∀ {M} →
--             Γ ⊢ M ≋ embedNf (nbe M) `: A
-- soundness = {!!}
