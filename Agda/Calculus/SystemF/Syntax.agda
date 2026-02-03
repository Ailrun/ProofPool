module Calculus.SystemF.Syntax where

open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; nothing; just)
open import Data.Nat using (ℕ; suc; _+_)

open import Calculus.GeneralOpSem

data Ty : Set where
  bot : Ty
  _⇒_ : Ty → Ty → Ty
  ‼_  : Ty → Ty
  #_  : ℕ → Ty

data Tm : Set where
  Λ‼_   : Tm → Tm
  _$‼_  : Tm → Ty → Tm
  λ⦂_∙_ : Ty → Tm → Tm
  _$_   : Tm → Tm → Tm
  #_    : ℕ → Tm

Ctx = List (Maybe Ty)

infix   5 ty

pattern kindTy = nothing
pattern ty Q = just Q

variable
  a a′ a″ a‴ a₀ a₁ a₂ a₃ : ℕ
  b b′ b″ b‴ b₀ b₁ b₂ b₃ : ℕ
  c c′ c″ c‴ c₀ c₁ c₂ c₃ : ℕ
  x x′ x″ x‴ x₀ x₁ x₂ x₃ : ℕ
  y y′ y″ y‴ y₀ y₁ y₂ y₃ : ℕ
  z z′ z″ z‴ z₀ z₁ z₂ z₃ : ℕ

  Q Q′ Q″ Q‴ Q₀ Q₁ Q₂ Q₃ : Ty
  R R′ R″ R‴ R₀ R₁ R₂ R₃ : Ty
  S S′ S″ S‴ S₀ S₁ S₂ S₃ : Ty
  T T′ T″ T‴ T₀ T₁ T₂ T₃ : Ty

  q q′ q″ q‴ q₀ q₁ q₂ q₃ : Tm
  r r′ r″ r‴ r₀ r₁ r₂ r₃ : Tm
  s s′ s″ s‴ s₀ s₁ s₂ s₃ : Tm
  t t′ t″ t‴ t₀ t₁ t₂ t₃ : Tm

  E E′ E″ E‴ E₀ E₁ E₂ E₃ : Maybe Ty

  Γ Γ′ Γ″ Γ‴ Γ₀ Γ₁ Γ₂ Γ₃ : Ctx
  Δ Δ′ Δ″ Δ‴ Δ₀ Δ₁ Δ₂ Δ₃ : Ctx
  Ψ Ψ′ Ψ″ Ψ‴ Ψ₀ Ψ₁ Ψ₂ Ψ₃ : Ctx

infixr 30 wkCtx[_]_
infixr 30 wkTy[_↑_]_
infixr 30 wk[Ty_↑_]_
infixr 30 wk[_↑_]_
infixr 30 Ty[_/_]_
infixr 30 Ctx[_]_
infixr 30 [Ty_/_]_
infixr 30 [_/_]_

wkTy[_↑_]_ : ℕ → ℕ → Ty → Ty
wkTy[ n ↑ a ] bot     = bot
wkTy[ n ↑ a ] (Q ⇒ R) = (wkTy[ n ↑ a ] Q) ⇒ (wkTy[ n ↑ a ] R)
wkTy[ n ↑ a ] (‼ Q)   = ‼ (wkTy[ n ↑ suc a ] Q)
wkTy[ n ↑ a ] (# b)   = # wkidx[ n ↑ a ] b

wkCtx[_]_ : ℕ → Ctx → Ctx
wkCtx[ n ] []           = []
wkCtx[ n ] (kindTy ∷ Γ) = kindTy ∷ wkCtx[ n ] Γ
wkCtx[ n ] (ty Q   ∷ Γ) = ty (wkTy[ n ↑ length Γ ] Q) ∷ wkCtx[ n ] Γ

wk[Ty_↑_]_ : ℕ → ℕ → Tm → Tm
wk[Ty n ↑ a ] (Λ‼ q)     = Λ‼ (wk[Ty n ↑ suc a ] q)
wk[Ty n ↑ a ] (q $‼ Q)   = (wk[Ty n ↑ a ] q) $‼ (wkTy[ n ↑ a ] Q)
wk[Ty n ↑ a ] (λ⦂ Q ∙ q) = λ⦂ (wkTy[ n ↑ a ] Q) ∙ (wk[Ty n ↑ a ] q)
wk[Ty n ↑ a ] (q $ r)    = (wk[Ty n ↑ a ] q) $ (wk[Ty n ↑ a ] r)
wk[Ty n ↑ a ] (# x)      = # x

wk[_↑_]_ : ℕ → ℕ → Tm → Tm
wk[ n ↑ x ] (Λ‼ q)     = Λ‼ (wk[ n ↑ x ] q)
wk[ n ↑ x ] (q $‼ Q)   = (wk[ n ↑ x ] q) $‼ Q
wk[ n ↑ x ] (λ⦂ Q ∙ q) = λ⦂ Q ∙ (wk[ n ↑ suc x ] q)
wk[ n ↑ x ] (q $ r)    = (wk[ n ↑ x ] q) $ (wk[ n ↑ x ] r)
wk[ n ↑ x ] (# y)      = # wkidx[ n ↑ x ] y

wkTy = wkTy[ 1 ↑ 0 ]_
wk[Ty] = wk[Ty 1 ↑ 0 ]_
wk = wk[ 1 ↑ 0 ]_

Ty[_/_]_ : Ty → ℕ → Ty → Ty
Ty[ Q / a ] bot     = bot
Ty[ Q / a ] (R ⇒ S) = Ty[ Q / a ] R ⇒ Ty[ Q / a ] S
Ty[ Q / a ] (‼ R)   = ‼ (Ty[ wkTy Q / suc a ] R)
Ty[ Q / a ] (# b)   = idx[ Q / a ] b along #_

Ctx[_]_ : Ty → Ctx → Ctx
Ctx[ Q ] []           = []
Ctx[ Q ] (kindTy ∷ Γ) = kindTy ∷ Ctx[ Q ] Γ
Ctx[ Q ] (ty R ∷ Γ)   = ty (Ty[ Q / length Γ ] R) ∷ Ctx[ Q ] Γ

[Ty_/_]_ : Ty → ℕ → Tm → Tm
[Ty Q / a ] (Λ‼ q)     = Λ‼ ([Ty wkTy Q / suc a ] q)
[Ty Q / a ] (q $‼ R)   = ([Ty Q / a ] q) $‼ (Ty[ Q / a ] R)
[Ty Q / a ] (λ⦂ R ∙ q) = λ⦂ (Ty[ Q / a ] R) ∙ ([Ty Q / a ] q)
[Ty Q / a ] (q $ r)    = ([Ty Q / a ] q) $ ([Ty Q / a ] r)
[Ty Q / a ] (# x)      = # x

[_/_]_ : Tm → ℕ → Tm → Tm
[ q / x ] (Λ‼ r)     = Λ‼ ([ wk[Ty] q / x ] r)
[ q / x ] (r $‼ Q)   = ([ q / x ] r) $‼ Q
[ q / x ] (λ⦂ Q ∙ r) = λ⦂ Q ∙ ([ wk q / suc x ] r)
[ q / x ] (r $ s)    = ([ q / x ] r) $ ([ q / x ] s)
[ q / x ] (# y)      = idx[ q / x ] y along #_
