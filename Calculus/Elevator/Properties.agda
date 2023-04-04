{-# OPTIONS --safe #-}
open import Calculus.Elevator.ModeSpec

module Calculus.Elevator.Properties ℓ₁ ℓ₂ (ℳ : ModeSpec ℓ₁ ℓ₂) where
private
  module ℳ = ModeSpec ℳ
open ℳ

open import Agda.Primitive
open import Data.Bool as Bool using (Bool; true; false)
import Data.Bool.Properties as Bool
open import Data.Empty as ⊥ using (⊥)
open import Data.List as List using (List; []; _∷_; _++_; length)
import Data.List.Properties as List
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as All
open import Data.Nat as ℕ using (ℕ; suc; _+_; s≤s)
import Data.Nat.Properties as ℕ
open import Data.Product as × using (_×_; _,_; proj₁; proj₂; ∃; ∃₂)
open import Data.Unit as ⊤ using (⊤)
import Function.Equivalence as FE
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.Definitions using (Monotonic₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst; subst₂; _≢_; ≢-sym)

import Calculus.Elevator.Syntax as S
import Calculus.Elevator.Typing as T
import Calculus.Elevator.OpSem as O
import Calculus.Elevator.Lemma as L
open S ℓ₁ ℓ₂ ℳ
open T ℓ₁ ℓ₂ ℳ
open O ℓ₁ ℓ₂ ℳ
open L ℓ₁ ℓ₂ ℳ

wk[↑]-preserves-⊢ : ∀ Δ →
                    Ψ is-all-deletable →
                    Δ ++ Γ ⊢[ m ] L ⦂ S →
                    ---------------------------------------------------
                    Δ ++ Ψ ++ Γ ⊢[ m ] wk[ length Ψ ↑ length Δ ] L ⦂ S
wk[↑]-preserves-⊢ Δ ΨDel (`unit ΔΓDel) = `unit (All.++⁺ (All.++⁻ˡ Δ ΔΓDel) (All.++⁺ ΨDel (All.++⁻ʳ Δ ΔΓDel)))
wk[↑]-preserves-⊢ Δ ΨDel (`λ⦂-∘ ⊢L) = `λ⦂-∘ wk[↑]-preserves-⊢ (_ ∷ Δ) ΨDel ⊢L
wk[↑]-preserves-⊢ {Ψ} {Γ} {m} {L `$ M} {S} Δ ΨDel (ΔΓ~ ⊢ ⊢L ⦂ ⊢⊸@(_`⊸[_]_ {S = T} _ _ _) `$ ⊢M)
  with Δ₀ , Δ₁ , Γ₀ , Γ₁ , refl , refl , Δ~ , Γ~ ← ~⊞-preserves-++ Δ ΔΓ~
     | Ψ₁ , Ψ~ ← left-bias-~⊞ Ψ
    with _    , Ψ₁Del ← ~⊞-preserves-is-all-deletable ΨDel Ψ~
       | eqΔ₀ , eqΔ₁ ← length-respects-~⊞ Δ~
       | _    , eqΨ₁ ← length-respects-~⊞ Ψ~ = ~⊞-++⁺ Δ~ (~⊞-++⁺ Ψ~ Γ~) ⊢ ⊢L′ ⦂ ⊢⊸ `$ ⊢M′
  where
    ⊢L′ : Δ₀ ++ Ψ ++ Γ₀ ⊢[ m ] wk[ length Ψ ↑ length Δ ] L ⦂ T `⊸ S
    ⊢L′
      rewrite sym eqΔ₀ = wk[↑]-preserves-⊢ Δ₀ ΨDel ⊢L

    ⊢M′ : Δ₁ ++ Ψ₁ ++ Γ₁ ⊢[ m ] wk[ length Ψ ↑ length Δ ] M ⦂ T
    ⊢M′
      rewrite sym eqΔ₁
            | sym eqΨ₁ = wk[↑]-preserves-⊢ Δ₁ Ψ₁Del ⊢M
wk[↑]-preserves-⊢ Δ ΨDel (`lift[-⇒-] ⊢L) = `lift[-⇒-] wk[↑]-preserves-⊢ Δ ΨDel ⊢L
wk[↑]-preserves-⊢ {Ψ} {Γ} {m} {`unlift[ m₀ ⇒ _ ] L} {S} Δ ΨDel (ΔΓ∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)
  with Δ′ , Γ′ , refl , Δ∤ , Γ∤ ← ∤-preserves-++ Δ ΔΓ∤
     | Ψ′ , Ψ∤ , _ ← is-all-deletable⇒∤ m₀ ΨDel
    with eqΔ′ ← length-respects-∤ Δ∤
       | eqΨ′ ← length-respects-∤ Ψ∤ = ∤-++⁺ Δ∤ (∤-++⁺ Ψ∤ Γ∤) ⊢`unlift[-⇒-] ⊢L′ ⦂ ⊢↑
  where
    ⊢L′ : Δ′ ++ Ψ′ ++ Γ′ ⊢[ m₀ ] wk[ length Ψ ↑ length Δ ] L ⦂ `↑[ m ⇒ m₀ ] S
    ⊢L′
      rewrite sym eqΔ′
            | sym eqΨ′ = wk[↑]-preserves-⊢ Δ′ (∤-preserves-is-all-deletable ΨDel Ψ∤) ⊢L
wk[↑]-preserves-⊢ {Ψ} {Γ} {m} {`return[ m₀ ⇒ _ ] L} {`↓[ _ ⇒ _ ] S}Δ ΨDel (ΔΓ∤ ⊢`return[-⇒-] ⊢L)
  with Δ′ , Γ′ , refl , Δ∤ , Γ∤ ← ∤-preserves-++ Δ ΔΓ∤
     | Ψ′ , Ψ∤ , _ ← is-all-deletable⇒∤ m₀ ΨDel
    with eqΔ′ ← length-respects-∤ Δ∤
       | eqΨ′ ← length-respects-∤ Ψ∤ = ∤-++⁺ Δ∤ (∤-++⁺ Ψ∤ Γ∤) ⊢`return[-⇒-] ⊢L′
  where
    ⊢L′ : Δ′ ++ Ψ′ ++ Γ′ ⊢[ m₀ ] wk[ length Ψ ↑ length Δ ] L ⦂ S
    ⊢L′
      rewrite sym eqΔ′
            | sym eqΨ′ = wk[↑]-preserves-⊢ Δ′ (∤-preserves-is-all-deletable ΨDel Ψ∤) ⊢L
wk[↑]-preserves-⊢ {Ψ} {Γ} {m} {`let-return[ _ ⇒ m₀ ] L `in M} {S} Δ ΨDel (ΔΓ~ ⊢`let-return[-⇒-] ⊢L ⦂ ⊢↓@(`↓[-⇒_][_]_ {S = T} _ _ _) `in ⊢M)
  with Δ₀ , Δ₁ , Γ₀ , Γ₁ , refl , refl , Δ~ , Γ~ ← ~⊞-preserves-++ Δ ΔΓ~
     | Ψ₁ , Ψ~ ← left-bias-~⊞ Ψ
    with _    , Ψ₁Del ← ~⊞-preserves-is-all-deletable ΨDel Ψ~
       | eqΔ₀ , eqΔ₁ ← length-respects-~⊞ Δ~
       | _    , eqΨ₁ ← length-respects-~⊞ Ψ~ = ~⊞-++⁺ Δ~ (~⊞-++⁺ Ψ~ Γ~) ⊢`let-return[-⇒-] ⊢L′ ⦂ ⊢↓ `in ⊢M′
  where
    ⊢L′ : Δ₀ ++ Ψ ++ Γ₀ ⊢[ m ] wk[ length Ψ ↑ length Δ ] L ⦂ `↓[ m₀ ⇒ m ] T
    ⊢L′
      rewrite sym eqΔ₀ = wk[↑]-preserves-⊢ Δ₀ ΨDel ⊢L

    ⊢M′ : (T , m₀ , true) ∷ Δ₁ ++ Ψ₁ ++ Γ₁ ⊢[ m ] wk[ length Ψ ↑ suc (length Δ) ] M ⦂ S
    ⊢M′
      rewrite sym eqΔ₁
            | sym eqΨ₁ = wk[↑]-preserves-⊢ (_ ∷ Δ₁) Ψ₁Del ⊢M
wk[↑]-preserves-⊢ Δ ΨDel (`#_ {x = y} y∈)
  with y ℕ.≥? length Δ
...  | yes y≥ = `# ≥∧∈-++⇒+-∈-++-++ Δ ΨDel y∈ y≥
...  | no  y≱ = `# <∧∈-++⇒∈-++-++ Δ ΨDel y∈ (ℕ.≰⇒> y≱)

⊢∧~⊞-is-all-deletable⇒⊢var : Γ ~ Γ₀ ⊞ Γ₁ →
                             Γ₀ is-all-deletable →
                             x ⦂[ m ] S ∈ Γ₁ →
                             x ⦂[ m ] S ∈ Γ
⊢∧~⊞-is-all-deletable⇒⊢var (contraction Co∈m ∷ Γ~) (d₀Del ∷ Γ₀Del) (here Γ₁Del) = here (~⊞⁻¹-preserves-is-all-deletable Γ₀Del Γ₁Del Γ~)
⊢∧~⊞-is-all-deletable⇒⊢var (to-right         ∷ Γ~) (d₀Del ∷ Γ₀Del) (here Γ₁Del) = here (~⊞⁻¹-preserves-is-all-deletable Γ₀Del Γ₁Del Γ~)
⊢∧~⊞-is-all-deletable⇒⊢var (d~               ∷ Γ~) (d₀Del ∷ Γ₀Del) (there d₁Del x∈) = there (~d⊞⁻¹-preserves-is-deletable d₀Del d₁Del d~) (⊢∧~⊞-is-all-deletable⇒⊢var Γ~ Γ₀Del x∈)

⊢∧~⊞-is-all-deletable⇒⊢ : Γ ~ Γ₀ ⊞ Γ₁ →
                          Γ₀ is-all-deletable →
                          Γ₁ ⊢[ m ] L ⦂ S →
                          Γ ⊢[ m ] L ⦂ S
⊢∧~⊞-is-all-deletable⇒⊢ Γ~ Γ₀Del (`unit Γ₁Del)                          = `unit (~⊞⁻¹-preserves-is-all-deletable Γ₀Del Γ₁Del Γ~)
⊢∧~⊞-is-all-deletable⇒⊢ Γ~ Γ₀Del (`λ⦂-∘ ⊢L)                             = `λ⦂-∘ ⊢∧~⊞-is-all-deletable⇒⊢ (to-right ∷ Γ~) (unusable ∷ Γ₀Del) ⊢L
⊢∧~⊞-is-all-deletable⇒⊢ Γ~ Γ₀Del (Γ₁~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)
  with _ , Γ₁′~ , Γ~′ ← ~⊞-assoc (~⊞-swap Γ~) (~⊞-swap Γ₁~) = ~⊞-swap Γ~′ ⊢ ⊢∧~⊞-is-all-deletable⇒⊢ (~⊞-swap Γ₁′~) Γ₀Del ⊢L ⦂ ⊢⊸ `$ ⊢M
⊢∧~⊞-is-all-deletable⇒⊢ Γ~ Γ₀Del (`lift[-⇒-] ⊢L)                        = `lift[-⇒-] (⊢∧~⊞-is-all-deletable⇒⊢ Γ~ Γ₀Del ⊢L)
⊢∧~⊞-is-all-deletable⇒⊢ {L = `unlift[ m₀ ⇒ _ ] L} Γ~ Γ₀Del (Γ₁∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)
  with _ , Γ₀∤ , Γ₀′Del ← is-all-deletable⇒∤ m₀ Γ₀Del
    with _ , Γ∤ , Γ′~ ← ~⊞⁻¹-preserves-∤ Γ₀∤ Γ₁∤ Γ~ = Γ∤ ⊢`unlift[-⇒-] ⊢∧~⊞-is-all-deletable⇒⊢ Γ′~ Γ₀′Del ⊢L ⦂ ⊢↑
⊢∧~⊞-is-all-deletable⇒⊢ {L = `return[ m₀ ⇒ _ ] L} Γ~ Γ₀Del (Γ₁∤ ⊢`return[-⇒-] ⊢L)
  with _ , Γ₀∤ , Γ₀′Del ← is-all-deletable⇒∤ m₀ Γ₀Del
    with _ , Γ∤ , Γ′~ ← ~⊞⁻¹-preserves-∤ Γ₀∤ Γ₁∤ Γ~ = Γ∤ ⊢`return[-⇒-] ⊢∧~⊞-is-all-deletable⇒⊢ Γ′~ Γ₀′Del ⊢L
⊢∧~⊞-is-all-deletable⇒⊢ Γ~ Γ₀Del (Γ₁~ ⊢`let-return[-⇒-] ⊢L ⦂ ⊢↓ `in ⊢M)
  with _ , Γ₁′~ , Γ~′ ← ~⊞-assoc (~⊞-swap Γ~) (~⊞-swap Γ₁~) = ~⊞-swap Γ~′ ⊢`let-return[-⇒-] (⊢∧~⊞-is-all-deletable⇒⊢ (~⊞-swap Γ₁′~) Γ₀Del ⊢L) ⦂ ⊢↓ `in ⊢M
⊢∧~⊞-is-all-deletable⇒⊢ Γ~ Γ₀Del (`# x∈)                                = `# ⊢∧~⊞-is-all-deletable⇒⊢var Γ~ Γ₀Del x∈

subst-targetvar : x ≡ y →
                  ∀ M →
                  Γ ⊢[ m ] [ L /[ m₀ ] x ] M ⦂ T →
                  Γ ⊢[ m ] [ L /[ m₀ ] y ] M ⦂ T
subst-targetvar {_} {_} {Γ} {m} {L} {m₀} {T} eq M = subst (λ x → Γ ⊢[ m ] [ L /[ m₀ ] x ] M ⦂ T) eq

[/]-preserves-⊢⁰ : ∀ Δ₀ →
                   ⊢[ m ] T ⦂⋆ →
                   Δ₀ ++ (S , m₀ , false) ∷ Ψ₀ ⊢[ m ] M ⦂ T →
                   ----------------------------------------------
                   Δ₀ ++ Ψ₀ ⊢[ m ] [ L /[ m₀ ] length Δ₀ ] M ⦂ T
[/]-preserves-⊢⁰ Δ₀ ⊢T (`unit Δ₀eΨ₀Del)
  with Δ₀Del , _ ∷ Ψ₀Del ← All.++⁻ Δ₀ Δ₀eΨ₀Del = `unit (All.++⁺ Δ₀Del Ψ₀Del)
[/]-preserves-⊢⁰ Δ₀ (⊢T₀ `⊸[ _ ] ⊢T₁) (`λ⦂-∘ ⊢M) = `λ⦂-∘ [/]-preserves-⊢⁰ (_ ∷ Δ₀) ⊢T₁ ⊢M
[/]-preserves-⊢⁰ {m} {T} {_} {m₀} {_} {M `$ N} {L} Δ₀ ⊢T (Δ₀SΨ₀~ ⊢ ⊢M ⦂ ⊢⊸ `$ ⊢N)
  with _`⊸[_]_ {S = S} ⊢S _ _ ← ⊢⊸
     | Δ₀₀ , Δ₀₁ , _ ∷ Ψ₀₀ , _ ∷ Ψ₀₁ , refl , refl , Δ₀~ , unusable ∷ Ψ₀~ ← ~⊞-preserves-++ Δ₀ Δ₀SΨ₀~
    with eqΔ₀₀ , eqΔ₀₁ ← length-respects-~⊞ Δ₀~ = ~⊞-++⁺ Δ₀~ Ψ₀~ ⊢ ⊢M′ ⦂ ⊢⊸ `$ ⊢N′
  where
    ⊢M′ : Δ₀₀ ++ Ψ₀₀ ⊢[ m ] [ L /[ m₀ ] length Δ₀ ] M ⦂ (S `⊸ T)
    ⊢M′
      rewrite sym eqΔ₀₀ = [/]-preserves-⊢⁰ Δ₀₀ ⊢⊸ ⊢M

    ⊢N′ : Δ₀₁ ++ Ψ₀₁ ⊢[ m ] [ L /[ m₀ ] length Δ₀ ] N ⦂ S
    ⊢N′
      rewrite sym eqΔ₀₁ = [/]-preserves-⊢⁰ Δ₀₁ ⊢S ⊢N
[/]-preserves-⊢⁰ Δ₀ (`↑[-⇒ _ ][ _ ] ⊢T) (`lift[-⇒-] ⊢M) = `lift[-⇒-] [/]-preserves-⊢⁰ Δ₀ ⊢T ⊢M
[/]-preserves-⊢⁰ {m} {T} {_} {m₀} {_} {`unlift[ m₁ ⇒ _ ] M} {L} Δ₀ ⊢T (Δ₀SΨ₀∤ ⊢`unlift[-⇒-] ⊢M ⦂ ⊢↑)
  with _ , (_ , _ , d) ∷ _ , refl , Δ₀∤ , d∤ ∷ Ψ₀∤ ← ∤-preserves-++ Δ₀ Δ₀SΨ₀∤
    with m₁ ≤?ₘ m₀
...    | yes _
      with false ← d = ∤-++⁺ Δ₀∤ Ψ₀∤ ⊢`unlift[-⇒-] subst-targetvar (length-respects-∤ Δ₀∤) M ([/]-preserves-⊢⁰ _ ⊢↑ ⊢M) ⦂ ⊢↑
...    | no  m₁≰
      with false ← d = ∤-++⁺ Δ₀∤ Ψ₀∤ ⊢`unlift[-⇒-] subst-targetvar (length-respects-∤ Δ₀∤) M ([/]-preserves-⊢⁰ _ ⊢↑ ⊢M) ⦂ ⊢↑
[/]-preserves-⊢⁰ {m} {`↓[ _ ⇒ _ ] T} {_} {m₀} {_} {`return[ m₁ ⇒ _ ] M} {L} Δ₀ (`↓[-⇒ _ ][ _ ] ⊢T) (Δ₀SΨ₀∤ ⊢`return[-⇒-] ⊢M)
  with _ , (_ , _ , d) ∷ _ , refl , Δ₀∤ , d∤ ∷ Ψ₀∤ ← ∤-preserves-++ Δ₀ Δ₀SΨ₀∤
    with m₁ ≤?ₘ m₀
...    | yes _
      with false ← d = ∤-++⁺ Δ₀∤ Ψ₀∤ ⊢`return[-⇒-] subst-targetvar (length-respects-∤ Δ₀∤) M ([/]-preserves-⊢⁰ _ ⊢T ⊢M)
...    | no  m₁≰
      with false ← d = ∤-++⁺ Δ₀∤ Ψ₀∤ ⊢`return[-⇒-] subst-targetvar (length-respects-∤ Δ₀∤) M ([/]-preserves-⊢⁰ _ ⊢T ⊢M)
[/]-preserves-⊢⁰ {m} {T} {_} {m₀} {_} {`let-return[ _ ⇒ m₁ ] M `in N} {L} Δ₀ ⊢T (Δ₀SΨ₀~ ⊢`let-return[-⇒-] ⊢M ⦂ ⊢↓ `in ⊢N)
  with `↓[-⇒_][_]_ {S = S} _ _ ⊢S ← ⊢↓
     | Δ₀₀ , Δ₀₁ , _ ∷ Ψ₀₀ , _ ∷ Ψ₀₁ , refl , refl , Δ₀~ , unusable ∷ Ψ₀~ ← ~⊞-preserves-++ Δ₀ Δ₀SΨ₀~
    with eqΔ₀₀ , eqΔ₀₁ ← length-respects-~⊞ Δ₀~ = (~⊞-++⁺ Δ₀~ Ψ₀~) ⊢`let-return[-⇒-] ⊢M′ ⦂ ⊢↓ `in ⊢N′
  where
    ⊢M′ : Δ₀₀ ++ Ψ₀₀ ⊢[ m ] [ L /[ m₀ ] length Δ₀ ] M ⦂ `↓[ m₁ ⇒ m ] S
    ⊢M′
      rewrite sym eqΔ₀₀ = [/]-preserves-⊢⁰ Δ₀₀ ⊢↓ ⊢M

    ⊢N′ : (S , m₁ , true) ∷ Δ₀₁ ++ Ψ₀₁ ⊢[ m ] [ wk L /[ m₀ ] suc (length Δ₀) ] N ⦂ T
    ⊢N′
      rewrite sym eqΔ₀₁ = [/]-preserves-⊢⁰ (_ ∷ Δ₀₁) ⊢T ⊢N
[/]-preserves-⊢⁰ Δ₀ ⊢T (`#_ {x = y} y∈)
  with y ℕ.≥? length Δ₀
...  | no  y≱ = `# <∧∈-++-++⇒∈-++ Δ₀ (_ ∷ []) y∈ (ℕ.≰⇒> y≱)
...  | yes y≥
    with y ℕ.≟ length Δ₀
...    | no  y≢   = `# ≥∧∈-++-++⇒∈-++ Δ₀ (_ ∷ []) y∈ (ℕ.≤-trans (ℕ.≤-reflexive (ℕ.+-comm _ 1)) (ℕ.≤∧≢⇒< y≥ (≢-sym y≢)))
...    | yes refl
      with _ , _ , _ , () ← len∈-inversion Δ₀ y∈

[/]-preserves-⊢¹ : ∀ Δ₀ →
                   Γ ~ Δ₀ ++ Ψ₀ ⊞ Γ₁ →
                   ⊢[ m₀ ] Γ₁ →
                   Γ₁ ⊢[ m₀ ] L ⦂ S →
                   ⊢[ m ] T ⦂⋆ →
                   Δ₀ ++ (S , m₀ , true) ∷ Ψ₀ ⊢[ m ] M ⦂ T →
                   --------------------------------------------
                   Γ ⊢[ m ] [ L /[ m₀ ] length Δ₀ ] M ⦂ T
[/]-preserves-⊢¹ Δ₀ Γ~ ⊢Γ₁ ⊢L ⊢T (`unit Δ₀eΨ₀Del)
  with Δ₀Del , weakening Wk∈m₀ ∷ Ψ₀Del ← All.++⁻ Δ₀ Δ₀eΨ₀Del = `unit (~⊞⁻¹-preserves-is-all-deletable (All.++⁺ Δ₀Del Ψ₀Del) (⊢∧Wk≤⇒is-all-deletable ⊢Γ₁ ℳ.≤-refl Wk∈m₀) Γ~)
[/]-preserves-⊢¹ Δ₀ Γ~ ⊢Γ₁ ⊢L (⊢T₀ `⊸[ _ ] ⊢T₁) (`λ⦂-∘ ⊢M) = `λ⦂-∘ ([/]-preserves-⊢¹ (_ ∷ Δ₀) (to-left ∷ Γ~) ((⊢T₀ , unusable) ∷ ⊢Γ₁) (wk[↑]-preserves-⊢ [] (unusable ∷ []) ⊢L) ⊢T₁ ⊢M)
[/]-preserves-⊢¹ {_} {_} {_} {m₀} {L} {_} {m} {T} {M `$ N} Δ₀ Γ~ ⊢Γ₁ ⊢L ⊢T (Δ₀SΨ₀~ ⊢ ⊢M ⦂ ⊢⊸ `$ ⊢N)
  with _`⊸[_]_ {S = T₀} ⊢T₀ _ _ ← ⊢⊸
     | Δ₀₀ , Δ₀₁ , _ ∷ Ψ₀₀ , _ ∷ Ψ₀₁ , refl , refl , Δ₀~ , d~ ∷ Ψ₀~ ← ~⊞-preserves-++ Δ₀ Δ₀SΨ₀~
    with d~
...    | contraction Co∈m₀
      with Γ₂′ , Γ₃′ , Γ₂′~ , Γ₃′~ , Γ~′ ← ~⊞-contraction-assoc Γ~ (~⊞-++⁺ Δ₀~ Ψ₀~) ⊢Γ₁ Co∈m₀ = Γ~′ ⊢ subst-targetvar (proj₁ (length-respects-~⊞ Δ₀~)) M ([/]-preserves-⊢¹ _ Γ₂′~ ⊢Γ₁ ⊢L ⊢⊸ ⊢M) ⦂ ⊢⊸ `$ subst-targetvar (proj₂ (length-respects-~⊞ Δ₀~)) N ([/]-preserves-⊢¹ _ Γ₃′~ ⊢Γ₁ ⊢L ⊢T₀ ⊢N)
...    | to-left
      with Γ₁′ , Γ₁′~ , Γ~′ ← ~⊞-assoc Γ~ (~⊞-swap (~⊞-++⁺ Δ₀~ Ψ₀~)) = ~⊞-swap Γ~′ ⊢ subst-targetvar (proj₁ (length-respects-~⊞ Δ₀~)) M ([/]-preserves-⊢¹ _ Γ₁′~ ⊢Γ₁ ⊢L ⊢⊸ ⊢M) ⦂ ⊢⊸ `$ subst-targetvar (proj₂ (length-respects-~⊞ Δ₀~)) N ([/]-preserves-⊢⁰ _ ⊢T₀ ⊢N)
...    | to-right
      with Γ₁′ , Γ₁′~ , Γ~′ ← ~⊞-assoc Γ~ (~⊞-++⁺ Δ₀~ Ψ₀~) = Γ~′ ⊢ subst-targetvar (proj₁ (length-respects-~⊞ Δ₀~)) M ([/]-preserves-⊢⁰ _ ⊢⊸ ⊢M) ⦂ ⊢⊸ `$ subst-targetvar (proj₂ (length-respects-~⊞ Δ₀~)) N ([/]-preserves-⊢¹ _ Γ₁′~ ⊢Γ₁ ⊢L ⊢T₀ ⊢N)
[/]-preserves-⊢¹ Δ₀ Γ~ ⊢Γ₁ ⊢L (`↑[-⇒ _ ][ _ ] ⊢T) (`lift[-⇒-] ⊢M) = `lift[-⇒-] [/]-preserves-⊢¹ Δ₀ Γ~ ⊢Γ₁ ⊢L ⊢T ⊢M
[/]-preserves-⊢¹ {_} {_} {_} {m₀} {L} {_} {m} {T} {`unlift[ m₁ ⇒ _ ] M} Δ₀ Γ~ ⊢Γ₁ ⊢L ⊢T (Δ₀SΨ₀∤ ⊢`unlift[-⇒-] ⊢M ⦂ ⊢↑)
  with Δ₀′ , _ ∷ Ψ₀′ , refl , Δ₀∤ , d∤ ∷ Ψ₀∤ ← ∤-preserves-++ Δ₀ Δ₀SΨ₀∤
    with d∤ | m₁ ≤?ₘ m₀
...    | delete m₁≰ _               | yes m₁≤ with () ← m₁≰ m₁≤
...    | keep _                     | yes m₁≤
      with Γ′ , Γ∤ , Γ′~ ← ~⊞⁻¹-preserves-∤ (∤-++⁺ Δ₀∤ Ψ₀∤) (⊢∧≤⇒∤ ⊢Γ₁ m₁≤) Γ~ = Γ∤ ⊢`unlift[-⇒-] (subst-targetvar (length-respects-∤ Δ₀∤) M ([/]-preserves-⊢¹ Δ₀′ Γ′~ ⊢Γ₁ ⊢L ⊢↑ ⊢M)) ⦂ ⊢↑
...    | delete _ (weakening Wk∈m₀) | no  m₁≰ = ⊢∧~⊞-is-all-deletable⇒⊢ (~⊞-swap Γ~) (⊢∧Wk≤⇒is-all-deletable ⊢Γ₁ ℳ.≤-refl Wk∈m₀) (∤-++⁺ Δ₀∤ Ψ₀∤ ⊢`unlift[-⇒-] (subst-targetvar (length-respects-∤ Δ₀∤) M ([/]-preserves-⊢⁰ Δ₀′ ⊢↑ ⊢M)) ⦂ ⊢↑)
...    | keep m₁≤                   | no  m₁≰ with () ← m₁≰ m₁≤
[/]-preserves-⊢¹ {_} {_} {_} {m₀} {L} {_} {m} {T} {`return[ m₁ ⇒ _ ] M} Δ₀ Γ~ ⊢Γ₁ ⊢L (`↓[-⇒ _ ][ _ ] ⊢T) (Δ₀SΨ₀∤ ⊢`return[-⇒-] ⊢M)
  with Δ₀′ , _ ∷ Ψ₀′ , refl , Δ₀∤ , d∤ ∷ Ψ₀∤ ← ∤-preserves-++ Δ₀ Δ₀SΨ₀∤
    with d∤ | m₁ ≤?ₘ m₀
...    | delete m₁≰ _               | yes m₁≤ with () ← m₁≰ m₁≤
...    | keep _                     | yes m₁≤
      with Γ′ , Γ∤ , Γ′~ ← ~⊞⁻¹-preserves-∤ (∤-++⁺ Δ₀∤ Ψ₀∤) (⊢∧≤⇒∤ ⊢Γ₁ m₁≤) Γ~ = Γ∤ ⊢`return[-⇒-] (subst-targetvar (length-respects-∤ Δ₀∤) M ([/]-preserves-⊢¹ Δ₀′ Γ′~ ⊢Γ₁ ⊢L ⊢T ⊢M))
...    | delete _ (weakening Wk∈m₀) | no  m₁≰ = ⊢∧~⊞-is-all-deletable⇒⊢ (~⊞-swap Γ~) (⊢∧Wk≤⇒is-all-deletable ⊢Γ₁ ℳ.≤-refl Wk∈m₀) (∤-++⁺ Δ₀∤ Ψ₀∤ ⊢`return[-⇒-] (subst-targetvar (length-respects-∤ Δ₀∤) M ([/]-preserves-⊢⁰ Δ₀′ ⊢T ⊢M)))
...    | keep m₁≤                   | no  m₁≰ with () ← m₁≰ m₁≤
[/]-preserves-⊢¹ {_} {_} {_} {m₀} {L} {_} {m} {T} {`let-return[ _ ⇒ _ ] M `in N} Δ₀ Γ~ ⊢Γ₁ ⊢L ⊢T (Δ₀SΨ₀~ ⊢`let-return[-⇒-] ⊢M ⦂ ⊢↓ `in ⊢N)
  with `↓[-⇒_][_]_ {S = T₀} _ _ ⊢T₀ ← ⊢↓
     | Δ₀₀ , Δ₀₁ , _ ∷ Ψ₀₀ , _ ∷ Ψ₀₁ , refl , refl , Δ₀~ , d~ ∷ Ψ₀~ ← ~⊞-preserves-++ Δ₀ Δ₀SΨ₀~
    with d~
...    | contraction Co∈m₀
      with Γ₂′ , Γ₃′ , Γ₂′~ , Γ₃′~ , Γ~′ ← ~⊞-contraction-assoc Γ~ (~⊞-++⁺ Δ₀~ Ψ₀~) ⊢Γ₁ Co∈m₀ = Γ~′ ⊢`let-return[-⇒-] subst-targetvar (proj₁ (length-respects-~⊞ Δ₀~)) M ([/]-preserves-⊢¹ _ Γ₂′~ ⊢Γ₁ ⊢L ⊢↓ ⊢M) ⦂ ⊢↓ `in subst-targetvar (cong suc (proj₂ (length-respects-~⊞ Δ₀~))) N ([/]-preserves-⊢¹ _ (to-left ∷ Γ₃′~) ((⊢T₀ , unusable) ∷ ⊢Γ₁) (wk[↑]-preserves-⊢ [] (unusable ∷ []) ⊢L) ⊢T ⊢N)
...    | to-left
      with Γ₁′ , Γ₁′~ , Γ~′ ← ~⊞-assoc Γ~ (~⊞-swap (~⊞-++⁺ Δ₀~ Ψ₀~)) = ~⊞-swap Γ~′ ⊢`let-return[-⇒-] subst-targetvar (proj₁ (length-respects-~⊞ Δ₀~)) M ([/]-preserves-⊢¹ _ Γ₁′~ ⊢Γ₁ ⊢L ⊢↓ ⊢M) ⦂ ⊢↓ `in subst-targetvar (cong suc (proj₂ (length-respects-~⊞ Δ₀~))) N ([/]-preserves-⊢⁰ _ ⊢T ⊢N)
...    | to-right
      with Γ₁′ , Γ₁′~ , Γ~′ ← ~⊞-assoc Γ~ (~⊞-++⁺ Δ₀~ Ψ₀~) = Γ~′ ⊢`let-return[-⇒-] subst-targetvar (proj₁ (length-respects-~⊞ Δ₀~)) M ([/]-preserves-⊢⁰ _ ⊢↓ ⊢M) ⦂ ⊢↓ `in subst-targetvar (cong suc (proj₂ (length-respects-~⊞ Δ₀~))) N ([/]-preserves-⊢¹ _ (to-left ∷ Γ₁′~) ((⊢T₀ , unusable) ∷ ⊢Γ₁) (wk[↑]-preserves-⊢ [] (unusable ∷ []) ⊢L) ⊢T ⊢N)
[/]-preserves-⊢¹ {Ψ₀ = Ψ₀} {m₀ = m₀} {S = S} Δ₀ Γ~ ⊢Γ₁ ⊢L ⊢T (`#_ {x = y} y∈)
  with y ℕ.≥? length Δ₀
...  | no  y≱
    with weakening Wk∈m₀ ∷ _ ← <∧∈-++⇒is-all-deletable Δ₀ y∈ (ℕ.≰⇒> y≱) = `# ⊢∧~⊞-is-all-deletable⇒⊢var (~⊞-swap Γ~) (⊢∧Wk≤⇒is-all-deletable ⊢Γ₁ ℳ.≤-refl Wk∈m₀) (<∧∈-++-++⇒∈-++ Δ₀ (_ ∷ []) y∈ (ℕ.≰⇒> y≱))
...  | yes y≥
    with y ℕ.≟ length Δ₀
...    | no  y≢
      rewrite sym (List.++-assoc Δ₀ ((S , m₀ , true) ∷ []) Ψ₀)
        with weakening Wk∈m₀ ∷ _ ← All.++⁻ʳ Δ₀ (≥∧∈-++⇒is-all-deletable (Δ₀ ++ _) y∈ (ℕ.≤-trans (ℕ.≤-reflexive (trans (List.length-++ Δ₀) (ℕ.+-comm _ 1))) (ℕ.≤∧≢⇒< y≥ (≢-sym y≢))))
          rewrite List.++-assoc Δ₀ ((S , m₀ , true) ∷ []) Ψ₀ = `# ⊢∧~⊞-is-all-deletable⇒⊢var (~⊞-swap Γ~) (⊢∧Wk≤⇒is-all-deletable ⊢Γ₁ ℳ.≤-refl Wk∈m₀) (≥∧∈-++-++⇒∈-++ Δ₀ (_ ∷ []) y∈ (ℕ.≤-trans (ℕ.≤-reflexive (ℕ.+-comm _ 1)) (ℕ.≤∧≢⇒< y≥ (≢-sym y≢))))
...    | yes refl
      with Δ₀Ψ₀Del , refl , refl , refl ← len∈-inversion Δ₀ y∈ = ⊢∧~⊞-is-all-deletable⇒⊢ Γ~ Δ₀Ψ₀Del ⊢L

preservation    : ⊢[ m ] Γ →
                  ⊢[ m ] S ⦂⋆ →
                  Γ ⊢[ m ] L ⦂ S →
                  L ⟶ L′ →
                  -----------------
                  Γ ⊢[ m ] L′ ⦂ S
preservation[≤] : ⊢[ m ] Γ →
                  ⊢[ m ] S ⦂⋆ →
                  Γ ⊢[ m ] L ⦂ S →
                  ¬ (m₀ ≤ₘ m) →
                  L ⟶[ m₀ ≤] L′ →
                  -----------------
                  Γ ⊢[ m ] L′ ⦂ S

preservation ⊢Γ ⊢S                     (Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)                                     ξ- L⟶ `$?                  = Γ~ ⊢ preservation (⊢∧-~⊞-⇒⊢₀ ⊢Γ Γ~) ⊢⊸ ⊢L L⟶ ⦂ ⊢⊸ `$ ⊢M
preservation ⊢Γ ⊢S                     (Γ~ ⊢ ⊢L ⦂ ⊢T `⊸[ m ] ⊢S′ `$ ⊢M)                         (ξ-! VL `$ M⟶)             = Γ~ ⊢ ⊢L ⦂ ⊢T `⊸[ m ] ⊢S′ `$ preservation (⊢∧-~⊞-⇒⊢₁ ⊢Γ Γ~) ⊢T ⊢M M⟶
preservation ⊢Γ ⊢S                     (Γ~ ⊢ `λ⦂-∘ ⊢L ⦂ ⊢⊸ `$ ⊢M)                               β-⊸                        = [/]-preserves-⊢¹ [] Γ~ (proj₂ (⊢∧-~⊞-⇒⊢ ⊢Γ Γ~)) ⊢M ⊢S ⊢L
preservation ⊢Γ (`↑[-⇒ <m ][ ↑∈m ] ⊢S) (`lift[-⇒-] ⊢L)                                          (ξ-`lift[-⇒-] L⟶[≤])       = `lift[-⇒-] preservation[≤] (⊢∧<ₘ⇒⊢ ⊢Γ <m) ⊢S ⊢L (ℳ.<⇒≱ <m) L⟶[≤]
preservation ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)                               (ξ-`unlift[-⇒-] L⟶)        = Γ∤ ⊢`unlift[-⇒-] preservation (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢↑ ⊢L L⟶ ⦂ ⊢↑
preservation ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] `lift[-⇒-] ⊢L ⦂ ⊢↑)                    (β-↑ WL)                   = ∤⁻¹-preserves-⊢ [] ⊢L Γ∤
preservation ⊢Γ (`↓[-⇒ m< ][ ↓∈m ] ⊢S) (Γ∤ ⊢`return[-⇒-] ⊢L)                                    (ξ-`return[-⇒-] L⟶)        = Γ∤ ⊢`return[-⇒-] preservation (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢S ⊢L L⟶
preservation ⊢Γ ⊢S                     (Γ~ ⊢`let-return[-⇒-] ⊢L ⦂ ⊢↓ `in ⊢M)                    ξ-`let-return[-⇒-] L⟶ `in- = Γ~ ⊢`let-return[-⇒-] preservation (⊢∧-~⊞-⇒⊢₀ ⊢Γ Γ~) ⊢↓ ⊢L L⟶ ⦂ ⊢↓ `in ⊢M
preservation ⊢Γ ⊢S                     (Γ~ ⊢`let-return[-⇒-] (Γ₀∤ ⊢`return[-⇒-] ⊢L) ⦂ ⊢↓ `in ⊢M) (β-↓ VL)
  with Γ₀₁ , Γ₀~ , Γ₀₁Del ← ∤⇒~⊞-is-deletable Γ₀∤
    with Γ″ , Γ″~ , Γ~′ ← ~⊞-assoc Γ~ Γ₀~ = [/]-preserves-⊢¹ [] (~⊞-swap Γ~′) (⊢∧∤⇒⊢ (⊢∧-~⊞-⇒⊢₀ ⊢Γ Γ~) Γ₀∤) ⊢L ⊢S (⊢∧~⊞-is-all-deletable⇒⊢ (to-right ∷ Γ″~) (unusable ∷ Γ₀₁Del) ⊢M)

preservation[≤] ⊢Γ ⊢S                     (Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)                  ≮m ξ- L⟶[≤] `$?                       = Γ~ ⊢ preservation[≤] (⊢∧-~⊞-⇒⊢₀ ⊢Γ Γ~) ⊢⊸ ⊢L ≮m L⟶[≤] ⦂ ⊢⊸ `$ ⊢M
preservation[≤] ⊢Γ ⊢S                     (Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)                  ≮m (ξ-! WL `$ M⟶[≤])
  with ⊢T `⊸[ m ] ⊢S′ ← ⊢⊸                                                                                            = Γ~ ⊢ ⊢L ⦂ ⊢T `⊸[ m ] ⊢S′ `$ preservation[≤] (⊢∧-~⊞-⇒⊢₁ ⊢Γ Γ~) ⊢T ⊢M ≮m M⟶[≤]
preservation[≤] ⊢Γ (`↑[-⇒ <m ][ ↑∈m ] ⊢S) (`lift[-⇒-] ⊢L)                       ≮m (ξ-`lift[-⇒-] L⟶[≤])               = `lift[-⇒-] preservation[≤] (⊢∧<ₘ⇒⊢ ⊢Γ <m) ⊢S ⊢L (λ m₁≤ → ≮m (ℳ.≤-trans m₁≤ (ℳ.<⇒≤ <m))) L⟶[≤] 
preservation[≤] ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)            ≮m (ξ-`unlift[≰ ≰m₀ ⇒-] L⟶[≤])        = Γ∤ ⊢`unlift[-⇒-] preservation[≤] (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢↑ ⊢L ≰m₀ L⟶[≤] ⦂ ⊢↑
preservation[≤] ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)            ≮m (ξ-`unlift[≤ ≤m₀ ⇒-] L⟶)           = Γ∤ ⊢`unlift[-⇒-] preservation (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢↑ ⊢L L⟶ ⦂ ⊢↑
preservation[≤] ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] `lift[-⇒-] ⊢L ⦂ ⊢↑) ≮m (β-↑ m₀≤ WL)                       = ∤⁻¹-preserves-⊢ [] ⊢L Γ∤
preservation[≤] ⊢Γ (`↓[-⇒ m< ][ ↓∈m ] ⊢S) (Γ∤ ⊢`return[-⇒-] ⊢L)                 ≮m (ξ-`return[≰ ≰m₀ ⇒-] L⟶[≤])        = Γ∤ ⊢`return[-⇒-] preservation[≤] (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢S ⊢L ≰m₀ L⟶[≤]
preservation[≤] ⊢Γ (`↓[-⇒ m< ][ ↓∈m ] ⊢S) (Γ∤ ⊢`return[-⇒-] ⊢L)                 ≮m (ξ-`return[≤ ≤m₀ ⇒-] L⟶)           = Γ∤ ⊢`return[-⇒-] preservation (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢S ⊢L L⟶
preservation[≤] ⊢Γ ⊢S                     (Γ~ ⊢`let-return[-⇒-] ⊢L ⦂ ⊢↓ `in ⊢M) ≮m ξ-`let-return[-⇒-] L⟶[≤] `in?      = Γ~ ⊢`let-return[-⇒-] preservation[≤] (⊢∧-~⊞-⇒⊢₀ ⊢Γ Γ~) ⊢↓ ⊢L ≮m L⟶[≤] ⦂ ⊢↓ `in ⊢M
preservation[≤] ⊢Γ ⊢S                     (Γ~ ⊢`let-return[-⇒-] ⊢L ⦂ ⊢↓ `in ⊢M) ≮m (ξ-`let-return[-⇒-]! WL `in M⟶[≤])
  with `↓[-⇒ m< ][ ↓∈m ] ⊢T ← ⊢↓                                                                                      = Γ~ ⊢`let-return[-⇒-] ⊢L ⦂ (`↓[-⇒ m< ][ ↓∈m ] ⊢T) `in preservation[≤] ((⊢T , valid (ℳ.<⇒≤ m<)) ∷ ⊢∧-~⊞-⇒⊢₁ ⊢Γ Γ~) ⊢S ⊢M ≮m M⟶[≤]
preservation[≤] ⊢Γ (⊢S `⊸[ ⊸∈m ] ⊢T)      (`λ⦂-∘ ⊢L)                            ≮m (ξ-`λ⦂[-]-∘ L⟶[≤])                 = `λ⦂-∘ preservation[≤] ((⊢S , valid ℳ.≤-refl) ∷ ⊢Γ) ⊢T ⊢L ≮m L⟶[≤]
