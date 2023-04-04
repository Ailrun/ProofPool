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
open import Data.Sum as ⊎ using (_⊎_; inj₁; inj₂)
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

subst-wk[-↑-] : x ≡ x′ →
                k ≡ k′ →
                ∀ L →
                Γ ⊢[ m ] wk[ x ↑ k ] L ⦂ S →
                -----------------------------
                Γ ⊢[ m ] wk[ x′ ↑ k′ ] L ⦂ S
subst-wk[-↑-] {Γ = Γ} {m} {S} eq₀ eq₁ L = subst₂ (λ x k → Γ ⊢[ m ] wk[ x ↑ k ] L ⦂ S) eq₀ eq₁

⊢wk[-↑-] : ∀ Δ →
           Ψ is-all-del →
           Δ ++ Γ ⊢[ m ] L ⦂ S →
           ---------------------------------------------------
           Δ ++ Ψ ++ Γ ⊢[ m ] wk[ length Ψ ↑ length Δ ] L ⦂ S
⊢wk[-↑-]                                         Δ ΨDel (`unit ΔΓDel)                           = `unit (All.++⁺ (All.++⁻ˡ Δ ΔΓDel) (All.++⁺ ΨDel (All.++⁻ʳ Δ ΔΓDel)))
⊢wk[-↑-]                                         Δ ΨDel (`λ⦂-∘ ⊢L)                              = `λ⦂-∘ ⊢wk[-↑-] (_ ∷ Δ) ΨDel ⊢L
⊢wk[-↑-] {Ψ} {L = L `$ M}                        Δ ΨDel (ΔΓ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)
  with Δ₀ , Δ₁ , Γ₀ , Γ₁ , refl , refl , Δ~ , Γ~ ← ~⊞-preserves-++ Δ ΔΓ~
     | Ψ₁ , Ψ~ ← left-bias-~⊞ Ψ
    with _    , Ψ₁Del ← ~⊞-preserves-is-all-del ΨDel Ψ~
       | eqΔ₀ , eqΔ₁ ← length-respects-~⊞ Δ~                                                    = ~⊞-++⁺ Δ~ (~⊞-++⁺ Ψ~ Γ~) ⊢ ⊢L′ ⦂ ⊢⊸ `$ ⊢M′
  where
    ⊢L′ =
      subst-wk[-↑-] refl eqΔ₀ L
        (⊢wk[-↑-] Δ₀ ΨDel ⊢L)
    ⊢M′ =
      subst-wk[-↑-] (proj₂ (length-respects-~⊞ Ψ~)) eqΔ₁ M
        (⊢wk[-↑-] Δ₁ Ψ₁Del ⊢M)

⊢wk[-↑-]                                         Δ ΨDel (`lift[-⇒-] ⊢L)                         = `lift[-⇒-] ⊢wk[-↑-] Δ ΨDel ⊢L
⊢wk[-↑-]     {L = `unlift[ m₀ ⇒ _ ] L}           Δ ΨDel (ΔΓ∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)
  with Δ′ , Γ′ , refl , Δ∤ , Γ∤ ← ∤-preserves-++ Δ ΔΓ∤
     | Ψ′ , Ψ∤ , _ ← is-all-del⇒∤ m₀ ΨDel                                                       = ∤-++⁺ Δ∤ (∤-++⁺ Ψ∤ Γ∤) ⊢`unlift[-⇒-] ⊢L′ ⦂ ⊢↑
  where
    ⊢L′ =
      subst-wk[-↑-] (length-respects-∤ Ψ∤) (length-respects-∤ Δ∤) L
        (⊢wk[-↑-] Δ′ (∤-preserves-is-all-del ΨDel Ψ∤) ⊢L)

⊢wk[-↑-]     {L = `return[ m₀ ⇒ _ ] L}           Δ ΨDel (ΔΓ∤ ⊢`return[-⇒-] ⊢L)
  with Δ′ , Γ′ , refl , Δ∤ , Γ∤ ← ∤-preserves-++ Δ ΔΓ∤
     | Ψ′ , Ψ∤ , _ ← is-all-del⇒∤ m₀ ΨDel                                                       = ∤-++⁺ Δ∤ (∤-++⁺ Ψ∤ Γ∤) ⊢`return[-⇒-] ⊢L′
  where
    ⊢L′ =
      subst-wk[-↑-] (length-respects-∤ Ψ∤) (length-respects-∤ Δ∤) L
        (⊢wk[-↑-] Δ′ (∤-preserves-is-all-del ΨDel Ψ∤) ⊢L)

⊢wk[-↑-] {Ψ} {L = `let-return[ _ ⇒ m₀ ] L `in M} Δ ΨDel (ΔΓ~ ⊢`let-return[-⇒-] ⊢L ⦂ ⊢↓ `in ⊢M)
  with Δ₀ , Δ₁ , Γ₀ , Γ₁ , refl , refl , Δ~ , Γ~ ← ~⊞-preserves-++ Δ ΔΓ~
     | Ψ₁ , Ψ~ ← left-bias-~⊞ Ψ
    with _    , Ψ₁Del ← ~⊞-preserves-is-all-del ΨDel Ψ~
       | eqΔ₀ , eqΔ₁ ← length-respects-~⊞ Δ~                                                    = ~⊞-++⁺ Δ~ (~⊞-++⁺ Ψ~ Γ~) ⊢`let-return[-⇒-] ⊢L′ ⦂ ⊢↓ `in ⊢M′
  where
    ⊢L′ =
      subst-wk[-↑-] refl eqΔ₀ L
        (⊢wk[-↑-] Δ₀ ΨDel ⊢L)
    ⊢M′ =
      subst-wk[-↑-] (proj₂ (length-respects-~⊞ Ψ~)) (cong suc eqΔ₁) M
        (⊢wk[-↑-] (_ ∷ Δ₁) Ψ₁Del ⊢M)

⊢wk[-↑-]                                         Δ ΨDel (`#_ {x = y} y∈)
  with y ℕ.≥? length Δ
...  | yes y≥                                                                                   = `# ≥∧∈-++⇒+-∈-++-++ Δ ΨDel y∈ y≥
...  | no  y≱                                                                                   = `# <∧∈-++⇒∈-++-++ Δ ΨDel y∈ (ℕ.≰⇒> y≱)

~⊞-is-all-del∧∈⇒∈ : Γ ~ Γ₀ ⊞ Γ₁ →
                    Γ₀ is-all-del →
                    x ⦂[ m ] S ∈ Γ₁ →
                    ----------------------
                    x ⦂[ m ] S ∈ Γ
~⊞-is-all-del∧∈⇒∈ (contraction Co∈m ∷ Γ~) (d₀Del ∷ Γ₀Del) (here Γ₁Del)     = here (~⊞⁻¹-preserves-is-all-del Γ₀Del Γ₁Del Γ~)
~⊞-is-all-del∧∈⇒∈ (to-right         ∷ Γ~) (d₀Del ∷ Γ₀Del) (here Γ₁Del)     = here (~⊞⁻¹-preserves-is-all-del Γ₀Del Γ₁Del Γ~)
~⊞-is-all-del∧∈⇒∈ (d~               ∷ Γ~) (d₀Del ∷ Γ₀Del) (there d₁Del x∈) = there (~d⊞⁻¹-preserves-is-del d₀Del d₁Del d~) (~⊞-is-all-del∧∈⇒∈ Γ~ Γ₀Del x∈)

~⊞-is-all-del∧⊢⇒⊢ : Γ ~ Γ₀ ⊞ Γ₁ →
                    Γ₀ is-all-del →
                    Γ₁ ⊢[ m ] L ⦂ S →
                    ----------------------
                    Γ ⊢[ m ] L ⦂ S
~⊞-is-all-del∧⊢⇒⊢                           Γ~ Γ₀Del (`unit Γ₁Del)                          = `unit ΓDel
  where
    ΓDel = ~⊞⁻¹-preserves-is-all-del Γ₀Del Γ₁Del Γ~

~⊞-is-all-del∧⊢⇒⊢                           Γ~ Γ₀Del (`λ⦂-∘ ⊢L)                             = `λ⦂-∘ ⊢L′
  where
    ⊢L′ = ~⊞-is-all-del∧⊢⇒⊢ (to-right ∷ Γ~) (unusable ∷ Γ₀Del) ⊢L

~⊞-is-all-del∧⊢⇒⊢                           Γ~ Γ₀Del (Γ₁~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)
  with _ , Γ₁′~ , Γ~′ ← ~⊞-assoc (~⊞-swap Γ~) (~⊞-swap Γ₁~)                                 = ~⊞-swap Γ~′ ⊢ ⊢L′ ⦂ ⊢⊸ `$ ⊢M
  where
    ⊢L′ = ~⊞-is-all-del∧⊢⇒⊢ (~⊞-swap Γ₁′~) Γ₀Del ⊢L

~⊞-is-all-del∧⊢⇒⊢                           Γ~ Γ₀Del (`lift[-⇒-] ⊢L)                        = `lift[-⇒-] ⊢L′
  where
    ⊢L′ = ~⊞-is-all-del∧⊢⇒⊢ Γ~ Γ₀Del ⊢L

~⊞-is-all-del∧⊢⇒⊢ {L = `unlift[ m₀ ⇒ _ ] L} Γ~ Γ₀Del (Γ₁∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)
  with _ , Γ₀∤ , Γ₀′Del ← is-all-del⇒∤ m₀ Γ₀Del
    with _ , Γ∤ , Γ′~ ← ~⊞⁻¹-preserves-∤ Γ₀∤ Γ₁∤ Γ~                                         = Γ∤ ⊢`unlift[-⇒-] ⊢L′ ⦂ ⊢↑
  where
    ⊢L′ = ~⊞-is-all-del∧⊢⇒⊢ Γ′~ Γ₀′Del ⊢L

~⊞-is-all-del∧⊢⇒⊢ {L = `return[ m₀ ⇒ _ ] L} Γ~ Γ₀Del (Γ₁∤ ⊢`return[-⇒-] ⊢L)
  with _ , Γ₀∤ , Γ₀′Del ← is-all-del⇒∤ m₀ Γ₀Del
    with _ , Γ∤ , Γ′~ ← ~⊞⁻¹-preserves-∤ Γ₀∤ Γ₁∤ Γ~                                         = Γ∤ ⊢`return[-⇒-] ⊢L′
  where
    ⊢L′ = ~⊞-is-all-del∧⊢⇒⊢ Γ′~ Γ₀′Del ⊢L

~⊞-is-all-del∧⊢⇒⊢                           Γ~ Γ₀Del (Γ₁~ ⊢`let-return[-⇒-] ⊢L ⦂ ⊢↓ `in ⊢M)
  with _ , Γ₁′~ , Γ~′ ← ~⊞-assoc (~⊞-swap Γ~) (~⊞-swap Γ₁~)                                 = ~⊞-swap Γ~′ ⊢`let-return[-⇒-] ⊢L′ ⦂ ⊢↓ `in ⊢M
  where
    ⊢L′ = ~⊞-is-all-del∧⊢⇒⊢ (~⊞-swap Γ₁′~) Γ₀Del ⊢L

~⊞-is-all-del∧⊢⇒⊢                           Γ~ Γ₀Del (`# x∈)                                = `# x∈′
  where
    x∈′ = ~⊞-is-all-del∧∈⇒∈ Γ~ Γ₀Del x∈

subst-[/-] : x ≡ x′ →
             ∀ M →
             Γ ⊢[ m ] [ L /[ m₀ ] x ] M ⦂ T →
             Γ ⊢[ m ] [ L /[ m₀ ] x′ ] M ⦂ T
subst-[/-] {Γ = Γ} {m} {L} {m₀} {T} eq M = subst (λ x → Γ ⊢[ m ] [ L /[ m₀ ] x ] M ⦂ T) eq

false⊢[/] : ∀ Δ₀ →
            ⊢[ m ] T ⦂⋆ →
            Δ₀ ++ (S , m₀ , false) ∷ Ψ₀ ⊢[ m ] M ⦂ T →
            ----------------------------------------------
            Δ₀ ++ Ψ₀ ⊢[ m ] [ L /[ m₀ ] length Δ₀ ] M ⦂ T
false⊢[/]                                              Δ₀ ⊢T                  (`unit Δ₀eΨ₀Del)
  with Δ₀Del , _ ∷ Ψ₀Del ← All.++⁻ Δ₀ Δ₀eΨ₀Del = `unit (All.++⁺ Δ₀Del Ψ₀Del)
false⊢[/]                                              Δ₀ (⊢T₀ `⊸[ _ ] ⊢T₁)   (`λ⦂-∘ ⊢M)                                = `λ⦂-∘ ⊢M′
  where
    ⊢M′ = false⊢[/] (_ ∷ Δ₀) ⊢T₁ ⊢M

false⊢[/]           {M = M `$ N}                       Δ₀ ⊢T                  (Δ₀dΨ₀~ ⊢ ⊢M ⦂ ⊢⊸ `$ ⊢N)
  with ⊢S `⊸[ _ ] _ ← ⊢⊸
     | Δ₀₀ , Δ₀₁ , _ ∷ Ψ₀₀ , _ ∷ Ψ₀₁ , refl , refl , Δ₀~ , unusable ∷ Ψ₀~ ← ~⊞-preserves-++ Δ₀ Δ₀dΨ₀~
    with eqΔ₀₀ , eqΔ₀₁ ← length-respects-~⊞ Δ₀~                                                                         = ~⊞-++⁺ Δ₀~ Ψ₀~ ⊢ ⊢M′ ⦂ ⊢⊸ `$ ⊢N′
  where
    ⊢M′ = subst-[/-] eqΔ₀₀ M (false⊢[/] Δ₀₀ ⊢⊸ ⊢M)
    ⊢N′ = subst-[/-] eqΔ₀₁ N (false⊢[/] Δ₀₁ ⊢S ⊢N)

false⊢[/]                                              Δ₀ (`↑[-⇒ _ ][ _ ] ⊢T) (`lift[-⇒-] ⊢M)                           = `lift[-⇒-] false⊢[/] Δ₀ ⊢T ⊢M
false⊢[/] {m₀ = m₀} {M = `unlift[ m₁ ⇒ m ] M}          Δ₀ ⊢T                  (Δ₀dΨ₀∤ ⊢`unlift[-⇒-] ⊢M ⦂ ⊢↑)
  with _ , (_ , _ , d) ∷ _ , refl , Δ₀∤ , d∤ ∷ Ψ₀∤ ← ∤-preserves-++ Δ₀ Δ₀dΨ₀∤
    with m₁ ≤?ₘ m₀ | d
...    | yes _     | false
      with ⊢M′ ← subst-[/-] (length-respects-∤ Δ₀∤) M (false⊢[/] _ ⊢↑ ⊢M)                                               = ∤-++⁺ Δ₀∤ Ψ₀∤ ⊢`unlift[-⇒-] ⊢M′ ⦂ ⊢↑
...    | no  m₁≰   | false
      with ⊢M′ ← subst-[/-] (length-respects-∤ Δ₀∤) M (false⊢[/] _ ⊢↑ ⊢M)                                               = ∤-++⁺ Δ₀∤ Ψ₀∤ ⊢`unlift[-⇒-] ⊢M′ ⦂ ⊢↑

false⊢[/] {m₀ = m₀} {M = `return[ m₁ ⇒ m ] M}          Δ₀ (`↓[-⇒ _ ][ _ ] ⊢T) (Δ₀dΨ₀∤ ⊢`return[-⇒-] ⊢M)
  with _ , (_ , _ , d) ∷ _ , refl , Δ₀∤ , d∤ ∷ Ψ₀∤ ← ∤-preserves-++ Δ₀ Δ₀dΨ₀∤
    with m₁ ≤?ₘ m₀ | d
...    | yes _     | false
      with ⊢M′ ← subst-[/-] (length-respects-∤ Δ₀∤) M (false⊢[/] _ ⊢T ⊢M)                                               = ∤-++⁺ Δ₀∤ Ψ₀∤ ⊢`return[-⇒-] ⊢M′
...    | no  m₁≰   | false
      with ⊢M′ ← subst-[/-] (length-respects-∤ Δ₀∤) M (false⊢[/] _ ⊢T ⊢M)                                               = ∤-++⁺ Δ₀∤ Ψ₀∤ ⊢`return[-⇒-] ⊢M′

false⊢[/]           {M = `let-return[ _ ⇒ _ ] M `in N} Δ₀ ⊢T                  (Δ₀dΨ₀~ ⊢`let-return[-⇒-] ⊢M ⦂ ⊢↓ `in ⊢N)
  with Δ₀₀ , Δ₀₁ , _ ∷ Ψ₀₀ , _ ∷ Ψ₀₁ , refl , refl , Δ₀~ , unusable ∷ Ψ₀~ ← ~⊞-preserves-++ Δ₀ Δ₀dΨ₀~
    with eqΔ₀₀ , eqΔ₀₁ ← length-respects-~⊞ Δ₀~                                                                         = (~⊞-++⁺ Δ₀~ Ψ₀~) ⊢`let-return[-⇒-] ⊢M′ ⦂ ⊢↓ `in ⊢N′
  where
    ⊢M′ = subst-[/-] eqΔ₀₀ M (false⊢[/] Δ₀₀ ⊢↓ ⊢M)
    ⊢N′ = subst-[/-] (cong suc eqΔ₀₁) N (false⊢[/] (_ ∷ Δ₀₁) ⊢T ⊢N)

false⊢[/]                                              Δ₀ ⊢T                  (`#_ {x = y} y∈)
  with y ℕ.≥? length Δ₀
...  | no  y≱
    with y∈′ ← <∧∈-++-++⇒∈-++ Δ₀ (_ ∷ []) y∈ (ℕ.≰⇒> y≱)                                                                 = `# y∈′
...  | yes y≥
    with y ℕ.≟ length Δ₀
...    | no  y≢
    with y∈′ ← ≥∧∈-++-++⇒∈-++ Δ₀ (_ ∷ []) y∈ (ℕ.≤-trans (ℕ.≤-reflexive (ℕ.+-comm _ 1)) (ℕ.≤∧≢⇒< y≥ (≢-sym y≢)))         = `# y∈′
...    | yes refl with _ , _ , _ , () ← len∈-inversion Δ₀ y∈

true⊢[/] : ∀ Δ₀ →
           Γ ~ Δ₀ ++ Ψ₀ ⊞ Γ₁ →
           ⊢[ m₀ ] Γ₁ →
           Γ₁ ⊢[ m₀ ] L ⦂ S →
           ⊢[ m ] T ⦂⋆ →
           Δ₀ ++ (S , m₀ , true) ∷ Ψ₀ ⊢[ m ] M ⦂ T →
           --------------------------------------------
           Γ ⊢[ m ] [ L /[ m₀ ] length Δ₀ ] M ⦂ T
true⊢[/]                                              Δ₀ Γ~ ⊢Γ₁ ⊢L ⊢T (`unit Δ₀eΨ₀Del)
  with Δ₀Del , weakening Wk∈m₀ ∷ Ψ₀Del ← All.++⁻ Δ₀ Δ₀eΨ₀Del                                                                     = `unit (~⊞⁻¹-preserves-is-all-del (All.++⁺ Δ₀Del Ψ₀Del) (⊢∧Wk≤⇒is-all-del ⊢Γ₁ ℳ.≤-refl Wk∈m₀) Γ~)
true⊢[/]                                              Δ₀ Γ~ ⊢Γ₁ ⊢L (⊢T₀ `⊸[ _ ] ⊢T₁) (`λ⦂-∘ ⊢M)                                  = `λ⦂-∘ (true⊢[/] (_ ∷ Δ₀) (to-left ∷ Γ~) ((⊢T₀ , unusable) ∷ ⊢Γ₁) (⊢wk[-↑-] [] (unusable ∷ []) ⊢L) ⊢T₁ ⊢M)
true⊢[/]           {M = M `$ N}                       Δ₀ Γ~ ⊢Γ₁ ⊢L ⊢T (Δ₀dΨ₀~ ⊢ ⊢M ⦂ ⊢⊸ `$ ⊢N)
  with ⊢T₀ `⊸[ _ ] _ ← ⊢⊸
     | _ , _ , _ , _ , refl , refl , Δ₀~ , d~ ∷ Ψ₀~ ← ~⊞-preserves-++ Δ₀ Δ₀dΨ₀~
    with eqΔ₀₀ , eqΔ₀₁ ← length-respects-~⊞ Δ₀~
      with d~
...      | contraction Co∈m₀
        with _ , _ , Γ₂′~ , Γ₃′~ , Γ~′ ← ~⊞-contraction-assoc Γ~ (~⊞-++⁺ Δ₀~ Ψ₀~) ⊢Γ₁ Co∈m₀
          with ⊢M′ ← subst-[/-] eqΔ₀₀ M (true⊢[/] _ Γ₂′~ ⊢Γ₁ ⊢L ⊢⊸ ⊢M)
             | ⊢N′ ← subst-[/-] eqΔ₀₁ N (true⊢[/] _ Γ₃′~ ⊢Γ₁ ⊢L ⊢T₀ ⊢N)                                                          = Γ~′ ⊢ ⊢M′ ⦂ ⊢⊸ `$ ⊢N′
...      | to-left
        with _ , Γ₁′~ , Γ~′ ← ~⊞-assoc Γ~ (~⊞-swap (~⊞-++⁺ Δ₀~ Ψ₀~))
          with ⊢M′ ← subst-[/-] eqΔ₀₀ M (true⊢[/] _ Γ₁′~ ⊢Γ₁ ⊢L ⊢⊸ ⊢M)
             | ⊢N′ ← subst-[/-] eqΔ₀₁ N (false⊢[/] _ ⊢T₀ ⊢N)                                                                     = ~⊞-swap Γ~′ ⊢ ⊢M′ ⦂ ⊢⊸ `$ ⊢N′
...      | to-right
        with _ , Γ₁′~ , Γ~′ ← ~⊞-assoc Γ~ (~⊞-++⁺ Δ₀~ Ψ₀~)
          with ⊢M′ ← subst-[/-] eqΔ₀₀ M (false⊢[/] _ ⊢⊸ ⊢M)
             | ⊢N′ ← subst-[/-] eqΔ₀₁ N (true⊢[/] _ Γ₁′~ ⊢Γ₁ ⊢L ⊢T₀ ⊢N)                                                          = Γ~′ ⊢ ⊢M′ ⦂ ⊢⊸ `$ ⊢N′

true⊢[/]                                              Δ₀ Γ~ ⊢Γ₁ ⊢L (`↑[-⇒ _ ][ _ ] ⊢T) (`lift[-⇒-] ⊢M)                           = `lift[-⇒-] true⊢[/] Δ₀ Γ~ ⊢Γ₁ ⊢L ⊢T ⊢M
true⊢[/] {m₀ = m₀} {M = `unlift[ m₁ ⇒ _ ] M}          Δ₀ Γ~ ⊢Γ₁ ⊢L ⊢T                  (Δ₀dΨ₀∤ ⊢`unlift[-⇒-] ⊢M ⦂ ⊢↑)
  with _ , _ , refl , Δ₀∤ , d∤ ∷ Ψ₀∤ ← ∤-preserves-++ Δ₀ Δ₀dΨ₀∤
    with d∤                         | m₁ ≤?ₘ m₀
...    | delete m₁≰ _               | yes m₁≤ with () ← m₁≰ m₁≤
...    | keep _                     | yes m₁≤
      with _ , Γ∤ , Γ′~ ← ~⊞⁻¹-preserves-∤ (∤-++⁺ Δ₀∤ Ψ₀∤) (⊢∧≤⇒∤ ⊢Γ₁ m₁≤) Γ~
        with ⊢M′ ← subst-[/-] (length-respects-∤ Δ₀∤) M (true⊢[/] _ Γ′~ ⊢Γ₁ ⊢L ⊢↑ ⊢M)                                            = Γ∤ ⊢`unlift[-⇒-] ⊢M′ ⦂ ⊢↑
...    | delete _ (weakening Wk∈m₀) | no  m₁≰
      with Γ₁Del ← ⊢∧Wk≤⇒is-all-del ⊢Γ₁ ℳ.≤-refl Wk∈m₀
         | ⊢M′ ← subst-[/-] (length-respects-∤ Δ₀∤) M (false⊢[/] _ ⊢↑ ⊢M)                                                        = ~⊞-is-all-del∧⊢⇒⊢ (~⊞-swap Γ~) Γ₁Del (∤-++⁺ Δ₀∤ Ψ₀∤ ⊢`unlift[-⇒-] ⊢M′ ⦂ ⊢↑)
...    | keep m₁≤                   | no  m₁≰ with () ← m₁≰ m₁≤

true⊢[/] {m₀ = m₀} {M = `return[ m₁ ⇒ _ ] M}          Δ₀ Γ~ ⊢Γ₁ ⊢L (`↓[-⇒ _ ][ _ ] ⊢T) (Δ₀dΨ₀∤ ⊢`return[-⇒-] ⊢M)
  with _ , _ , refl , Δ₀∤ , d∤ ∷ Ψ₀∤ ← ∤-preserves-++ Δ₀ Δ₀dΨ₀∤
    with d∤ | m₁ ≤?ₘ m₀
...    | delete m₁≰ _               | yes m₁≤ with () ← m₁≰ m₁≤
...    | keep _                     | yes m₁≤
      with _ , Γ∤ , Γ′~ ← ~⊞⁻¹-preserves-∤ (∤-++⁺ Δ₀∤ Ψ₀∤) (⊢∧≤⇒∤ ⊢Γ₁ m₁≤) Γ~
        with ⊢M′ ← subst-[/-] (length-respects-∤ Δ₀∤) M (true⊢[/] _ Γ′~ ⊢Γ₁ ⊢L ⊢T ⊢M)                                            = Γ∤ ⊢`return[-⇒-] ⊢M′
...    | delete _ (weakening Wk∈m₀) | no  m₁≰
      with Γ₁Del ← ⊢∧Wk≤⇒is-all-del ⊢Γ₁ ℳ.≤-refl Wk∈m₀
         | ⊢M′ ← subst-[/-] (length-respects-∤ Δ₀∤) M (false⊢[/] _ ⊢T ⊢M)                                                        = ~⊞-is-all-del∧⊢⇒⊢ (~⊞-swap Γ~) Γ₁Del (∤-++⁺ Δ₀∤ Ψ₀∤ ⊢`return[-⇒-] ⊢M′)
...    | keep m₁≤                   | no  m₁≰ with () ← m₁≰ m₁≤

true⊢[/]           {M = `let-return[ _ ⇒ _ ] M `in N} Δ₀ Γ~ ⊢Γ₁ ⊢L ⊢T                  (Δ₀dΨ₀~ ⊢`let-return[-⇒-] ⊢M ⦂ ⊢↓ `in ⊢N)
  with `↓[-⇒ _ ][ _ ] ⊢T₀ ← ⊢↓
     | _ , _ , _ , _ , refl , refl , Δ₀~ , d~ ∷ Ψ₀~ ← ~⊞-preserves-++ Δ₀ Δ₀dΨ₀~
    with eqΔ₀₀ , eqΔ₀₁ ← length-respects-~⊞ Δ₀~
      with d~
...      | contraction Co∈m₀
        with _ , _ , Γ₂′~ , Γ₃′~ , Γ~′ ← ~⊞-contraction-assoc Γ~ (~⊞-++⁺ Δ₀~ Ψ₀~) ⊢Γ₁ Co∈m₀
          with ⊢M′ ← subst-[/-] eqΔ₀₀ M (true⊢[/] _ Γ₂′~ ⊢Γ₁ ⊢L ⊢↓ ⊢M)
             | ⊢N′ ← true⊢[/] _ (to-left ∷ Γ₃′~) ((⊢T₀ , unusable) ∷ ⊢Γ₁) (⊢wk[-↑-] [] (unusable ∷ []) ⊢L) ⊢T ⊢N
            with ⊢N″ ← subst-[/-] (cong suc eqΔ₀₁) N ⊢N′                                                                         = Γ~′ ⊢`let-return[-⇒-] ⊢M′ ⦂ ⊢↓ `in ⊢N″
...      | to-left
        with Γ₁′ , Γ₁′~ , Γ~′ ← ~⊞-assoc Γ~ (~⊞-swap (~⊞-++⁺ Δ₀~ Ψ₀~))
          with ⊢M′ ← subst-[/-] eqΔ₀₀ M (true⊢[/] _ Γ₁′~ ⊢Γ₁ ⊢L ⊢↓ ⊢M)
             | ⊢N′ ← subst-[/-] (cong suc eqΔ₀₁) N (false⊢[/] _ ⊢T ⊢N)                                                           = ~⊞-swap Γ~′ ⊢`let-return[-⇒-] ⊢M′ ⦂ ⊢↓ `in ⊢N′
...      | to-right
        with Γ₁′ , Γ₁′~ , Γ~′ ← ~⊞-assoc Γ~ (~⊞-++⁺ Δ₀~ Ψ₀~)
          with ⊢M′ ← subst-[/-] eqΔ₀₀ M (false⊢[/] _ ⊢↓ ⊢M)
             | ⊢N′ ← true⊢[/] _ (to-left ∷ Γ₁′~) ((⊢T₀ , unusable) ∷ ⊢Γ₁) (⊢wk[-↑-] [] (unusable ∷ []) ⊢L) ⊢T ⊢N
            with ⊢N″ ← subst-[/-] (cong suc eqΔ₀₁) N ⊢N′                                                                         = Γ~′ ⊢`let-return[-⇒-] ⊢M′ ⦂ ⊢↓ `in ⊢N″

true⊢[/]                                              Δ₀ Γ~ ⊢Γ₁ ⊢L ⊢T                  (`#_ {x = y} y∈)
  with y ℕ.≥? length Δ₀
...  | no  y≱
    with weakening Wk∈m₀ ∷ _ ← <∧∈-++⇒is-all-del Δ₀ y∈ (ℕ.≰⇒> y≱)
      with y∈′ ← ~⊞-is-all-del∧∈⇒∈ (~⊞-swap Γ~) (⊢∧Wk≤⇒is-all-del ⊢Γ₁ ℳ.≤-refl Wk∈m₀) (<∧∈-++-++⇒∈-++ Δ₀ (_ ∷ []) y∈ (ℕ.≰⇒> y≱)) = `# y∈′
...  | yes y≥
    with y ℕ.≟ length Δ₀
...    | no  y≢
      with y∈′ ← subst (_ ⦂[ _ ] _ ∈_) (sym (List.++-assoc Δ₀ (_ ∷ []) _)) y∈
         | y> ← subst (y ℕ.≥_) (ℕ.+-comm 1 _) (ℕ.≤∧≢⇒< y≥ (≢-sym y≢))
        with y∈″ ← ≥∧∈-++-++⇒∈-++ Δ₀ (_ ∷ []) y∈ y>
           | Δ₀dDel ← ≥∧∈-++⇒is-all-del _ y∈′ (subst (y ℕ.≥_) (sym (List.length-++ Δ₀)) y>)
          with weakening Wk∈m₀ ∷ _ ← All.++⁻ʳ Δ₀ Δ₀dDel
            with y∈‴ ← ~⊞-is-all-del∧∈⇒∈ (~⊞-swap Γ~) (⊢∧Wk≤⇒is-all-del ⊢Γ₁ ℳ.≤-refl Wk∈m₀) y∈″                                  = `# y∈‴
...    | yes refl
      with Δ₀Ψ₀Del , refl , refl , refl ← len∈-inversion Δ₀ y∈                                                                   = ~⊞-is-all-del∧⊢⇒⊢ Γ~ Δ₀Ψ₀Del ⊢L

preservation    : ⊢[ m ] Γ →
                  ⊢[ m ] S ⦂⋆ →
                  Γ ⊢[ m ] L ⦂ S →
                  L ⟶ L′ →
                  -----------------
                  Γ ⊢[ m ] L′ ⦂ S
preservation[≤] : ⊢[ m ] Γ →
                  ⊢[ m ] S ⦂⋆ →
                  Γ ⊢[ m ] L ⦂ S →
                  L ⟶[ m₀ ≤] L′ →
                  -----------------
                  Γ ⊢[ m ] L′ ⦂ S

preservation ⊢Γ ⊢S                     (Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)                                      ξ- L⟶ `$?                  = Γ~ ⊢ preservation (⊢∧-~⊞-⇒⊢₀ ⊢Γ Γ~) ⊢⊸ ⊢L L⟶ ⦂ ⊢⊸ `$ ⊢M
preservation ⊢Γ ⊢S                     (Γ~ ⊢ ⊢L ⦂ ⊢T `⊸[ m ] ⊢S′ `$ ⊢M)                          (ξ-! VL `$ M⟶)             = Γ~ ⊢ ⊢L ⦂ ⊢T `⊸[ m ] ⊢S′ `$ preservation (⊢∧-~⊞-⇒⊢₁ ⊢Γ Γ~) ⊢T ⊢M M⟶
preservation ⊢Γ ⊢S                     (Γ~ ⊢ `λ⦂-∘ ⊢L ⦂ ⊢⊸ `$ ⊢M)                                β-⊸                        = true⊢[/] [] Γ~ (proj₂ (⊢∧-~⊞-⇒⊢ ⊢Γ Γ~)) ⊢M ⊢S ⊢L
preservation ⊢Γ (`↑[-⇒ <m ][ ↑∈m ] ⊢S) (`lift[-⇒-] ⊢L)                                           (ξ-`lift[-⇒-] L⟶[≤])       = `lift[-⇒-] preservation[≤] (⊢∧<ₘ⇒⊢ ⊢Γ <m) ⊢S ⊢L L⟶[≤]
preservation ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)                                (ξ-`unlift[-⇒-] L⟶)        = Γ∤ ⊢`unlift[-⇒-] preservation (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢↑ ⊢L L⟶ ⦂ ⊢↑
preservation ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] `lift[-⇒-] ⊢L ⦂ ⊢↑)                     (β-↑ WL)                   = ∤⁻¹-preserves-⊢ [] ⊢L Γ∤
preservation ⊢Γ (`↓[-⇒ m< ][ ↓∈m ] ⊢S) (Γ∤ ⊢`return[-⇒-] ⊢L)                                     (ξ-`return[-⇒-] L⟶)        = Γ∤ ⊢`return[-⇒-] preservation (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢S ⊢L L⟶
preservation ⊢Γ ⊢S                     (Γ~ ⊢`let-return[-⇒-] ⊢L ⦂ ⊢↓ `in ⊢M)                     ξ-`let-return[-⇒-] L⟶ `in- = Γ~ ⊢`let-return[-⇒-] preservation (⊢∧-~⊞-⇒⊢₀ ⊢Γ Γ~) ⊢↓ ⊢L L⟶ ⦂ ⊢↓ `in ⊢M
preservation ⊢Γ ⊢S                     (Γ~ ⊢`let-return[-⇒-] (Γ₀∤ ⊢`return[-⇒-] ⊢L) ⦂ ⊢↓ `in ⊢M) (β-↓ VL)
  with Γ₀₁ , Γ₀~ , Γ₀₁Del ← ∤⇒~⊞-is-del Γ₀∤
    with Γ″ , Γ″~ , Γ~′ ← ~⊞-assoc Γ~ Γ₀~                                                                                   = true⊢[/] [] (~⊞-swap Γ~′) (⊢∧∤⇒⊢ (⊢∧-~⊞-⇒⊢₀ ⊢Γ Γ~) Γ₀∤) ⊢L ⊢S (~⊞-is-all-del∧⊢⇒⊢ (to-right ∷ Γ″~) (unusable ∷ Γ₀₁Del) ⊢M)

preservation[≤] ⊢Γ ⊢S                     (Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)                  ξ- L⟶[≤] `$?                       = Γ~ ⊢ preservation[≤] (⊢∧-~⊞-⇒⊢₀ ⊢Γ Γ~) ⊢⊸ ⊢L L⟶[≤] ⦂ ⊢⊸ `$ ⊢M
preservation[≤] ⊢Γ ⊢S                     (Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)                  (ξ-! WL `$ M⟶[≤])
  with ⊢T `⊸[ m ] ⊢S′ ← ⊢⊸                                                                                         = Γ~ ⊢ ⊢L ⦂ ⊢T `⊸[ m ] ⊢S′ `$ preservation[≤] (⊢∧-~⊞-⇒⊢₁ ⊢Γ Γ~) ⊢T ⊢M M⟶[≤]
preservation[≤] ⊢Γ (`↑[-⇒ <m ][ ↑∈m ] ⊢S) (`lift[-⇒-] ⊢L)                       (ξ-`lift[-⇒-] L⟶[≤])               = `lift[-⇒-] preservation[≤] (⊢∧<ₘ⇒⊢ ⊢Γ <m) ⊢S ⊢L L⟶[≤] 
preservation[≤] ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)            (ξ-`unlift[≰ ≰m₀ ⇒-] L⟶[≤])        = Γ∤ ⊢`unlift[-⇒-] preservation[≤] (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢↑ ⊢L L⟶[≤] ⦂ ⊢↑
preservation[≤] ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)            (ξ-`unlift[≤ ≤m₀ ⇒-] L⟶)           = Γ∤ ⊢`unlift[-⇒-] preservation (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢↑ ⊢L L⟶ ⦂ ⊢↑
preservation[≤] ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] `lift[-⇒-] ⊢L ⦂ ⊢↑) (β-↑ m₀≤ WL)                       = ∤⁻¹-preserves-⊢ [] ⊢L Γ∤
preservation[≤] ⊢Γ (`↓[-⇒ m< ][ ↓∈m ] ⊢S) (Γ∤ ⊢`return[-⇒-] ⊢L)                 (ξ-`return[≰ ≰m₀ ⇒-] L⟶[≤])        = Γ∤ ⊢`return[-⇒-] preservation[≤] (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢S ⊢L L⟶[≤]
preservation[≤] ⊢Γ (`↓[-⇒ m< ][ ↓∈m ] ⊢S) (Γ∤ ⊢`return[-⇒-] ⊢L)                 (ξ-`return[≤ ≤m₀ ⇒-] L⟶)           = Γ∤ ⊢`return[-⇒-] preservation (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢S ⊢L L⟶
preservation[≤] ⊢Γ ⊢S                     (Γ~ ⊢`let-return[-⇒-] ⊢L ⦂ ⊢↓ `in ⊢M) ξ-`let-return[-⇒-] L⟶[≤] `in?      = Γ~ ⊢`let-return[-⇒-] preservation[≤] (⊢∧-~⊞-⇒⊢₀ ⊢Γ Γ~) ⊢↓ ⊢L L⟶[≤] ⦂ ⊢↓ `in ⊢M
preservation[≤] ⊢Γ ⊢S                     (Γ~ ⊢`let-return[-⇒-] ⊢L ⦂ ⊢↓ `in ⊢M) (ξ-`let-return[-⇒-]! WL `in M⟶[≤])
  with `↓[-⇒ m< ][ ↓∈m ] ⊢T ← ⊢↓                                                                                   = Γ~ ⊢`let-return[-⇒-] ⊢L ⦂ (`↓[-⇒ m< ][ ↓∈m ] ⊢T) `in preservation[≤] ((⊢T , valid (ℳ.<⇒≤ m<)) ∷ ⊢∧-~⊞-⇒⊢₁ ⊢Γ Γ~) ⊢S ⊢M M⟶[≤]
preservation[≤] ⊢Γ (⊢S `⊸[ ⊸∈m ] ⊢T)      (`λ⦂-∘ ⊢L)                            (ξ-`λ⦂[-]-∘ L⟶[≤])                 = `λ⦂-∘ preservation[≤] ((⊢S , valid ℳ.≤-refl) ∷ ⊢Γ) ⊢T ⊢L L⟶[≤]


canonoical-⊸ : Γ ⊢[ m ] L ⦂ S `⊸ T →
               WeakNorm L →
               ∃₂ (λ S L′ → L ≡ `λ⦂[ m ] S ∘ L′) ⊎ WeakNeut L
canonoical-⊸ (`λ⦂-∘ ⊢L) (`λ⦂[ _ ] _ ∘ _) = inj₁ (_ , _ , refl)
canonoical-⊸ _          (`neut NL)       = inj₂ NL

canonoical-↑ : Γ ⊢[ m ] L ⦂ `↑[ m₀ ⇒ m ] S →
               WeakNorm L →
               ∃ (λ L′ → L ≡ `lift[ m₀ ⇒ m ] L′ × TermWORedex[ m ≤] L′) ⊎ WeakNeut L
canonoical-↑ (`lift[-⇒-] ⊢L) (`lift[ _ ⇒ _ ] WL) = inj₁ (_ , refl , WL)
canonoical-↑ _               (`neut NL)          = inj₂ NL

canonoical-↓ : Γ ⊢[ m ] L ⦂ `↓[ m₀ ⇒ m ] S →
               WeakNorm L →
               ∃ (λ L′ → L ≡ `return[ m₀ ⇒ m ] L′ × WeakNorm L′) ⊎ WeakNeut L
canonoical-↓ (_ ⊢`return[-⇒-] ⊢L) (`return[ _ ⇒ _ ] VL) = inj₁ (_ , refl , VL)
canonoical-↓ _                    (`neut NL)            = inj₂ NL


progress    : ⊢[ m ] Γ →
              ⊢[ m ] S ⦂⋆ →
              Γ ⊢[ m ] L ⦂ S →
              WeakNorm L ⊎ ∃ (λ L′ → L ⟶ L′)
progress[≤] : ∀ m₀ →
              ⊢[ m ] Γ →
              ⊢[ m ] S ⦂⋆ →
              Γ ⊢[ m ] L ⦂ S →
              TermWORedex[ m₀ ≤] L ⊎ ∃ (λ L′ → L ⟶[ m₀ ≤] L′)


progress ⊢Γ ⊢S                            (`unit ΓDel)                          = inj₁ `unit
progress ⊢Γ ⊢S                            (`λ⦂-∘ ⊢L)                            = inj₁ (`λ⦂[ _ ] _ ∘ _)
progress ⊢Γ ⊢S                            (Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)
  with ⊢T `⊸[ _ ] _ ← ⊢⊸
     | ⊢Γ₀ , ⊢Γ₁ ← ⊢∧-~⊞-⇒⊢ ⊢Γ Γ~
    with progress ⊢Γ₀ ⊢⊸ ⊢L
...    | inj₂ (_ , L⟶)                                                          = inj₂ (_ , ξ- L⟶ `$?)
...    | inj₁ VL
      with progress ⊢Γ₁ ⊢T ⊢M
...      | inj₂ (_ , M⟶)                                                        = inj₂ (_ , ξ-! VL `$ M⟶)
...      | inj₁ VM
        with canonoical-⊸ ⊢L VL
...        | inj₂ NL                                                            = inj₁ (`neut (NL `$ VM))
...        | inj₁ (_ , _ , refl)                                                = inj₂ (_ , β-⊸)
progress ⊢Γ (`↑[-⇒_][_]_ {m = m} <m _ ⊢S) (`lift[-⇒-] ⊢L)
  with progress[≤] m (⊢∧<ₘ⇒⊢ ⊢Γ <m) ⊢S ⊢L
...  | inj₂ (_ , L⟶[≤])                                                         = inj₂ (_ , ξ-`lift[-⇒-] L⟶[≤])
...  | inj₁ WL                                                                  = inj₁ (`lift[ _ ⇒ _ ] WL)
progress ⊢Γ ⊢S                            (Γ∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)
  with progress (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢↑ ⊢L
...  | inj₂ (_ , L⟶)                                                            = inj₂ (_ , ξ-`unlift[-⇒-] L⟶)
...  | inj₁ VL
    with canonoical-↑ ⊢L VL
...    | inj₂ NL                                                                = inj₁ (`neut (`unlift[ _ ⇒ _ ] NL))
...    | inj₁ (_ , refl , WL′)                                                  = inj₂ (_ , β-↑ WL′)
progress ⊢Γ (`↓[-⇒ _ ][ _ ] ⊢S)           (Γ∤ ⊢`return[-⇒-] ⊢L)
  with progress (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢S ⊢L
...  | inj₂ (_ , L⟶) = inj₂ (_ , ξ-`return[-⇒-] L⟶)
...  | inj₁ VL       = inj₁ (`return[ _ ⇒ _ ] VL)
progress ⊢Γ ⊢S                            (Γ~ ⊢`let-return[-⇒-] ⊢L ⦂ ⊢↓ `in ⊢M)
  with `↓[-⇒ m< ][ _ ] ⊢T ← ⊢↓
     | ⊢Γ₀ , ⊢Γ₁ ← ⊢∧-~⊞-⇒⊢ ⊢Γ Γ~
    with progress ⊢Γ₀ ⊢↓ ⊢L
...    | inj₂ (_ , L⟶)                                                          = inj₂ (_ , ξ-`let-return[-⇒-] L⟶ `in-)
...    | inj₁ VL
      with canonoical-↓ ⊢L VL
...      | inj₂ NL                                                              = inj₁ (`neut (`let-return[ _ ⇒ _ ] NL `in _))
...      | inj₁ (_ , refl , VL′)                                                = inj₂ (_ , β-↓ VL′)
progress ⊢Γ ⊢S                            (`# x∈)                               = inj₁ (`neut (`# _))


progress[≤]                           m₀ ⊢Γ ⊢S                    (`unit ΓDel)                         = inj₁ `unit
progress[≤]                           m₀ ⊢Γ (⊢S `⊸[ _ ] ⊢T)       (`λ⦂-∘ ⊢L)
  with progress[≤] m₀ ((⊢S , valid ℳ.≤-refl) ∷ ⊢Γ) ⊢T ⊢L
...  | inj₂ (_ , L⟶[≤])                                                                                = inj₂ (_ , ξ-`λ⦂[-]-∘ L⟶[≤])
...  | inj₁ WL                                                                                         = inj₁ (`λ⦂[ _ ] _ ∘ WL)
progress[≤]                           m₀ ⊢Γ ⊢S                    (Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)
  with ⊢T `⊸[ _ ] _ ← ⊢⊸
     | ⊢Γ₀ , ⊢Γ₁ ← ⊢∧-~⊞-⇒⊢ ⊢Γ Γ~
    with progress[≤] m₀ ⊢Γ₀ ⊢⊸ ⊢L
...    | inj₂ (_ , L⟶[≤])                                                                              = inj₂ (_ , ξ- L⟶[≤] `$?)
...    | inj₁ WL
      with progress[≤] m₀ ⊢Γ₁ ⊢T ⊢M
...      | inj₂ (_ , M⟶[≤])                                                                            = inj₂ (_ , ξ-! WL `$ M⟶[≤])
...      | inj₁ WM                                                                                     = inj₁ (WL `$ WM)
progress[≤]                           m₀ ⊢Γ (`↑[-⇒ <m ][ _ ] ⊢S) (`lift[-⇒-] ⊢L)
  with progress[≤] m₀ (⊢∧<ₘ⇒⊢ ⊢Γ <m) ⊢S ⊢L
...  | inj₂ (_ , L⟶[≤])                                                                                = inj₂ (_ , ξ-`lift[-⇒-] L⟶[≤])
...  | inj₁ WL                                                                                         = inj₁ (`lift[ _ ⇒ _ ] WL)
progress[≤] {L = `unlift[ m₁ ⇒ _ ] L} m₀ ⊢Γ ⊢S                   (Γ∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)
  with m₀ ≤?ₘ m₁
...  | no  m₀≰
    with progress[≤] m₀ (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢↑ ⊢L
...    | inj₂ (_ , L⟶[≤])                                                                              = inj₂ (_ , (ξ-`unlift[≰ m₀≰ ⇒-] L⟶[≤]))
...    | inj₁ WL                                                                                       = inj₁ (`unlift[≰ m₀≰ ⇒ _ ] WL)
progress[≤] {L = `unlift[ m₁ ⇒ _ ] L} m₀ ⊢Γ ⊢S                   (Γ∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)
     | yes m₀≤
    with progress (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢↑ ⊢L
...    | inj₂ (_ , L⟶)                                                                                 = inj₂ (_ , ξ-`unlift[≤ m₀≤ ⇒-] L⟶)
...    | inj₁ VL
      with ≢lift[-⇒-]? L
...      | no ¬≢liftL
        with _ , _ , _ , refl ← ¬≢lift[-⇒-]⇒≡lift[-⇒-] L ¬≢liftL
          with `lift[-⇒-] ⊢L′ ← ⊢L
             | `lift[ _ ⇒ _ ] VL′ ← VL                                                                 = inj₂ (_ , β-↑ m₀≤ VL′)
...      | yes ≢liftL                                                                                  = inj₁ (`unlift[≤ m₀≤ ⇒ _ ] VL ≢liftL)
progress[≤] {L = `return[ m₁ ⇒ _ ] L} m₀ ⊢Γ (`↓[-⇒ _ ][ _ ] ⊢S)  (Γ∤ ⊢`return[-⇒-] ⊢L)
  with m₀ ≤?ₘ m₁
...  | no  m₀≰
    with progress[≤] m₀ (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢S ⊢L
...    | inj₂ (_ , L⟶[≤])                                                                              = inj₂ (_ , (ξ-`return[≰ m₀≰ ⇒-] L⟶[≤]))
...    | inj₁ WL                                                                                       = inj₁ (`return[≰ m₀≰ ⇒ _ ] WL)
progress[≤] {L = `return[ m₁ ⇒ _ ] L} m₀ ⊢Γ (`↓[-⇒ _ ][ _ ] ⊢S)  (Γ∤ ⊢`return[-⇒-] ⊢L)
     | yes m₀≤
    with progress (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢S ⊢L
...    | inj₂ (_ , L⟶)                                                                                 = inj₂ (_ , ξ-`return[≤ m₀≤ ⇒-] L⟶)
...    | inj₁ VL                                                                                       = inj₁ (`return[≤ m₀≤ ⇒ _ ] VL)
progress[≤]                           m₀ ⊢Γ ⊢S                   (Γ~ ⊢`let-return[-⇒-] ⊢L ⦂ ⊢↓ `in ⊢M)
  with `↓[-⇒ m< ][ _ ] ⊢T ← ⊢↓
     | ⊢Γ₀ , ⊢Γ₁ ← ⊢∧-~⊞-⇒⊢ ⊢Γ Γ~
    with progress[≤] m₀ ⊢Γ₀ ⊢↓ ⊢L
...    | inj₂ (_ , L⟶[≤])                                                                              = inj₂ (_ , ξ-`let-return[-⇒-] L⟶[≤] `in?)
...    | inj₁ WL
      with progress[≤] m₀ ((⊢T , valid (ℳ.<⇒≤ m<)) ∷ ⊢Γ₁) ⊢S ⊢M
...      | inj₂ (_ , M⟶[≤])                                                                            = inj₂ (_ , ξ-`let-return[-⇒-]! WL `in M⟶[≤])
...      | inj₁ WM                                                                                     = inj₁ (`let-return[ _ ⇒ _ ] WL `in WM)
progress[≤]                          m₀ ⊢Γ ⊢S                   (`# x∈)                                = inj₁ (`# _)
