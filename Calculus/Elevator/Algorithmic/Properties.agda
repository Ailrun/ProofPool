{-# OPTIONS --safe #-}
open import Calculus.Elevator.ModeSpec

module Calculus.Elevator.Algorithmic.Properties {ℓ₁ ℓ₂} (ℳ : ModeSpec ℓ₁ ℓ₂) where
open ModeSpec ℳ

open import Data.Bool as Bool using (true; false)
open import Data.List as List using ([]; _∷_; _++_; length)
import Data.List.Properties as List
open import Data.List.Relation.Unary.All as All using ([]; _∷_)
import Data.List.Relation.Unary.All.Properties as All
open import Data.Nat as ℕ using (suc; _+_; s≤s)
import Data.Nat.Properties as ℕ
open import Data.Product as × using (_×_; _,_; proj₁; proj₂; ∃; ∃₂; -,_)
open import Data.Sum as ⊎ using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Nullary.Decidable using (dec-yes; dec-no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)

import Calculus.Elevator.Syntax as S
import Calculus.Elevator.Typing as T
import Calculus.Elevator.Typing.Properties as TP
import Calculus.Elevator.Algorithmic as A
import Calculus.Elevator.OpSem as O
open S ℳ
open T ℳ
open TP ℳ
open A ℳ
open O ℳ

unused-idempotent : ∀ Δ →
                    unused (unused Δ) ≡ unused Δ
unused-idempotent []      = refl
unused-idempotent (_ ∷ Δ) = cong (_ ∷_) (unused-idempotent Δ)

~⊞-unusedˡ : Δ ~ Δ₀ ⊞ Δ₁ →
            unused Δ ≡ unused Δ₀
~⊞-unusedˡ []       = refl
~⊞-unusedˡ (_ ∷ Δ~) = cong (_ ∷_) (~⊞-unusedˡ Δ~)

~⊞-preserves-unused : Δ ~ Δ₀ ⊞ Δ₁ →
                      unused Δ ~ unused Δ₀ ⊞ unused Δ₁
~⊞-preserves-unused []        = []
~⊞-preserves-unused (d~ ∷ Δ~) = unusable ∷ ~⊞-preserves-unused Δ~

~d⊞-uniqueʳ : d [ m ]~d d′ ⊞ false →
              d ≡ d′
~d⊞-uniqueʳ unusable = refl
~d⊞-uniqueʳ to-left  = refl

~⊞-uniqueʳ : ∀ Γ₁ →
             Γ ~ Γ₀ ⊞ unused Γ₁ →
             Γ ≡ Γ₀
~⊞-uniqueʳ []       []        = refl
~⊞-uniqueʳ (_ ∷ Γ₁) (d~ ∷ Γ~)
  rewrite ~d⊞-uniqueʳ d~  = cong (_ ∷_) (~⊞-uniqueʳ Γ₁ Γ~)

~⊞-unused-assoc : ∀ Δ′ →
                  Δ ~ Δ₀ ⊞ Δ₁ →
                  Ψ₀ ~ Δ₀ ⊞ unused Δ′ →
                  Ψ₁ ~ Δ₁ ⊞ unused Δ′ →
                  ∃ (λ Δ″ → Δ″ ~ Δ ⊞ unused Δ′ × Δ″ ~ Ψ₀ ⊞ Ψ₁)
~⊞-unused-assoc []       []        []          []          = _ , [] , []
~⊞-unused-assoc (_ ∷ Δ′) (d~ ∷ Δ~) (d₀~ ∷ Ψ₀~) (d₁~ ∷ Ψ₁~)
  with _ , Δ″~ , Δ″∼′ ← ~⊞-unused-assoc Δ′ Δ~ Ψ₀~ Ψ₁~
    rewrite ~d⊞-uniqueʳ d₀~
          | ~d⊞-uniqueʳ d₁~ = _ , ~d⊞-identityʳ _ ∷ Δ″~ , d~ ∷ Δ″∼′

~⊞-preserves-drop⇒ : ∀ m →
                     Δ ~ Δ₀ ⊞ Δ₁ →
                     Δ drop[ m ]⇒ ~ Δ₀ drop[ m ]⇒ ⊞ Δ₁ drop[ m ]⇒
~⊞-preserves-drop⇒ m []                   = []
~⊞-preserves-drop⇒ m (_∷_ {m = m₀} d~ Δ~)
  with m ≤?ₘ m₀
...  | yes _ = d~ ∷ ~⊞-preserves-drop⇒ m Δ~
...  | no  _ = unusable ∷ ~⊞-preserves-drop⇒ m Δ~

unused-cancelˡ-drop⇒ : ∀ m Δ →
                       unused (Δ drop[ m ]⇒) ≡ unused Δ
unused-cancelˡ-drop⇒ m []                 = refl
unused-cancelˡ-drop⇒ m ((_ , m₀ , _) ∷ Δ)
  with m ≤?ₘ m₀
...  | yes _ = cong (_ ∷_) (unused-cancelˡ-drop⇒ m Δ)
...  | no  _ = cong (_ ∷_) (unused-cancelˡ-drop⇒ m Δ)

unused-cancelʳ-drop⇒ : ∀ m Δ →
                       unused Δ drop[ m ]⇒ ≡ unused Δ
unused-cancelʳ-drop⇒ m []                 = refl
unused-cancelʳ-drop⇒ m ((_ , m₀ , _) ∷ Δ)
  with m ≤?ₘ m₀
...  | yes _ = cong (_ ∷_) (unused-cancelʳ-drop⇒ m Δ)
...  | no  _ = cong (_ ∷_) (unused-cancelʳ-drop⇒ m Δ)

~d⊞-true⇒true : d [ m ]~d true ⊞ d′ →
                d ≡ true
~d⊞-true⇒true (contraction Co∈m) = refl
~d⊞-true⇒true to-left            = refl

~⊞-preserves-usage∈ : Γ ~ Γ₀ ⊞ Γ₁ →
                      x ⦂[ m ] S ∈ Γ₀ ⇒ Δ₀ →
                      ∃ (λ Δ → Δ ~ Δ₀ ⊞ unused Γ₁ × x ⦂[ m ] S ∈ Γ ⇒ Δ)
~⊞-preserves-usage∈ {m = m} (d~ ∷ Γ~) here
  rewrite proj₂ (dec-yes (m ≤?ₘ m) ≤ₘ-refl)
        | ~d⊞-true⇒true d~                      = _ , to-left ∷ ~⊞-preserves-unused Γ~ , here
~⊞-preserves-usage∈        (d~ ∷ Γ~) (there x∈)
  with _ , Δ~ , x∈′ ← ~⊞-preserves-usage∈ Γ~ x∈ = _ , unusable ∷ Δ~ , there x∈′

~⊞-preserves-usage : Γ ~ Γ₀ ⊞ Γ₁ →
                     Γ₀ ⊢[ m ] L ⦂ S ⇒ Δ₀ →
                     ∃ (λ Δ → Δ ~ Δ₀ ⊞ unused Γ₁ × Γ ⊢[ m ] L ⦂ S ⇒ Δ)
~⊞-preserves-usage Γ~ `unit = _ , ~⊞-preserves-unused Γ~ , `unit
~⊞-preserves-usage Γ~ (`λ⦂[ dUsed ]-∘ ⊢L⇒)
  with _ , ~d ∷ Δ~ , ⊢L⇒′ ← ~⊞-preserves-usage (to-left ∷ Γ~) ⊢L⇒
    rewrite ~d⊞-uniqueʳ ~d = _ , Δ~ , `λ⦂[ dUsed ]-∘ ⊢L⇒′
~⊞-preserves-usage Γ~ (Δ₀~ ⊢ ⊢L⇒ ⦂ ⊢⊸ `$ ⊢M⇒)
  with _ , ~ΔuΓ₁ , ⊢L⇒′ ← ~⊞-preserves-usage Γ~ ⊢L⇒
     | _ , ~Δ′uΓ₁ , ⊢M′⇒ ← ~⊞-preserves-usage Γ~ ⊢M⇒
    with _ , Δ~ , Δ~′ ← ~⊞-unused-assoc _ Δ₀~ ~ΔuΓ₁ ~Δ′uΓ₁ = _ , Δ~ , Δ~′ ⊢ ⊢L⇒′ ⦂ ⊢⊸ `$ ⊢M′⇒
~⊞-preserves-usage Γ~ (`lift[-⇒-] ⊢L⇒)
  with _ , Δ~ , ⊢L⇒′ ← ~⊞-preserves-usage Γ~ ⊢L⇒ = _ , Δ~ , `lift[-⇒-] ⊢L⇒′
~⊞-preserves-usage {Γ₁ = Γ₁} Γ~ (`unlift[-⇒-]_⦂_ {m₀ = m₀} ⊢L⇒ ⊢↑)
  with _ , Δ~ , ⊢L⇒′ ← ~⊞-preserves-usage (~⊞-preserves-drop⇒ m₀ Γ~) ⊢L⇒
    rewrite unused-cancelˡ-drop⇒ m₀ Γ₁             = _ , Δ~ , `unlift[-⇒-] ⊢L⇒′ ⦂ ⊢↑
~⊞-preserves-usage {Γ₁ = Γ₁} Γ~ (`return[-⇒-]_ {m₀ = m₀} ⊢L⇒)
  with _ , Δ~ , ⊢L⇒′ ← ~⊞-preserves-usage (~⊞-preserves-drop⇒ m₀ Γ~) ⊢L⇒
    rewrite unused-cancelˡ-drop⇒ m₀ Γ₁              = _ , Δ~ , `return[-⇒-] ⊢L⇒′
~⊞-preserves-usage Γ~ (Δ₀~ ⊢`let-return[-⇒ dUsed ] ⊢L⇒ ⦂ ⊢↓ `in ⊢M⇒)
  with _ , ~ΔuΓ₁ , ⊢L⇒′ ← ~⊞-preserves-usage Γ~ ⊢L⇒
     | _ , ~d ∷ ~Δ′uΓ₁ , ⊢M′⇒ ← ~⊞-preserves-usage (to-left ∷ Γ~) ⊢M⇒
    with _ , Δ~ , Δ~′ ← ~⊞-unused-assoc _ Δ₀~ ~ΔuΓ₁ ~Δ′uΓ₁
      rewrite ~d⊞-uniqueʳ ~d = _ , Δ~ , Δ~′ ⊢`let-return[-⇒ dUsed ] ⊢L⇒′ ⦂ ⊢↓ `in ⊢M′⇒
~⊞-preserves-usage Γ~ (`# x∈)
  with _ , Δ~ , x∈′ ← ~⊞-preserves-usage∈ Γ~ x∈ = _ , Δ~ , `# x∈′

drop⇒-∤-consistent : Γ ∤[ m ] Γ′ →
                     Γ′ ≡ Γ drop[ m ]⇒
drop⇒-∤-consistent []                    = refl
drop⇒-∤-consistent (delete m≰ dDel ∷ Γ∤)
  rewrite dec-no (_ ≤?ₘ _) m≰            = cong (_ ∷_) (drop⇒-∤-consistent Γ∤)
drop⇒-∤-consistent (keep   m≤      ∷ Γ∤)
  rewrite proj₂ (dec-yes (_ ≤?ₘ _) m≤)   = cong (_ ∷_) (drop⇒-∤-consistent Γ∤)

used-by⇒~d⊞ : d [ m ]is-used-by d₀ →
              ∃ (λ d₁ → d [ m ]~d d₀ ⊞ d₁ × d₁ [ m ]is-del)
used-by⇒~d⊞ used             = _ , to-left , unusable
used-by⇒~d⊞ (weakening Wk∈m) = _ , to-right , weakening Wk∈m

∉unused : ∀ Γ →
          ¬ (x ⦂[ m ] S ∈ unused Γ ⇒ Ψ)
∉unused (_ ∷ Γ) (there x∈) = ∉unused Γ x∈

∈drop⇒∈ : ∀ Γ →
         x ⦂[ m₀ ] S ∈ Γ drop[ m ]⇒ ⇒ Ψ →
         x ⦂[ m₀ ] S ∈ Γ ⇒ Ψ
∈drop⇒∈ {m = m} ((_ , m₁ , d) ∷ Γ) x∈
  with m ≤?ₘ m₁ | x∈
...  | yes _    | here
    rewrite unused-cancelˡ-drop⇒ m Γ = here
...  | yes _    | there x∈′          = there (∈drop⇒∈ Γ x∈′)
...  | no  _    | there x∈′          = there (∈drop⇒∈ Γ x∈′)

~⊞-preserves-∈ : Δ ~ Δ₀ ⊞ Δ₁ →
                x ⦂[ m ] S ∈ Δ ⇒ Ψ →
                (x ⦂[ m ] S ∈ Δ₀ ⇒ Ψ) ⊎ (x ⦂[ m ] S ∈ Δ₁ ⇒ Ψ)
~⊞-preserves-∈ (_  ∷ Δ~) (there x∈)
  with ~⊞-preserves-∈ Δ~ x∈
...  | inj₁ x∈′ = inj₁ (there x∈′)
...  | inj₂ x∈′ = inj₂ (there x∈′)
~⊞-preserves-∈ (contraction Co∈m ∷ Δ~) here
  rewrite ~⊞-unusedˡ Δ~ = inj₁ here
~⊞-preserves-∈ (to-left ∷ Δ~) here
  rewrite ~⊞-unusedˡ Δ~ = inj₁ here
~⊞-preserves-∈ (to-right ∷ Δ~) here
  rewrite ~⊞-unusedˡ (~⊞-swap Δ~) = inj₂ here

∈∧∈⇒∈ : y ⦂[ m ] S ∈ Γ ⇒ Δ →
        x ⦂[ m₀ ] T ∈ Δ ⇒ Ψ →
        x ⦂[ m₀ ] T ∈ Γ ⇒ Ψ
∈∧∈⇒∈ {Γ = _ ∷ Γ} here here
  rewrite unused-idempotent Γ = here
∈∧∈⇒∈ here (there x∈) with () ← ∉unused _ x∈
∈∧∈⇒∈ (there y∈) (there x∈) = there (∈∧∈⇒∈ y∈ x∈)

⊢∧∈⇒∈ : Γ ⊢[ m ] L ⦂ S ⇒ Δ →
        x ⦂[ m₀ ] T ∈ Δ ⇒ Ψ →
        x ⦂[ m₀ ] T ∈ Γ ⇒ Ψ
⊢∧∈⇒∈ `unit x∈ with () ← ∉unused _ x∈
⊢∧∈⇒∈ (`λ⦂[ dDel ]-∘ ⊢L) x∈
  with there x∈′ ← ⊢∧∈⇒∈ ⊢L (there x∈) = x∈′
⊢∧∈⇒∈ (Δ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M) x∈
  with ~⊞-preserves-∈ Δ~ x∈
...  | inj₁ x∈₀ = ⊢∧∈⇒∈ ⊢L x∈₀
...  | inj₂ x∈₁ = ⊢∧∈⇒∈ ⊢M x∈₁
⊢∧∈⇒∈ (`lift[-⇒-] ⊢L) x∈ = ⊢∧∈⇒∈ ⊢L x∈
⊢∧∈⇒∈ (`unlift[-⇒-] ⊢L ⦂ ⊢↑) x∈ = ∈drop⇒∈ _ (⊢∧∈⇒∈ ⊢L x∈)
⊢∧∈⇒∈ (`return[-⇒-] ⊢L) x∈ = ∈drop⇒∈ _ (⊢∧∈⇒∈ ⊢L x∈)
⊢∧∈⇒∈ (Δ~ ⊢`let-return[-⇒ dDel ] ⊢L ⦂ ⊢↓ `in ⊢M) x∈
  with ~⊞-preserves-∈ Δ~ x∈
...  | inj₁ x∈₀ = ⊢∧∈⇒∈ ⊢L x∈₀
...  | inj₂ x∈₁
    with there x∈′ ← ⊢∧∈⇒∈ ⊢M (there x∈₁) = x∈′
⊢∧∈⇒∈ (`# y∈) x∈ = ∈∧∈⇒∈ y∈ x∈

¬∈⇒∤self : (∀ {x m₀ S Δ} → ¬ (m ≤ₘ m₀) → ¬ x ⦂[ m₀ ] S ∈ Γ ⇒ Δ) →
            Γ ∤[ m ] Γ
¬∈⇒∤self         {Γ = []}               ¬∈ = []
¬∈⇒∤self {m = m} {Γ = (S , m₀ , d) ∷ Γ} ¬∈
  with m ≤?ₘ m₀
...  | yes m≤ = keep m≤ ∷ ¬∈⇒∤self (λ ≰m₀ x∈ → ¬∈ ≰m₀ (there x∈))
...  | no  m≰
    with d
...    | true with () ← ¬∈ m≰ here
...    | false = delete m≰ unusable ∷ ¬∈⇒∤self (λ ≰m₀ x∈ → ¬∈ ≰m₀ (there x∈))

¬∈drop : ∀ Γ →
         ¬ (m ≤ₘ m₀) →
         ¬ x ⦂[ m₀ ] S ∈ Γ drop[ m ]⇒ ⇒ Δ
¬∈drop {m = m} ((_ , m₁ , d) ∷ Γ) m≰ x∈
  with m ≤?ₘ m₁ | x∈
...  | yes m≤   | here      with () ← m≰ m≤
...  | yes _    | there x∈′ = ¬∈drop Γ m≰ x∈′
...  | no  _    | there x∈′ = ¬∈drop Γ m≰ x∈′

~d⊞-preserves-is-used-by : d [ m ]~d d₀ ⊞ d₁ →
                           d₀ [ m ]is-used-by dS₀ →
                           d₁ [ m ]is-used-by dS₁ →
                           ∃ (λ dS → dS [ m ]~d dS₀ ⊞ dS₁ × d [ m ]is-used-by dS)
~d⊞-preserves-is-used-by (contraction Co∈m) used             used             = _ , contraction Co∈m , used
~d⊞-preserves-is-used-by (contraction Co∈m) used             (weakening Wk∈m) = _ , to-left , used
~d⊞-preserves-is-used-by (contraction Co∈m) (weakening Wk∈m) d₁Used           = _ , ~d⊞-identityˡ _ , d₁Used

~⊞-preserves-is-all-used-by : Γ ~ Γ₀ ⊞ Γ₁ →
                              Γ₀ is-all-used-by Δ₀ →
                              Γ₁ is-all-used-by Δ₁ →
                              ∃ (λ Δ → Δ ~ Δ₀ ⊞ Δ₁ × Γ is-all-used-by Δ)
~⊞-preserves-is-all-used-by [] [] [] = _ , [] , []
~⊞-preserves-is-all-used-by (d~ ∷ Γ~) (d₀Used ∷ Γ₀Used) (d₁Used ∷ Γ₁Used)
  with _ , dS~ , dUsed ← ~d⊞-preserves-is-used-by d~ d₀Used d₁Used
     | _ , Δ~ , ΓUsed ← ~⊞-preserves-is-all-used-by Γ~ Γ₀Used Γ₁Used = _ , dS~ ∷ Δ~ , dUsed ∷ ΓUsed

completeness : Γ ⊢[ m ] L ⦂ S →
               Γ A⊢[ m ] L ⦂ S
completeness (`unit ΓDel) = _ , `unit , {!!}
completeness (`λ⦂-∘ ⊢L)
  with _ , ⊢L⇒ , dUsed ∷ Γ′Used ← completeness ⊢L = _ , `λ⦂[ dUsed ]-∘ ⊢L⇒ , Γ′Used
completeness (Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)
  with _ , ⊢L⇒ , Γ₀Used ← completeness ⊢L
     | _ , ⊢M⇒ , Γ₁Used ← completeness ⊢M
    with _ , Δ₀~ , ⊢L⇒′ ← ~⊞-preserves-usage Γ~ ⊢L⇒
       | _ , Δ₁~ , ⊢M⇒′ ← ~⊞-preserves-usage (~⊞-swap Γ~) ⊢M⇒
      rewrite ~⊞-uniqueʳ _ Δ₀~
            | ~⊞-uniqueʳ _ Δ₁~
        with _ , Δ~ , ΓUsed ← ~⊞-preserves-is-all-used-by Γ~ Γ₀Used Γ₁Used = _ , Δ~ ⊢ ⊢L⇒′ ⦂ ⊢⊸ `$ ⊢M⇒′ , ΓUsed
completeness (`lift[-⇒-] ⊢L)
  with _ , ⊢L⇒ , Γ′Used ← completeness ⊢L = _ , `lift[-⇒-] ⊢L⇒ , Γ′Used
completeness (Γ∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)
  with _ , ⊢L⇒ , Γ′Used ← completeness ⊢L
    rewrite drop⇒-∤-consistent Γ∤ = _ , `unlift[-⇒-] ⊢L⇒ ⦂ ⊢↑ , {!!}
completeness (Γ∤ ⊢`return[-⇒-] ⊢L)
  with _ , ⊢L⇒ , Γ′Used ← completeness ⊢L
    rewrite drop⇒-∤-consistent Γ∤ = _ , `return[-⇒-] ⊢L⇒ , {!!}
completeness (Γ~ ⊢`let-return[-⇒-] ⊢L ⦂ ⊢↓ `in ⊢M)
  with _ , ⊢L⇒ , Γ₀Used ← completeness ⊢L
     | _ , ⊢M⇒ , dUsed ∷ Γ₁Used ← completeness ⊢M
    with _ , Δ₀~ , ⊢L⇒′ ← ~⊞-preserves-usage Γ~ ⊢L⇒
       | _ , d~ ∷ Δ₁~ , ⊢M⇒′ ← ~⊞-preserves-usage (to-left ∷ ~⊞-swap Γ~) ⊢M⇒
      rewrite ~d⊞-uniqueʳ d~
            | ~⊞-uniqueʳ _ Δ₀~
            | ~⊞-uniqueʳ _ Δ₁~
        with _ , Δ~ , ΓUsed ← ~⊞-preserves-is-all-used-by Γ~ Γ₀Used Γ₁Used = _ , Δ~ ⊢`let-return[-⇒ dUsed ] ⊢L⇒′ ⦂ ⊢↓ `in ⊢M⇒′ , ΓUsed
completeness (`# x∈) = {!!} , `# {!!} , {!!}

soundness-helper : Γ ⊢[ m ] L ⦂ S ⇒ Δ →
                   Δ ⊢[ m ] L ⦂ S
soundness-helper `unit = `unit {!!}
soundness-helper {Δ = Δ} (`λ⦂[ dUsed ]-∘ ⊢L⇒)
  with _ , Δ~ ← left-bias-~⊞ Δ
     | Δ′Del ← left-bias-~⊞-is-all-del Δ
     | _ , ~d , d₁Del ← used-by⇒~d⊞ dUsed = `λ⦂-∘ ~⊞-is-all-del∧⊢⇒⊢ (~d⊞-swap ~d ∷ ~⊞-swap Δ~) (d₁Del ∷ Δ′Del) (soundness-helper ⊢L⇒)
soundness-helper (Δ~ ⊢ ⊢L⇒ ⦂ ⊢⊸ `$ ⊢M⇒) = Δ~ ⊢ soundness-helper ⊢L⇒ ⦂ ⊢⊸ `$ soundness-helper ⊢M⇒
soundness-helper (`lift[-⇒-] ⊢L⇒) = `lift[-⇒-] soundness-helper ⊢L⇒
soundness-helper {Γ = Γ} (`unlift[-⇒-] ⊢L⇒ ⦂ ⊢↑) = ¬∈⇒∤self (λ ≰m₀ x∈ → ¬∈drop Γ ≰m₀ (⊢∧∈⇒∈ ⊢L⇒ x∈)) ⊢`unlift[-⇒-] soundness-helper ⊢L⇒ ⦂ ⊢↑
soundness-helper {Γ = Γ} (`return[-⇒-] ⊢L⇒) = ¬∈⇒∤self (λ ≰m₀ x∈ → ¬∈drop Γ ≰m₀ (⊢∧∈⇒∈ ⊢L⇒ x∈)) ⊢`return[-⇒-] soundness-helper ⊢L⇒
soundness-helper (_⊢`let-return[-⇒_]_⦂_`in_ {Δ₁ = Δ₁} Δ~ dUsed ⊢L⇒ ⊢↓ ⊢M⇒)
  with _ , Δ₁~ ← left-bias-~⊞ Δ₁
     | Δ₁′Del ← left-bias-~⊞-is-all-del Δ₁
     | _ , ~d , d₁Del ← used-by⇒~d⊞ dUsed = Δ~ ⊢`let-return[-⇒-] soundness-helper ⊢L⇒ ⦂ ⊢↓ `in ~⊞-is-all-del∧⊢⇒⊢ (~d⊞-swap ~d ∷ ~⊞-swap Δ₁~) (d₁Del ∷ Δ₁′Del) (soundness-helper ⊢M⇒)
soundness-helper (`# x∈) = `# {!!}

soundness : Γ A⊢[ m ] L ⦂ S →
            Γ ⊢[ m ] L ⦂ S
soundness (_ , ⊢L⇒ , ΓUsed) = ~⊞-is-all-del∧⊢⇒⊢ {!!} {!!} (soundness-helper ⊢L⇒)
