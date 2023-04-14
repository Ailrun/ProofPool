{-# OPTIONS --safe #-}
open import Calculus.Elevator.ModeSpec

module Calculus.Elevator.Algorithmic.Properties {ℓ₁ ℓ₂} (ℳ : ModeSpec ℓ₁ ℓ₂) where
open ModeSpec ℳ

open import Data.Bool as Bool using (true; false)
open import Data.List as List using ([]; _∷_; _++_; length)
import Data.List.Properties as List
open import Data.List.Relation.Unary.All as All using ([]; _∷_)
import Data.List.Relation.Unary.All.Properties as All
open import Data.Nat as ℕ using (zero; suc; _+_; s≤s)
import Data.Nat.Properties as ℕ
open import Data.Product as × using (_×_; _,_; proj₁; proj₂; ∃; ∃₂; -,_)
open import Data.Sum as ⊎ using (_⊎_; inj₁; inj₂)
open import Function using (case_of_; _∘′_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable as Dec using (dec-yes; dec-no; _×-dec_)
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
~⊞-unused-assoc []       []        []          []          = -, [] , []
~⊞-unused-assoc (_ ∷ Δ′) (d~ ∷ Δ~) (d₀~ ∷ Ψ₀~) (d₁~ ∷ Ψ₁~)
  with _ , Δ″~ , Δ″∼′ ← ~⊞-unused-assoc Δ′ Δ~ Ψ₀~ Ψ₁~
    rewrite ~d⊞-uniqueʳ d₀~
          | ~d⊞-uniqueʳ d₁~ = -, ~d⊞-identityʳ _ ∷ Δ″~ , d~ ∷ Δ″∼′

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
        | ~d⊞-true⇒true d~                        = -, to-left ∷ ~⊞-preserves-unused Γ~ , here
~⊞-preserves-usage∈         (d~ ∷ Γ~) (there x∈⇒)
  with _ , Δ~ , x∈⇒′ ← ~⊞-preserves-usage∈ Γ~ x∈⇒ = -, unusable ∷ Δ~ , there x∈⇒′

~⊞-preserves-usage : Γ ~ Γ₀ ⊞ Γ₁ →
                     Γ₀ ⊢[ m ] L ⦂ S ⇒ Δ₀ →
                     ∃ (λ Δ → Δ ~ Δ₀ ⊞ unused Γ₁ × Γ ⊢[ m ] L ⦂ S ⇒ Δ)
~⊞-preserves-usage           Γ~ `unit                                          = -, ~⊞-preserves-unused Γ~ , `unit
~⊞-preserves-usage           Γ~ (`λ⦂[ dUsed ]-∘ ⊢L⇒)
  with _ , ~d ∷ Δ~ , ⊢L⇒′ ← ~⊞-preserves-usage (to-left ∷ Γ~) ⊢L⇒
    rewrite ~d⊞-uniqueʳ ~d                                                     = -, Δ~ , `λ⦂[ dUsed ]-∘ ⊢L⇒′
~⊞-preserves-usage           Γ~ (Δ₀~ ⊢ ⊢L⇒ ⦂ ⊢⊸ `$ ⊢M⇒)
  with _ , ~ΔuΓ₁ , ⊢L⇒′ ← ~⊞-preserves-usage Γ~ ⊢L⇒
     | _ , ~Δ′uΓ₁ , ⊢M′⇒ ← ~⊞-preserves-usage Γ~ ⊢M⇒
    with _ , Δ~ , Δ~′ ← ~⊞-unused-assoc _ Δ₀~ ~ΔuΓ₁ ~Δ′uΓ₁                     = -, Δ~ , Δ~′ ⊢ ⊢L⇒′ ⦂ ⊢⊸ `$ ⊢M′⇒
~⊞-preserves-usage           Γ~ (`lift[-⇒-] ⊢L⇒)
  with _ , Δ~ , ⊢L⇒′ ← ~⊞-preserves-usage Γ~ ⊢L⇒                               = -, Δ~ , `lift[-⇒-] ⊢L⇒′
~⊞-preserves-usage {Γ₁ = Γ₁} Γ~ (`unlift[-⇒-]_⦂_ {m₀ = m₀} ⊢L⇒ ⊢↑)
  with _ , Δ~ , ⊢L⇒′ ← ~⊞-preserves-usage (~⊞-preserves-drop⇒ m₀ Γ~) ⊢L⇒
    rewrite unused-cancelˡ-drop⇒ m₀ Γ₁                                         = -, Δ~ , `unlift[-⇒-] ⊢L⇒′ ⦂ ⊢↑
~⊞-preserves-usage {Γ₁ = Γ₁} Γ~ (`return[-⇒-]_ {m₀ = m₀} ⊢L⇒)
  with _ , Δ~ , ⊢L⇒′ ← ~⊞-preserves-usage (~⊞-preserves-drop⇒ m₀ Γ~) ⊢L⇒
    rewrite unused-cancelˡ-drop⇒ m₀ Γ₁                                         = -, Δ~ , `return[-⇒-] ⊢L⇒′
~⊞-preserves-usage           Γ~ (Δ₀~ ⊢`let-return[-⇒ dUsed ] ⊢L⇒ ⦂ ⊢↓ `in ⊢M⇒)
  with _ , ~ΔuΓ₁ , ⊢L⇒′ ← ~⊞-preserves-usage Γ~ ⊢L⇒
     | _ , ~d ∷ ~Δ′uΓ₁ , ⊢M′⇒ ← ~⊞-preserves-usage (to-left ∷ Γ~) ⊢M⇒
    with _ , Δ~ , Δ~′ ← ~⊞-unused-assoc _ Δ₀~ ~ΔuΓ₁ ~Δ′uΓ₁
      rewrite ~d⊞-uniqueʳ ~d                                                   = -, Δ~ , Δ~′ ⊢`let-return[-⇒ dUsed ] ⊢L⇒′ ⦂ ⊢↓ `in ⊢M′⇒
~⊞-preserves-usage           Γ~ (`# x∈⇒)
  with _ , Δ~ , x∈⇒′ ← ~⊞-preserves-usage∈ Γ~ x∈⇒                              = -, Δ~ , `# x∈⇒′

drop⇒-∤-consistent : Γ ∤[ m ] Γ′ →
                     Γ′ ≡ Γ drop[ m ]⇒
drop⇒-∤-consistent []                    = refl
drop⇒-∤-consistent (delete m≰ dDel ∷ Γ∤)
  rewrite dec-no (_ ≤?ₘ _) m≰            = cong (_ ∷_) (drop⇒-∤-consistent Γ∤)
drop⇒-∤-consistent (keep   m≤      ∷ Γ∤)
  rewrite proj₂ (dec-yes (_ ≤?ₘ _) m≤)   = cong (_ ∷_) (drop⇒-∤-consistent Γ∤)

used-by⇒~d⊞ : d [ m ]is-used-by d₀ →
              ∃ (λ d₁ → d [ m ]~d d₀ ⊞ d₁ × d₁ [ m ]is-del)
used-by⇒~d⊞ used             = -, to-left , unusable
used-by⇒~d⊞ unusable         = -, unusable , unusable
used-by⇒~d⊞ (weakening Wk∈m) = -, to-right , weakening Wk∈m

∉unused : ∀ Γ →
          ¬ (x ⦂[ m ] S ∈ unused Γ ⇒ Ψ)
∉unused (_ ∷ Γ) (there x∈⇒) = ∉unused Γ x∈⇒

∈drop⇒∈ : ∀ Γ →
         x ⦂[ m₀ ] S ∈ Γ drop[ m ]⇒ ⇒ Ψ →
         x ⦂[ m₀ ] S ∈ Γ ⇒ Ψ
∈drop⇒∈ {m = m} ((_ , m₁ , d) ∷ Γ) x∈⇒
  with m ≤?ₘ m₁ | x∈⇒
...  | yes _    | here
    rewrite unused-cancelˡ-drop⇒ m Γ = here
...  | yes _    | there x∈⇒′         = there (∈drop⇒∈ Γ x∈⇒′)
...  | no  _    | there x∈⇒′         = there (∈drop⇒∈ Γ x∈⇒′)

~⊞-preserves-∈ : Δ ~ Δ₀ ⊞ Δ₁ →
                x ⦂[ m ] S ∈ Δ ⇒ Ψ →
                (x ⦂[ m ] S ∈ Δ₀ ⇒ Ψ) ⊎ (x ⦂[ m ] S ∈ Δ₁ ⇒ Ψ)
~⊞-preserves-∈ (_  ∷ Δ~)               (there x∈⇒)
  with ~⊞-preserves-∈ Δ~ x∈⇒
...  | inj₁ x∈⇒′                                   = inj₁ (there x∈⇒′)
...  | inj₂ x∈⇒′                                   = inj₂ (there x∈⇒′)
~⊞-preserves-∈ (contraction Co∈m ∷ Δ~) here
  rewrite ~⊞-unusedˡ Δ~                            = inj₁ here
~⊞-preserves-∈ (to-left ∷ Δ~)          here
  rewrite ~⊞-unusedˡ Δ~                            = inj₁ here
~⊞-preserves-∈ (to-right ∷ Δ~)         here
  rewrite ~⊞-unusedˡ (~⊞-swap Δ~)                  = inj₂ here

∈⇒∧∈⇒⇒∈⇒ : y ⦂[ m ] S ∈ Γ ⇒ Δ →
        x ⦂[ m₀ ] T ∈ Δ ⇒ Ψ →
        x ⦂[ m₀ ] T ∈ Γ ⇒ Ψ
∈⇒∧∈⇒⇒∈⇒ {Γ = _ ∷ Γ} here        here
  rewrite unused-idempotent Γ                = here
∈⇒∧∈⇒⇒∈⇒             here        (there x∈⇒) with () ← ∉unused _ x∈⇒
∈⇒∧∈⇒⇒∈⇒             (there y∈⇒) (there x∈⇒) = there (∈⇒∧∈⇒⇒∈⇒ y∈⇒ x∈⇒)

⊢∧∈⇒⇒∈⇒ : Γ ⊢[ m ] L ⦂ S ⇒ Δ →
        x ⦂[ m₀ ] T ∈ Δ ⇒ Ψ →
        x ⦂[ m₀ ] T ∈ Γ ⇒ Ψ
⊢∧∈⇒⇒∈⇒ `unit                                      x∈⇒ with () ← ∉unused _ x∈⇒
⊢∧∈⇒⇒∈⇒ (`λ⦂[ dDel ]-∘ ⊢L)                         x∈⇒
  with there x∈⇒′ ← ⊢∧∈⇒⇒∈⇒ ⊢L (there x∈⇒)             = x∈⇒′
⊢∧∈⇒⇒∈⇒ (Δ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)                       x∈⇒
  with ~⊞-preserves-∈ Δ~ x∈⇒
...  | inj₁ x∈⇒₀                                       = ⊢∧∈⇒⇒∈⇒ ⊢L x∈⇒₀
...  | inj₂ x∈⇒₁                                       = ⊢∧∈⇒⇒∈⇒ ⊢M x∈⇒₁
⊢∧∈⇒⇒∈⇒ (`lift[-⇒-] ⊢L)                            x∈⇒ = ⊢∧∈⇒⇒∈⇒ ⊢L x∈⇒
⊢∧∈⇒⇒∈⇒ (`unlift[-⇒-] ⊢L ⦂ ⊢↑)                     x∈⇒ = ∈drop⇒∈ _ (⊢∧∈⇒⇒∈⇒ ⊢L x∈⇒)
⊢∧∈⇒⇒∈⇒ (`return[-⇒-] ⊢L)                          x∈⇒ = ∈drop⇒∈ _ (⊢∧∈⇒⇒∈⇒ ⊢L x∈⇒)
⊢∧∈⇒⇒∈⇒ (Δ~ ⊢`let-return[-⇒ dDel ] ⊢L ⦂ ⊢↓ `in ⊢M) x∈⇒
  with ~⊞-preserves-∈ Δ~ x∈⇒
...  | inj₁ x∈⇒₀                                       = ⊢∧∈⇒⇒∈⇒ ⊢L x∈⇒₀
...  | inj₂ x∈⇒₁
    with there x∈⇒′ ← ⊢∧∈⇒⇒∈⇒ ⊢M (there x∈⇒₁)          = x∈⇒′
⊢∧∈⇒⇒∈⇒ (`# y∈⇒)                                   x∈⇒ = ∈⇒∧∈⇒⇒∈⇒ y∈⇒ x∈⇒

¬∈⇒⇒∤self : (∀ {x m₀ S Δ} → ¬ (m ≤ₘ m₀) → ¬ x ⦂[ m₀ ] S ∈ Γ ⇒ Δ) →
            Γ ∤[ m ] Γ
¬∈⇒⇒∤self         {Γ = []}               ¬∈ = []
¬∈⇒⇒∤self {m = m} {Γ = (S , m₀ , d) ∷ Γ} ¬∈
  with m ≤?ₘ m₀
...  | yes m≤                               = keep m≤ ∷ ¬∈⇒⇒∤self (λ ≰m₀ x∈ → ¬∈ ≰m₀ (there x∈))
...  | no  m≰
    with d
...    | true with () ← ¬∈ m≰ here
...    | false                              = delete m≰ unusable ∷ ¬∈⇒⇒∤self (λ ≰m₀ x∈ → ¬∈ ≰m₀ (there x∈))

¬∈drop⇒ : ∀ Γ →
          ¬ (m ≤ₘ m₀) →
          ¬ x ⦂[ m₀ ] S ∈ Γ drop[ m ]⇒ ⇒ Δ
¬∈drop⇒ {m = m} ((_ , m₁ , d) ∷ Γ) m≰ x∈⇒
  with m ≤?ₘ m₁ | x∈⇒
...  | yes m≤   | here       with () ← m≰ m≤
...  | yes _    | there x∈⇒′ = ¬∈drop⇒ Γ m≰ x∈⇒′
...  | no  _    | there x∈⇒′ = ¬∈drop⇒ Γ m≰ x∈⇒′

~d⊞-preserves-is-used-by : d [ m ]~d d₀ ⊞ d₁ →
                           d₀ [ m ]is-used-by dS₀ →
                           d₁ [ m ]is-used-by dS₁ →
                           ∃ (λ dS → dS [ m ]~d dS₀ ⊞ dS₁ × d [ m ]is-used-by dS)
~d⊞-preserves-is-used-by (contraction Co∈m) used             used             = -, contraction Co∈m , used
~d⊞-preserves-is-used-by (contraction Co∈m) used             (weakening Wk∈m) = -, to-left , used
~d⊞-preserves-is-used-by (contraction Co∈m) (weakening Wk∈m) d₁Used           = -, ~d⊞-identityˡ _ , d₁Used
~d⊞-preserves-is-used-by to-left            d₀Used           unusable         = -, ~d⊞-identityʳ _ , d₀Used
~d⊞-preserves-is-used-by to-right           unusable         d₁Used           = -, ~d⊞-identityˡ _ , d₁Used
~d⊞-preserves-is-used-by unusable           unusable         d₁Used           = -, ~d⊞-identityˡ _ , d₁Used

~⊞-preserves-is-all-used-by : Γ ~ Γ₀ ⊞ Γ₁ →
                              Γ₀ is-all-used-by Δ₀ →
                              Γ₁ is-all-used-by Δ₁ →
                              ∃ (λ Δ → Δ ~ Δ₀ ⊞ Δ₁ × Γ is-all-used-by Δ)
~⊞-preserves-is-all-used-by []        []                []                = -, [] , []
~⊞-preserves-is-all-used-by (d~ ∷ Γ~) (d₀Used ∷ Γ₀Used) (d₁Used ∷ Γ₁Used)
  with _ , dS~ , dUsed ← ~d⊞-preserves-is-used-by d~ d₀Used d₁Used
     | _ , Δ~ , ΓUsed ← ~⊞-preserves-is-all-used-by Γ~ Γ₀Used Γ₁Used      = -, dS~ ∷ Δ~ , dUsed ∷ ΓUsed

is-del⇒is-used-by-false : ∀ m →
                          d [ m ]is-del →
                          d [ m ]is-used-by false
is-del⇒is-used-by-false m unusable         = unusable
is-del⇒is-used-by-false m (weakening Wk∈m) = weakening Wk∈m

is-all-del⇒is-all-used-by-unused : Γ is-all-del →
                                   Γ is-all-used-by unused Γ
is-all-del⇒is-all-used-by-unused []            = []
is-all-del⇒is-all-used-by-unused (dDel ∷ ΓDel) = is-del⇒is-used-by-false _ dDel ∷ is-all-del⇒is-all-used-by-unused ΓDel

∤d⁻¹-preserves-is-used-by : d [ m₀ ]∤[ m ]d d′ →
                            d′ [ m₀ ]is-used-by dS →
                            d [ m₀ ]is-used-by dS
∤d⁻¹-preserves-is-used-by (delete _ dDel) unusable = is-del⇒is-used-by-false _ dDel
∤d⁻¹-preserves-is-used-by (keep _)        d′Used   = d′Used

∤⁻¹-preserves-is-all-used-by : Γ ∤[ m ] Γ′ →
                               Γ′ is-all-used-by Δ →
                               Γ is-all-used-by Δ
∤⁻¹-preserves-is-all-used-by []        []                = []
∤⁻¹-preserves-is-all-used-by (d∤ ∷ Γ∤) (d′Used ∷ Γ′Used) = ∤d⁻¹-preserves-is-used-by d∤ d′Used ∷ ∤⁻¹-preserves-is-all-used-by Γ∤ Γ′Used

unused-is-all-del : ∀ Γ →
                    unused Γ is-all-del
unused-is-all-del []      = []
unused-is-all-del (_ ∷ Γ) = unusable ∷ unused-is-all-del Γ

is-used-by⇒~d⊞-is-del : d [ m ]is-used-by dS →
                        ∃ (λ d′ → d [ m ]~d dS ⊞ d′ × d′ [ m ]is-del)
is-used-by⇒~d⊞-is-del used             = -, to-left , unusable
is-used-by⇒~d⊞-is-del unusable         = -, unusable , unusable
is-used-by⇒~d⊞-is-del (weakening Wk∈m) = -, to-right , weakening Wk∈m

is-all-used-by⇒~⊞-is-all-del : Γ is-all-used-by Δ →
                               ∃ (λ Γ′ → Γ ~ Δ ⊞ Γ′ × Γ′ is-all-del)
is-all-used-by⇒~⊞-is-all-del []                            = -, [] , []
is-all-used-by⇒~⊞-is-all-del (dUsed ∷ ΓUsed)
  with _ , d~ , d′Del ← is-used-by⇒~d⊞-is-del dUsed
     | _ , Γ~ , Γ′Del ← is-all-used-by⇒~⊞-is-all-del ΓUsed = -, d~ ∷ Γ~ , d′Del ∷ Γ′Del

completeness∈ : x ⦂[ m ] S ∈ Γ →
                ∃ (λ Δ → x ⦂[ m ] S ∈ Γ ⇒ Δ × Γ is-all-used-by Δ)
completeness∈ (here ΓDel)                 = -, here , used ∷ is-all-del⇒is-all-used-by-unused ΓDel
completeness∈ (there dDel x∈)
  with _ , x∈⇒ , ΓUsed ← completeness∈ x∈ = -, there x∈⇒ , is-del⇒is-used-by-false _ dDel ∷ ΓUsed

completeness : Γ ⊢[ m ] L ⦂ S →
               Γ A⊢[ m ] L ⦂ S
completeness (`unit ΓDel)                                                  = -, `unit , is-all-del⇒is-all-used-by-unused ΓDel
completeness (`λ⦂-∘ ⊢L)
  with _ , ⊢L⇒ , dUsed ∷ Γ′Used ← completeness ⊢L                          = -, `λ⦂[ dUsed ]-∘ ⊢L⇒ , Γ′Used
completeness (Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)
  with _ , ⊢L⇒ , Γ₀Used ← completeness ⊢L
     | _ , ⊢M⇒ , Γ₁Used ← completeness ⊢M
    with _ , Δ₀~ , ⊢L⇒′ ← ~⊞-preserves-usage Γ~ ⊢L⇒
       | _ , Δ₁~ , ⊢M⇒′ ← ~⊞-preserves-usage (~⊞-swap Γ~) ⊢M⇒
      rewrite ~⊞-uniqueʳ _ Δ₀~
            | ~⊞-uniqueʳ _ Δ₁~
        with _ , Δ~ , ΓUsed ← ~⊞-preserves-is-all-used-by Γ~ Γ₀Used Γ₁Used = -, Δ~ ⊢ ⊢L⇒′ ⦂ ⊢⊸ `$ ⊢M⇒′ , ΓUsed
completeness (`lift[-⇒-] ⊢L)
  with _ , ⊢L⇒ , Γ′Used ← completeness ⊢L                                  = -, `lift[-⇒-] ⊢L⇒ , Γ′Used
completeness (Γ∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)
  with _ , ⊢L⇒ , Γ′Used ← completeness ⊢L
     | refl ← drop⇒-∤-consistent Γ∤                                        = -, `unlift[-⇒-] ⊢L⇒ ⦂ ⊢↑ , ∤⁻¹-preserves-is-all-used-by Γ∤ Γ′Used
completeness (Γ∤ ⊢`return[-⇒-] ⊢L)
  with _ , ⊢L⇒ , Γ′Used ← completeness ⊢L
     | refl ← drop⇒-∤-consistent Γ∤                                        = -, `return[-⇒-] ⊢L⇒ , ∤⁻¹-preserves-is-all-used-by Γ∤ Γ′Used
completeness (Γ~ ⊢`let-return[-⇒-] ⊢L ⦂ ⊢↓ `in ⊢M)
  with _ , ⊢L⇒ , Γ₀Used ← completeness ⊢L
     | _ , ⊢M⇒ , dUsed ∷ Γ₁Used ← completeness ⊢M
    with _ , Δ₀~ , ⊢L⇒′ ← ~⊞-preserves-usage Γ~ ⊢L⇒
       | _ , d~ ∷ Δ₁~ , ⊢M⇒′ ← ~⊞-preserves-usage (to-left ∷ ~⊞-swap Γ~) ⊢M⇒
      rewrite ~d⊞-uniqueʳ d~
            | ~⊞-uniqueʳ _ Δ₀~
            | ~⊞-uniqueʳ _ Δ₁~
        with _ , Δ~ , ΓUsed ← ~⊞-preserves-is-all-used-by Γ~ Γ₀Used Γ₁Used = -, Δ~ ⊢`let-return[-⇒ dUsed ] ⊢L⇒′ ⦂ ⊢↓ `in ⊢M⇒′ , ΓUsed
completeness (`# x∈)
  with _ , x∈⇒ , ΓUsed ← completeness∈ x∈                                  = -, `# x∈⇒ , ΓUsed

soundness-helper∈ : x ⦂[ m ] S ∈ Γ ⇒ Δ →
                    x ⦂[ m ] S ∈ Δ
soundness-helper∈ here        = here (unused-is-all-del _)
soundness-helper∈ (there x∈⇒) = there unusable (soundness-helper∈ x∈⇒)

soundness-helper : Γ ⊢[ m ] L ⦂ S ⇒ Δ →
                   Δ ⊢[ m ] L ⦂ S
soundness-helper                 `unit                                                     = `unit (unused-is-all-del _)
soundness-helper         {Δ = Δ} (`λ⦂[ dUsed ]-∘ ⊢L⇒)
  with _ , Δ~ ← left-bias-~⊞ Δ
     | Δ′Del ← left-bias-~⊞-is-all-del Δ
     | _ , ~d , d₁Del ← used-by⇒~d⊞ dUsed                                                  = `λ⦂-∘ ⊢L
   where
     ⊢L = ~⊞-is-all-del∧⊢⇒⊢ (~⊞-swap (~d ∷ Δ~)) (d₁Del ∷ Δ′Del) (soundness-helper ⊢L⇒)

soundness-helper                 (Δ~ ⊢ ⊢L⇒ ⦂ ⊢⊸ `$ ⊢M⇒)                                    = Δ~ ⊢ soundness-helper ⊢L⇒ ⦂ ⊢⊸ `$ soundness-helper ⊢M⇒
soundness-helper                 (`lift[-⇒-] ⊢L⇒)                                          = `lift[-⇒-] soundness-helper ⊢L⇒
soundness-helper {Γ = Γ}         (`unlift[-⇒-] ⊢L⇒ ⦂ ⊢↑)                                   = Δ∤ ⊢`unlift[-⇒-] soundness-helper ⊢L⇒ ⦂ ⊢↑
  where
    Δ∤ = ¬∈⇒⇒∤self (λ ≰m₀ x∈ → ¬∈drop⇒ Γ ≰m₀ (⊢∧∈⇒⇒∈⇒ ⊢L⇒ x∈))

soundness-helper {Γ = Γ}         (`return[-⇒-] ⊢L⇒)                                        = Δ∤ ⊢`return[-⇒-] soundness-helper ⊢L⇒
  where
    Δ∤ = ¬∈⇒⇒∤self (λ ≰m₀ x∈ → ¬∈drop⇒ Γ ≰m₀ (⊢∧∈⇒⇒∈⇒ ⊢L⇒ x∈))

soundness-helper                 (_⊢`let-return[-⇒_]_⦂_`in_ {Δ₁ = Δ₁} Δ~ dUsed ⊢L⇒ ⊢↓ ⊢M⇒)
  with _ , Δ₁~ ← left-bias-~⊞ Δ₁
     | Δ₁′Del ← left-bias-~⊞-is-all-del Δ₁
     | _ , ~d , d₁Del ← used-by⇒~d⊞ dUsed                                                  = Δ~ ⊢`let-return[-⇒-] soundness-helper ⊢L⇒ ⦂ ⊢↓ `in ⊢M
    where
      ⊢M = ~⊞-is-all-del∧⊢⇒⊢ (~⊞-swap (~d ∷ Δ₁~)) (d₁Del ∷ Δ₁′Del) (soundness-helper ⊢M⇒)

soundness-helper (`# x∈⇒)                                                                  = `# soundness-helper∈ x∈⇒

soundness : Γ A⊢[ m ] L ⦂ S →
            Γ ⊢[ m ] L ⦂ S
soundness (_ , ⊢L⇒ , ΓUsed)
  with _ , Γ~ , Γ′Del ← is-all-used-by⇒~⊞-is-all-del ΓUsed = ~⊞-is-all-del∧⊢⇒⊢ (~⊞-swap Γ~) Γ′Del (soundness-helper ⊢L⇒)

infix   4 _⊢[_]_⦂?⇒?
infix   4 _A⊢[_]_⦂?

unused-++ : ∀ Γ₀ {Γ₁} →
            unused (Γ₀ ++ Γ₁) ≡ unused Γ₀ ++ unused Γ₁
unused-++ []       = refl
unused-++ (_ ∷ Γ₀) = cong (_ ∷_) (unused-++ Γ₀)

unused-length : ∀ Γ →
                length (unused Γ) ≡ length Γ
unused-length []      = refl
unused-length (_ ∷ Γ) = cong suc (unused-length Γ)

~d⊞⁻¹-det : d [ m ]~d d₀ ⊞ d₁ →
            d′ [ m ]~d d₀ ⊞ d₁ →
            d ≡ d′
~d⊞⁻¹-det (contraction Co∈m) (contraction Co∈m′) = refl
~d⊞⁻¹-det to-left            to-left             = refl
~d⊞⁻¹-det to-right           to-right            = refl
~d⊞⁻¹-det unusable           unusable            = refl

~⊞⁻¹-det : Δ ~ Δ₀ ⊞ Δ₁ →
           Δ′ ~ Δ₀ ⊞ Δ₁ →
           Δ ≡ Δ′
~⊞⁻¹-det []        []          = refl
~⊞⁻¹-det (d~ ∷ Δ~) (d′~ ∷ Δ′~)
  rewrite ~d⊞⁻¹-det d~ d′~
        | ~⊞⁻¹-det Δ~ Δ′~      = refl

∈-det : x ⦂[ m ] S ∈ Γ ⇒ Δ →
        x ⦂[ m ] S′ ∈ Γ ⇒ Δ′ →
        S ≡ S′ × Δ ≡ Δ′
∈-det here       here             = refl , refl
∈-det (there x∈) (there x∈′)
  with refl , refl ← ∈-det x∈ x∈′ = refl , refl

⊢-det : Γ ⊢[ m ] L ⦂ S ⇒ Δ →
        Γ ⊢[ m ] L ⦂ S′ ⇒ Δ′ →
        S ≡ S′ × Δ ≡ Δ′
⊢-det `unit                                      `unit                                           = refl , refl
⊢-det (`λ⦂[ dDel ]-∘ ⊢L)                         (`λ⦂[ dDel′ ]-∘ ⊢L′)
  with refl , refl ← ⊢-det ⊢L ⊢L′                                                                = refl , refl
⊢-det (Δ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)                       (Δ′~ ⊢ ⊢L′ ⦂ ⊢⊸′ `$ ⊢M′)
  with refl , refl ← ⊢-det ⊢L ⊢L′
     | refl , refl ← ⊢-det ⊢M ⊢M′                                                                = refl , ~⊞⁻¹-det Δ~ Δ′~
⊢-det (`lift[-⇒-] ⊢L)                            (`lift[-⇒-] ⊢L′)
  with refl , refl ← ⊢-det ⊢L ⊢L′                                                                = refl , refl
⊢-det (`unlift[-⇒-] ⊢L ⦂ ⊢↑)                     (`unlift[-⇒-] ⊢L′ ⦂ ⊢↑′)
  with refl , refl ← ⊢-det ⊢L ⊢L′                                                                = refl , refl
⊢-det (`return[-⇒-] ⊢L)                          (`return[-⇒-] ⊢L′)
  with refl , refl ← ⊢-det ⊢L ⊢L′                                                                = refl , refl
⊢-det (Δ~ ⊢`let-return[-⇒ dDel ] ⊢L ⦂ ⊢↓ `in ⊢M) (Δ′~ ⊢`let-return[-⇒ dDel′ ] ⊢L′ ⦂ ⊢↓′ `in ⊢M′)
  with refl , refl ← ⊢-det ⊢L ⊢L′
    with refl , refl ← ⊢-det ⊢M ⊢M′                                                              = refl , ~⊞⁻¹-det Δ~ Δ′~
⊢-det (`# x∈)                                    (`# x∈′)                                        = ∈-det x∈ x∈′

_Type≟_ : ∀ (S T : Type) → Dec (S ≡ T)
`⊤              Type≟ `⊤              = yes refl
`⊤              Type≟ (T `⊸ T′)       = no λ()
`⊤              Type≟ `↑[ m₂ ⇒ m₃ ] T = no λ()
`⊤              Type≟ `↓[ m₂ ⇒ m₃ ] T = no λ()
(S `⊸ S′)       Type≟ `⊤              = no λ()
(S `⊸ S′)       Type≟ (T `⊸ T′)       = Dec.map′
                                          (λ{ (refl , refl) → refl })
                                          (λ{ refl → refl , refl })
                                          (S Type≟ T ×-dec S′ Type≟ T′)
(S `⊸ S′)       Type≟ `↑[ m₂ ⇒ m₃ ] T = no λ()
(S `⊸ S′)       Type≟ `↓[ m₂ ⇒ m₃ ] T = no λ()
`↑[ m₀ ⇒ m₁ ] S Type≟ `⊤              = no λ()
`↑[ m₀ ⇒ m₁ ] S Type≟ (T `⊸ T′)       = no λ()
`↑[ m₀ ⇒ m₁ ] S Type≟ `↑[ m₂ ⇒ m₃ ] T = Dec.map′
                                          (λ{ (refl , refl , refl) → refl })
                                          (λ{ refl → refl , refl , refl })
                                          (m₀ ≟ₘ m₂ ×-dec m₁ ≟ₘ m₃ ×-dec S Type≟ T)
`↑[ m₀ ⇒ m₁ ] S Type≟ `↓[ m₂ ⇒ m₃ ] T = no λ()
`↓[ m₀ ⇒ m₁ ] S Type≟ `⊤              = no λ()
`↓[ m₀ ⇒ m₁ ] S Type≟ (T `⊸ T′)       = no λ()
`↓[ m₀ ⇒ m₁ ] S Type≟ `↑[ m₂ ⇒ m₃ ] T = no λ()
`↓[ m₀ ⇒ m₁ ] S Type≟ `↓[ m₂ ⇒ m₃ ] T = Dec.map′
                                          (λ{ (refl , refl , refl) → refl })
                                          (λ{ refl → refl , refl , refl })
                                          (m₀ ≟ₘ m₂ ×-dec m₁ ≟ₘ m₃ ×-dec S Type≟ T)

?[_]~d_⊞_ : ∀ m d₀ d₁ → Dec (∃ (λ d → d [ m ]~d d₀ ⊞ d₁))
?[ m ]~d false ⊞ d₁    = yes (-, ~d⊞-identityˡ _)
?[ m ]~d true  ⊞ false = yes (-, to-left)
?[ m ]~d true  ⊞ true  = Dec.map′ (λ Co∈m → -, contraction Co∈m) (λ{ (_ , contraction Co∈m) → Co∈m }) (Bool.T? (stₘ m ``Co))

?~_⊞_ : ∀ Δ₀ Δ₁ → Dec (∃ (λ Δ → Δ ~ Δ₀ ⊞ Δ₁))
?~ []                    ⊞ []                    = yes (-, [])
?~ []                    ⊞ (_              ∷ Δ₁) = no λ()
?~ (_              ∷ Δ₀) ⊞ []                    = no λ()
?~ ((S₀ , m₀ , d₀) ∷ Δ₀) ⊞ ((S₁ , m₁ , d₁) ∷ Δ₁) = Dec.map′
                                                     (λ{ (refl , refl , (_ , d~) , _ , Δ~) → -, d~ ∷ Δ~ })
                                                     (λ{ (_ , d~ ∷ Δ~) → refl , refl , (-, d~) , -, Δ~ })
                                                     (S₀ Type≟ S₁ ×-dec m₀ ≟ₘ m₁ ×-dec ?[ m₀ ]~d d₀ ⊞ d₁ ×-dec ?~ Δ₀ ⊞ Δ₁)

⊢[_]_?⦂⋆ : ∀ m S → Dec (⊢[ m ] S ⦂⋆)
⊢[ m ] `⊤              ?⦂⋆ = Dec.map′
                               `⊤[_]
                               (λ{ `⊤[ ⊤∈m ] → ⊤∈m })
                               (Bool.T? (opₘ m ``⊤))
⊢[ m ] S `⊸ T          ?⦂⋆ = Dec.map′
                               (×.uncurry′ (×.uncurry′ ∘′ _`⊸[_]_))
                               (λ{ (⊢S `⊸[ ⊸∈m ] ⊢T) → ⊢S , ⊸∈m , ⊢T })
                               (⊢[ m ] S ?⦂⋆ ×-dec Bool.T? (opₘ m ``⊸) ×-dec ⊢[ m ] T ?⦂⋆)
⊢[ m ] `↑[ m₀ ⇒ m₁ ] S ?⦂⋆ = Dec.map′
                               (λ{ (refl , <m , ↑∈m , ⊢S) → `↑[-⇒ <m ][ ↑∈m ] ⊢S })
                               (λ{ (`↑[-⇒ <m ][ ↑∈m ] ⊢S) → refl , <m , ↑∈m , ⊢S})
                               (m ≟ₘ m₁ ×-dec m₀ <?ₘ m ×-dec Bool.T? (opₘ m ``↑) ×-dec ⊢[ m₀ ] S ?⦂⋆)
⊢[ m ] `↓[ m₀ ⇒ m₁ ] S ?⦂⋆ = Dec.map′
                               (λ{ (refl , m< , ↓∈m , ⊢S) → `↓[-⇒ m< ][ ↓∈m ] ⊢S })
                               (λ{ (`↓[-⇒ m< ][ ↓∈m ] ⊢S) → refl , m< , ↓∈m , ⊢S})
                               (m ≟ₘ m₁ ×-dec m <?ₘ m₀ ×-dec Bool.T? (opₘ m ``↓) ×-dec ⊢[ m₀ ] S ?⦂⋆)

_[_]is-used-by?_ : ∀ d m dS → Dec (d [ m ]is-used-by dS)
false [ m ]is-used-by? false = yes unusable
false [ m ]is-used-by? true  = no λ()
true  [ m ]is-used-by? false = Dec.map′ weakening (λ{ (weakening Wk∈m) → Wk∈m }) (Bool.T? (stₘ m ``Wk))
true  [ m ]is-used-by? true  = yes used

_is-all-used-by?_ : ∀ Γ Δ → Dec (Γ is-all-used-by Δ)
[]                is-all-used-by? []                   = yes []
[]                is-all-used-by? (_              ∷ Δ) = no λ()
(_           ∷ Γ) is-all-used-by? []                   = no λ()
((S , m , d) ∷ Γ) is-all-used-by? ((S′ , m′ , dS) ∷ Δ) = Dec.map′
                                                           (λ{ (refl , refl , dUsed , ΓUsed) → dUsed ∷ ΓUsed })
                                                           (λ{ (dUsed ∷ ΓUsed) → refl , refl , dUsed , ΓUsed })
                                                           (S Type≟ S′ ×-dec m ≟ₘ m′ ×-dec d [ m ]is-used-by? dS ×-dec Γ is-all-used-by? Δ)

_⦂[_]?∈_⇒? : ∀ x m Γ → Dec (∃₂ (λ S Δ → x ⦂[ m ] S ∈ Γ ⇒ Δ))
x     ⦂[ m ]?∈ []                   ⇒? = no λ()
zero  ⦂[ m ]?∈ (S , m₀ , true)  ∷ Γ ⇒? = Dec.map′ (λ{ refl → -, -, here }) (λ{ (_ , _ , here) → refl }) (m ≟ₘ m₀)
zero  ⦂[ m ]?∈ (S , m₀ , false) ∷ Γ ⇒? = no λ()
suc x ⦂[ m ]?∈ _                ∷ Γ ⇒? = Dec.map′ (λ{ (_ , _ , x∈) → -, -, there x∈ }) (λ{ (_ , _ , there x∈) → -, -, x∈ }) (x ⦂[ m ]?∈ Γ ⇒?)

_⊢[_]_⦂?⇒? : ∀ Γ m L → Dec (∃₂ (λ S Δ → Γ ⊢[ m ] L ⦂ S ⇒ Δ))
Γ ⊢[ m ] `unit                          ⦂?⇒? = yes (-, -, `unit)
Γ ⊢[ m ] `lift[ m₀ ⇒ m₁ ] L             ⦂?⇒? = Dec.map′
                                                 (λ{ (refl , _ , _ , ⊢L) → -, -, `lift[-⇒-] ⊢L })
                                                 (λ{ (_ , _ , `lift[-⇒-] ⊢L) → refl , -, -, ⊢L })
                                                 (m ≟ₘ m₁ ×-dec Γ ⊢[ m₀ ] L ⦂?⇒?)
Γ ⊢[ m ] `unlift[ m₀ ⇒ m₁ ] L           ⦂?⇒?
  with m ≟ₘ m₁
...  | no  m≢m₁                              = no λ{ (_ , _ , `unlift[-⇒-] _ ⦂ _) → m≢m₁ refl }
...  | yes refl
    with Γ drop[ m₀ ]⇒ ⊢[ m₀ ] L ⦂?⇒?
...    | no ⊬L                               = no λ{ (_ , _ , `unlift[-⇒-] ⊢L ⦂ _) → ⊬L (-, -, ⊢L) }
...    | yes (↑T , _ , ⊢L)
      with ↑T
...      | `⊤                                = no λ{ (_ , _ , `unlift[-⇒-] ⊢L′ ⦂ _) → case (⊢-det ⊢L ⊢L′) of λ() }
...      | `↓[ _ ⇒ _ ] _                     = no λ{ (_ , _ , `unlift[-⇒-] ⊢L′ ⦂ _) → case (⊢-det ⊢L ⊢L′) of λ() }
...      | _ `⊸ _                            = no λ{ (_ , _ , `unlift[-⇒-] ⊢L′ ⦂ _) → case (⊢-det ⊢L ⊢L′) of λ() }
...      | ↑T@(`↑[ m₂ ⇒ m₃ ] T)              = Dec.map′
                                                 (λ{ (refl , ⊢↑@(`↑[-⇒ _ ][ _ ] _)) → -, -, `unlift[-⇒-] ⊢L ⦂ ⊢↑ })
                                                 (λ{ (_ , _ , `unlift[-⇒-] ⊢L′ ⦂ ⊢↑) →
                                                   case (⊢-det ⊢L ⊢L′) of λ{ (refl , refl) → refl , ⊢↑ }
                                                 })
                                                 (m ≟ₘ m₂ ×-dec ⊢[ m₀ ] ↑T ?⦂⋆)
Γ ⊢[ m ] `return[ m₀ ⇒ m₁ ] L           ⦂?⇒? = Dec.map′
                                                 (λ{ (refl , _ , _ , ⊢L) → -, -, `return[-⇒-] ⊢L })
                                                 (λ{ (_ , _ , `return[-⇒-] ⊢L′) → refl , -, -, ⊢L′ })
                                                 (m ≟ₘ m₁ ×-dec Γ drop[ m₀ ]⇒ ⊢[ m₀ ] L ⦂?⇒?)
Γ ⊢[ m ] `let-return[ m₀ ⇒ m₁ ] L `in M ⦂?⇒?
  with m ≟ₘ m₀
...  | no m≢m₀                               = no λ{ (_ , _ , _ ⊢`let-return[-⇒ _ ] _ ⦂ _ `in _) → m≢m₀ refl }
...  | yes refl
    with Γ ⊢[ m ] L ⦂?⇒?
...    | no  ⊬L                              = no λ{ (_ , _ , _ ⊢`let-return[-⇒ _ ] ⊢L ⦂ _ `in _) → ⊬L (-, -, ⊢L) }
...    | yes (↓T , Δ₀ , ⊢L)
      with ↓T
...      | `⊤                                = no λ{ (_ , _ , _ ⊢`let-return[-⇒ _ ] ⊢L′ ⦂ _ `in _) → case (⊢-det ⊢L ⊢L′) of λ() }
...      | `↑[ _ ⇒ _ ] _                     = no λ{ (_ , _ , _ ⊢`let-return[-⇒ _ ] ⊢L′ ⦂ _ `in _) → case (⊢-det ⊢L ⊢L′) of λ() }
...      | _ `⊸ _                            = no λ{ (_ , _ , _ ⊢`let-return[-⇒ _ ] ⊢L′ ⦂ _ `in _) → case (⊢-det ⊢L ⊢L′) of λ() }
...      | ↓T@(`↓[ m₂ ⇒ m₃ ] T)
        with m₁ ≟ₘ m₂
...        | no m₁≢m₂                        = no λ{ (_ , _ , _ ⊢`let-return[-⇒ _ ] ⊢L′ ⦂ _ `in _) → case (⊢-det ⊢L ⊢L′) of λ{ (refl , refl) → m₁≢m₂ refl } }
...        | yes refl
          with ⊢[ m₀ ] ↓T ?⦂⋆
...          | no ⊬↓                         = no λ{ (_ , _ , _ ⊢`let-return[-⇒ _ ] ⊢L′ ⦂ ⊢↓ `in _) → case (⊢-det ⊢L ⊢L′) of λ{ (refl , refl) → ⊬↓ ⊢↓ } }
...          | yes ⊢↓@(`↓[-⇒ _ ][ _ ] _)
          with (T , m₁ , true) ∷ Γ ⊢[ m ] M ⦂?⇒?
...          | no  ⊬M                        = no λ{ (_ , _ , _ ⊢`let-return[-⇒ _ ] ⊢L′ ⦂ _ `in ⊢M) → case (⊢-det ⊢L ⊢L′) of λ{ (refl , refl) → ⊬M (-, -, ⊢M) } }
...          | yes (_ , TΔ₁ , ⊢M)
            with TΔ₁
...            | []                          = no λ{ (_ , _ , _ ⊢`let-return[-⇒ _ ] ⊢L′ ⦂ _ `in ⊢M′) → case (⊢-det ⊢L ⊢L′) of λ{ (refl , refl) → case (⊢-det ⊢M ⊢M′) of λ() } }
...            | (T′ , m₁′ , d) ∷ Δ₁         = Dec.map′
                                                 (λ{ ((_ , Δ~) , refl , refl , dUsed) → -, -, Δ~ ⊢`let-return[-⇒ dUsed ] ⊢L ⦂ ⊢↓ `in ⊢M })
                                                 (λ{ (_ , _ , Δ~ ⊢`let-return[-⇒ dUsed ] ⊢L′ ⦂ _ `in ⊢M′) →
                                                   case (⊢-det ⊢L ⊢L′) of
                                                   λ{ (refl , refl) →
                                                     case (⊢-det ⊢M ⊢M′) of
                                                     λ{ (refl , refl) → (-, Δ~) , refl , refl , dUsed }
                                                   }
                                                 })
                                                 (?~ Δ₀ ⊞ Δ₁ ×-dec T Type≟ T′ ×-dec m₁ ≟ₘ m₁′ ×-dec true [ m₁ ]is-used-by? d)
Γ ⊢[ m ] `λ⦂[ m′ ] S ∘ L                ⦂?⇒?
  with m ≟ₘ m′
...  | no  m≢m′                              = no λ{ (_ , _ , `λ⦂[ _ ]-∘ _) → m≢m′ refl }
...  | yes refl
    with (S , m , true) ∷ Γ ⊢[ m ] L ⦂?⇒?
...    | no  ⊬L                              = no λ{ (_ , _ , `λ⦂[ _ ]-∘ ⊢L) → ⊬L (-, -, ⊢L) }
...    | yes (_ , Δ , ⊢L)
      with Δ
...      | []                                = no λ{ (_ , _ , `λ⦂[ _ ]-∘ ⊢L′) → case (⊢-det ⊢L ⊢L′) of λ() }
...      | (S′ , m′ , d) ∷ Δ′                = Dec.map′
                                                 (λ{ (refl , refl , dUsed) → -, -, `λ⦂[ dUsed ]-∘ ⊢L })
                                                 (λ{ (_ , _ , `λ⦂[ dUsed ]-∘ ⊢L′) →
                                                   case (⊢-det ⊢L ⊢L′) of
                                                   λ{ (refl , refl) → refl , refl , dUsed }
                                                 })
                                                 (S Type≟ S′ ×-dec m ≟ₘ m′ ×-dec true [ m ]is-used-by? d)
Γ ⊢[ m ] L `$ M                         ⦂?⇒?
  with Γ ⊢[ m ] L ⦂?⇒?
...  | no  ⊬L                                = no λ{ (_ , _ , _ ⊢ ⊢L ⦂ _ `$ _) → ⊬L (-, -, ⊢L) }
...  | yes (T⊸S , Δ₀ , ⊢L)
    with T⊸S
...    | `⊤                                  = no λ{ (_ , _ , _ ⊢ ⊢L′ ⦂ _ `$ _) → case (⊢-det ⊢L ⊢L′) of λ() }
...    | `↑[ _ ⇒ _ ] _                       = no λ{ (_ , _ , _ ⊢ ⊢L′ ⦂ _ `$ _) → case (⊢-det ⊢L ⊢L′) of λ() }
...    | `↓[ _ ⇒ _ ] _                       = no λ{ (_ , _ , _ ⊢ ⊢L′ ⦂ _ `$ _) → case (⊢-det ⊢L ⊢L′) of λ() }
...    | T⊸S@(T `⊸ _)
      with ⊢[ m ] T⊸S ?⦂⋆
...      | no  ⊬⊸                            = no λ{ (_ , _ , _ ⊢ ⊢L′ ⦂ ⊢⊸ `$ _) → case (⊢-det ⊢L ⊢L′) of λ{ (refl , refl) → ⊬⊸ ⊢⊸ } }
...      | yes ⊢⊸
        with Γ ⊢[ m ] M ⦂?⇒?
...        | no  ⊬M                          = no λ{ (_ , _ , _ ⊢ _ ⦂ _ `$ ⊢M) → ⊬M (-, -, ⊢M) }
...        | yes (T′ , Δ₁ , ⊢M)              = Dec.map′
                                                 (λ{ ((_ , Δ~) , refl) → -, -, Δ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M })
                                                 (λ{ (_ , _ , Δ~ ⊢ ⊢L′ ⦂ _ `$ ⊢M′) →
                                                   case (⊢-det ⊢L ⊢L′) of
                                                   λ{ (refl , refl) →
                                                     case (⊢-det ⊢M ⊢M′) of
                                                     λ{ (refl , refl) → (-, Δ~) , refl }
                                                   }
                                                 })
                                                 (?~ Δ₀ ⊞ Δ₁ ×-dec T Type≟ T′)
Γ ⊢[ m ] `# x                           ⦂?⇒? = Dec.map′
                                                 (λ{ (_ , _ , x∈) → -, -, `# x∈ })
                                                 (λ{ (_ , _ , `# x∈) → -, -, x∈ })
                                                 (x ⦂[ m ]?∈ Γ ⇒?)

_A⊢[_]_⦂? : ∀ Γ m L → Dec (∃ (λ S → Γ A⊢[ m ] L ⦂ S))
Γ A⊢[ m ] L ⦂?
  with Γ ⊢[ m ] L ⦂?⇒?
...  | no  ⊬L           = no (λ{ (_ , _ , ⊢L , _) → ⊬L (-, -, ⊢L) })
...  | yes (_ , Δ , ⊢L) = Dec.map′
                            (λ{ ΓUsed → _ , Δ , ⊢L , ΓUsed })
                            (λ{ (_ , _ , ⊢L′ , ΓUsed) →
                              case (⊢-det ⊢L ⊢L′) of
                              λ{ (refl , refl) → ΓUsed }
                            })
                            (Γ is-all-used-by? Δ)
