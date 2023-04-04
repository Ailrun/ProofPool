{-# OPTIONS --safe #-}
open import Calculus.Elevator.ModeSpec

module Calculus.Elevator.Lemma ℓ₁ ℓ₂ (ℳ : ModeSpec ℓ₁ ℓ₂) where
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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst; subst₂; _≢_; ≢-sym)

import Calculus.Elevator.Syntax as S
import Calculus.Elevator.Typing as T
import Calculus.Elevator.OpSem as O
open S ℓ₁ ℓ₂ ℳ
open T ℓ₁ ℓ₂ ℳ
open O ℓ₁ ℓ₂ ℳ

⊢d∧<ₘ⇒⊢d : [ m₀ ]⊢[ m ]d d →
           m′ <ₘ m →
           ------------------
           [ m₀ ]⊢[ m′ ]d d
⊢d∧<ₘ⇒⊢d (valid m≤) <m = valid (≤-trans (<⇒≤ <m) m≤)
⊢d∧<ₘ⇒⊢d unusable   <m = unusable

⊢∧<ₘ⇒⊢ : ⊢[ m ] Γ →
         m₀ <ₘ m →
         -----------
         ⊢[ m₀ ] Γ
⊢∧<ₘ⇒⊢ []               <m = []
⊢∧<ₘ⇒⊢ ((⊢S , ⊢d) ∷ ⊢Γ) <m = (⊢S , ⊢d∧<ₘ⇒⊢d ⊢d <m) ∷ ⊢∧<ₘ⇒⊢ ⊢Γ <m

⊢d∧-~d⊞-⇒⊢d : [ m₀ ]⊢[ m ]d dS →
              dS [ m₀ ]~d dS₀ ⊞ dS₁ →
              --------------------------------------
              [ m₀ ]⊢[ m ]d dS₀ × [ m₀ ]⊢[ m ]d dS₁
⊢d∧-~d⊞-⇒⊢d ⊢d         (contraction Co∈m₀) = ⊢d , ⊢d
⊢d∧-~d⊞-⇒⊢d (valid m≤) to-left             = valid m≤ , unusable
⊢d∧-~d⊞-⇒⊢d (valid m≤) to-right            = unusable , valid m≤
⊢d∧-~d⊞-⇒⊢d ⊢d         unusable            = ⊢d , ⊢d

⊢∧-~⊞-⇒⊢ : ⊢[ m ] Γ →
           Γ ~ Γ₀ ⊞ Γ₁ →
           ----------------------
           ⊢[ m ] Γ₀ × ⊢[ m ] Γ₁
⊢∧-~⊞-⇒⊢ []        []        = [] , []
⊢∧-~⊞-⇒⊢ ((⊢S , ⊢d) ∷ ⊢Γ) (d~ ∷ Γ~)
  with ⊢d₀ , ⊢d₁ ← ⊢d∧-~d⊞-⇒⊢d ⊢d d~
     | ⊢Γ₀ , ⊢Γ₁ ← ⊢∧-~⊞-⇒⊢ ⊢Γ Γ~    = (⊢S , ⊢d₀) ∷ ⊢Γ₀ , (⊢S , ⊢d₁) ∷ ⊢Γ₁

⊢∧-~⊞-⇒⊢₀ : ⊢[ m ] Γ →
             Γ ~ Γ₀ ⊞ Γ₁ →
             --------------
             ⊢[ m ] Γ₀
⊢∧-~⊞-⇒⊢₀ ⊢Γ Γ~ = proj₁ (⊢∧-~⊞-⇒⊢ ⊢Γ Γ~)

⊢∧-~⊞-⇒⊢₁ : ⊢[ m ] Γ →
             Γ ~ Γ₀ ⊞ Γ₁ →
             --------------
             ⊢[ m ] Γ₁
⊢∧-~⊞-⇒⊢₁ ⊢Γ Γ~ = proj₂ (⊢∧-~⊞-⇒⊢ ⊢Γ Γ~)

⊢d∧∤d⇒⊢d : [ m₀ ]⊢[ m ]d d →
           d [ m₀ ]∤[ m′ ]d d′ →
           ----------------------
           [ m₀ ]⊢[ m′ ]d d′
⊢d∧∤d⇒⊢d ⊢d         (delete m′≰ dDel) = unusable
⊢d∧∤d⇒⊢d (valid m≤) (keep m′≤)        = valid m′≤
⊢d∧∤d⇒⊢d (unusable) (keep m′≤)        = unusable

⊢d∧≤⇒∤d : [ m₀ ]⊢[ m ]d d →
          m′ ≤ₘ m →
          d [ m₀ ]∤[ m′ ]d d
⊢d∧≤⇒∤d                (valid m≤) ≤m = keep (≤-trans ≤m m≤)
⊢d∧≤⇒∤d {m₀} {m′ = m′} unusable   ≤m
  with m′ ≤?ₘ m₀
...  | no  m′≰ = delete m′≰ unusable
...  | yes m′≤ = keep m′≤

⊢∧≤⇒∤ : ⊢[ m ] Γ →
        m′ ≤ₘ m →
        Γ ∤[ m′ ] Γ
⊢∧≤⇒∤ []               ≤m = []
⊢∧≤⇒∤ ((⊢S , ⊢d) ∷ ⊢Γ) ≤m = ⊢d∧≤⇒∤d ⊢d ≤m ∷ ⊢∧≤⇒∤ ⊢Γ ≤m

⊢∧∤⇒⊢ : ⊢[ m ] Γ →
        Γ ∤[ m₀ ] Γ′ →
        ----------------
        ⊢[ m₀ ] Γ′
⊢∧∤⇒⊢ []        []        = []
⊢∧∤⇒⊢ ((⊢S , ⊢d) ∷ ⊢Γ) (d∤ ∷ Γ∤) = (⊢S , ⊢d∧∤d⇒⊢d ⊢d d∤) ∷ ⊢∧∤⇒⊢ ⊢Γ Γ∤

⊢d∧Wk≤⇒is-del : [ m₀ ]⊢[ m ]d d →
                m′ ≤ₘ m →
                Bool.T (stₘ m′ ``Wk) →
                d [ m₀ ]is-del
⊢d∧Wk≤⇒is-del (valid m≤) m′≤ Wk∈m′ = weakening (isWellStructured _ _ ``Wk m≤ (isWellStructured _ _ ``Wk m′≤ Wk∈m′))
⊢d∧Wk≤⇒is-del unusable   m′≤ Wk∈m′ = unusable

⊢∧Wk≤⇒is-all-del : ⊢[ m ] Γ →
                   m′ ≤ₘ m →
                   Bool.T (stₘ m′ ``Wk) →
                   Γ is-all-del
⊢∧Wk≤⇒is-all-del []               m′≤ Wk∈m′ = []
⊢∧Wk≤⇒is-all-del ((⊢S , ⊢d) ∷ ⊢Γ) m′≤ Wk∈m′ = ⊢d∧Wk≤⇒is-del ⊢d m′≤ Wk∈m′ ∷ ⊢∧Wk≤⇒is-all-del ⊢Γ m′≤ Wk∈m′

left-bias-~d⊞ : ∀ m d →
                ∃ (λ d₁ → d [ m ]~d d ⊞ d₁)
left-bias-~d⊞ _ false = _ , unusable
left-bias-~d⊞ _ true  = _ , to-left

left-bias-~⊞ : ∀ Γ →
               ∃ (λ Γ₁ → Γ ~ Γ ⊞ Γ₁)
left-bias-~⊞ []                = _ , []
left-bias-~⊞ ((S , m , d) ∷ Γ)
  with _ , d~ ← left-bias-~d⊞ m d
     | _ , Γ~ ← left-bias-~⊞ Γ = _ , d~ ∷ Γ~

length-respects-~⊞ : Γ ~ Γ₀ ⊞ Γ₁ →
                     length Γ₀ ≡ length Γ × length Γ₁ ≡ length Γ
length-respects-~⊞ []       = refl , refl
length-respects-~⊞ (_ ∷ Γ~)
  with eq₀ , eq₁ ← length-respects-~⊞ Γ~
    rewrite eq₀
          | eq₁             = refl , refl

~d⊞-swap : d [ m ]~d d₀ ⊞ d₁ →
           d [ m ]~d d₁ ⊞ d₀
~d⊞-swap (contraction Co∈m) = contraction Co∈m
~d⊞-swap to-left            = to-right
~d⊞-swap to-right           = to-left
~d⊞-swap unusable           = unusable

~⊞-swap : Γ ~ Γ₀ ⊞ Γ₁ →
          Γ ~ Γ₁ ⊞ Γ₀
~⊞-swap []        = []
~⊞-swap (d~ ∷ Γ~) = ~d⊞-swap d~ ∷ ~⊞-swap Γ~

~⊞-preserves-++ : ∀ Δ →
                  Δ ++ Ψ ~ Γ₀ ⊞ Γ₁ →
                  ∃₂ (λ Δ₀ Δ₁ →
                    ∃₂ (λ Ψ₀ Ψ₁ → Γ₀ ≡ Δ₀ ++ Ψ₀ × Γ₁ ≡ Δ₁ ++ Ψ₁ × Δ ~ Δ₀ ⊞ Δ₁ × Ψ ~ Ψ₀ ⊞ Ψ₁))
~⊞-preserves-++ []      Ψ~                                           = _ , _ , _ , _ , refl , refl , [] , Ψ~
~⊞-preserves-++ (_ ∷ Δ) (d~ ∷ ΔΨ~)
  with _ , _ , _ , _ , refl , refl , Δ~ , Ψ~ ← ~⊞-preserves-++ Δ ΔΨ~ = _ , _ , _ , _ , refl , refl , d~ ∷ Δ~ , Ψ~

~⊞-++⁺ : Γ ~ Γ₀ ⊞ Γ₁ →
         Δ ~ Δ₀ ⊞ Δ₁ →
         Γ ++ Δ ~ Γ₀ ++ Δ₀ ⊞ Γ₁ ++ Δ₁
~⊞-++⁺ []        Δ~ = Δ~
~⊞-++⁺ (e~ ∷ Γ~) Δ~ = e~ ∷ ~⊞-++⁺ Γ~ Δ~

~d⊞-identityˡ : ∀ d →
                d [ m ]~d false ⊞ d
~d⊞-identityˡ false = unusable
~d⊞-identityˡ true = to-right

~d⊞-identityʳ : ∀ d →
                d [ m ]~d d ⊞ false
~d⊞-identityʳ false = unusable
~d⊞-identityʳ true  = to-left

~d⊞-assoc : d [ m ]~d d₀ ⊞ d₁ →
            d₀ [ m ]~d d₂ ⊞ d₃ →
            ∃ (λ d₁′ → d₁′ [ m ]~d d₃ ⊞ d₁ × d [ m ]~d d₂ ⊞ d₁′)
~d⊞-assoc d~              to-left            = _ , ~d⊞-identityˡ _ , d~
~d⊞-assoc d~              to-right           = _ , d~ , ~d⊞-identityˡ _
~d⊞-assoc d~              unusable           = _ , ~d⊞-identityˡ _ , d~
~d⊞-assoc (contraction _) (contraction Co∈m) = _ , contraction Co∈m , contraction Co∈m
~d⊞-assoc to-left         (contraction Co∈m) = _ , to-left , contraction Co∈m

~d⊞-contraction-assoc : d [ m₀ ]~d d₀ ⊞ d₁ →
                        d₀ [ m₀ ]~d d₂ ⊞ d₃ →
                        [ m₀ ]⊢[ m ]d d₁ →
                        Bool.T (stₘ m ``Co) →
                        ∃₂ (λ d₂′ d₃′ → d₂′ [ m₀ ]~d d₂ ⊞ d₁ × d₃′ [ m₀ ]~d d₃ ⊞ d₁ × d [ m₀ ]~d d₂′ ⊞ d₃′)
~d⊞-contraction-assoc (contraction Co∈m₀) (contraction _) ⊢d         Co∈m = _ , _ , contraction Co∈m₀ , contraction Co∈m₀ , contraction Co∈m₀
~d⊞-contraction-assoc (contraction Co∈m₀) to-left         ⊢d         Co∈m = _ , _ , contraction Co∈m₀ , to-right , contraction Co∈m₀
~d⊞-contraction-assoc (contraction Co∈m₀) to-right        ⊢d         Co∈m = _ , _ , to-right , contraction Co∈m₀ , contraction Co∈m₀
~d⊞-contraction-assoc to-left             d₀~             ⊢d         Co∈m = _ , _ , ~d⊞-identityʳ _ , ~d⊞-identityʳ _ , d₀~
~d⊞-contraction-assoc to-right            unusable        (valid m≤) Co∈m = _ , _ , to-right , to-right , contraction (isWellStructured _ _ ``Co m≤ Co∈m)
~d⊞-contraction-assoc unusable            d₀~             ⊢d         Co∈m = _ , _ , ~d⊞-identityʳ _ , ~d⊞-identityʳ _ , d₀~

~⊞-assoc : Γ ~ Γ₀ ⊞ Γ₁ →
           Γ₀ ~ Γ₂ ⊞ Γ₃ →
           ∃ (λ Γ₁′ → Γ₁′ ~ Γ₃ ⊞ Γ₁ × Γ ~ Γ₂ ⊞ Γ₁′)
~⊞-assoc [] [] = _ , [] , []
~⊞-assoc (d~ ∷ Γ~) (d₀~ ∷ Γ₀~)
  with _ , d₁′~ , d~′ ← ~d⊞-assoc d~ d₀~
     | _ , Γ₁′~ , Γ~′ ← ~⊞-assoc Γ~ Γ₀~ = _ , d₁′~ ∷ Γ₁′~ , d~′ ∷ Γ~′

~⊞-contraction-assoc : Γ ~ Γ₀ ⊞ Γ₁ →
                       Γ₀ ~ Γ₂ ⊞ Γ₃ →
                       ⊢[ m ] Γ₁ →
                       Bool.T (stₘ m ``Co) →
                       ∃₂ (λ Γ₂′ Γ₃′ → Γ₂′ ~ Γ₂ ⊞ Γ₁ × Γ₃′ ~ Γ₃ ⊞ Γ₁ × Γ ~ Γ₂′ ⊞ Γ₃′)
~⊞-contraction-assoc []        []          []          Co∈m = _ , _ , [] , [] , []
~⊞-contraction-assoc (d~ ∷ Γ~) (d₀~ ∷ Γ₀~) ((⊢S , ⊢d₁) ∷ ⊢Γ₁) Co∈m
  with _ , _ , d₂′~ , d₃′~ , d~′ ← ~d⊞-contraction-assoc d~ d₀~ ⊢d₁ Co∈m
     | _ , _ , Γ₂′~ , Γ₃′~ , Γ~′ ← ~⊞-contraction-assoc Γ~ Γ₀~ ⊢Γ₁ Co∈m = _ , _ , d₂′~ ∷ Γ₂′~ , d₃′~ ∷ Γ₃′~ , d~′ ∷ Γ~′

~d⊞-preserves-is-del : d [ m ]is-del →
                       d [ m ]~d d₀ ⊞ d₁ →
                       --------------------------------
                       d₀ [ m ]is-del × d₁ [ m ]is-del
~d⊞-preserves-is-del dDel (contraction Co∈m) = dDel , dDel
~d⊞-preserves-is-del dDel to-left            = dDel , unusable
~d⊞-preserves-is-del dDel to-right           = unusable , dDel
~d⊞-preserves-is-del dDel unusable           = dDel , dDel

~d⊞⁻¹-preserves-is-del : d₀ [ m ]is-del →
                         d₁ [ m ]is-del →
                         d [ m ]~d d₀ ⊞ d₁ →
                         --------------------
                         d [ m ]is-del
~d⊞⁻¹-preserves-is-del d₀Del d₁Del (contraction Co∈m) = d₀Del
~d⊞⁻¹-preserves-is-del d₀Del d₁Del to-left            = d₀Del
~d⊞⁻¹-preserves-is-del d₀Del d₁Del to-right           = d₁Del
~d⊞⁻¹-preserves-is-del d₀Del d₁Del unusable           = d₀Del

~⊞-preserves-is-all-del : Γ is-all-del →
                          Γ ~ Γ₀ ⊞ Γ₁ →
                          ------------------------------
                          Γ₀ is-all-del × Γ₁ is-all-del
~⊞-preserves-is-all-del []            []               = [] , []
~⊞-preserves-is-all-del (dDel ∷ ΓDel) (d~ ∷ Γ~)
  with d₀Del , d₁Del ← ~d⊞-preserves-is-del dDel d~
     | Γ₀Del , Γ₁Del ← ~⊞-preserves-is-all-del ΓDel Γ~ = d₀Del ∷ Γ₀Del , d₁Del ∷ Γ₁Del

~⊞⁻¹-preserves-is-all-del : Γ₀ is-all-del →
                            Γ₁ is-all-del →
                            Γ ~ Γ₀ ⊞ Γ₁ →
                            ----------------
                            Γ is-all-del
~⊞⁻¹-preserves-is-all-del []              []              []        = []
~⊞⁻¹-preserves-is-all-del (d₀Del ∷ Γ₀Del) (d₁Del ∷ Γ₁Del) (d~ ∷ Γ~) = ~d⊞⁻¹-preserves-is-del d₀Del d₁Del d~ ∷ ~⊞⁻¹-preserves-is-all-del Γ₀Del Γ₁Del Γ~

is-del⇒∤d : ∀ m →
            d [ m₀ ]is-del →
            ------------------------------------------------
            ∃ (λ d′ → d [ m₀ ]∤[ m ]d d′ × d′ [ m₀ ]is-del)
is-del⇒∤d {m₀ = m₀} m dDel
  with m ≤?ₘ m₀
...  | no  ≰m₀ = _ , delete ≰m₀ dDel , unusable
...  | yes ≤m₀ = _ , keep ≤m₀ , dDel

is-all-del⇒∤ : ∀ m →
               Γ is-all-del →
               ---------------------------------------
               ∃ (λ Γ′ → Γ ∤[ m ] Γ′ × Γ′ is-all-del)
is-all-del⇒∤ m []                   = _ , [] , []
is-all-del⇒∤ m (dDel ∷ ΓDel)
  with _ , d∤ , d′Del ← is-del⇒∤d m dDel
     | _ , Γ∤ , Γ′Del ← is-all-del⇒∤ m ΓDel = _ , d∤ ∷ Γ∤ , d′Del ∷ Γ′Del

∤d⇒~d⊞-is-del : d [ m₀ ]∤[ m ]d d′ →
                ------------------------------------------------
                ∃ (λ d₁ → d [ m₀ ]~d d′ ⊞ d₁ × d₁ [ m₀ ]is-del)
∤d⇒~d⊞-is-del (delete ≰m₀ dDel) = _ , ~d⊞-identityˡ _ , dDel
∤d⇒~d⊞-is-del (keep ≤m₀)        = _ , ~d⊞-identityʳ _ , unusable

∤⇒~⊞-is-del : Γ ∤[ m ] Γ′ →
              ---------------------------------------
              ∃ (λ Γ₁ → Γ ~ Γ′ ⊞ Γ₁ × Γ₁ is-all-del)
∤⇒~⊞-is-del []        = _ , [] , []
∤⇒~⊞-is-del (d∤ ∷ Γ∤)
  with _ , d~ , d₁Del ← ∤d⇒~d⊞-is-del d∤
     | _ , Γ~ , Γ₁Del ← ∤⇒~⊞-is-del Γ∤ = _ , d~ ∷ Γ~ , d₁Del ∷ Γ₁Del

length-respects-∤ : Γ ∤[ m ] Γ′ →
                    length Γ′ ≡ length Γ
length-respects-∤ []        = refl
length-respects-∤ (e∤ ∷ Γ∤) = cong suc (length-respects-∤ Γ∤)

∤d⁻¹-preserves-~d⊞ : d [ m₀ ]~d d₀ ⊞ d₁ →
                     d′ [ m₀ ]∤[ m ]d d → 
                     ∃₂ (λ d′₀ d′₁ → d′ [ m₀ ]~d d′₀ ⊞ d′₁ × d′₀ [ m₀ ]∤[ m ]d d₀ × d′₁ [ m₀ ]∤[ m ]d d₁)
∤d⁻¹-preserves-~d⊞ d~       (keep ≤m₀)                     = _ , _ , d~ , keep ≤m₀ , keep ≤m₀
∤d⁻¹-preserves-~d⊞ unusable (delete ≰m₀ unusable)          = _ , _ , unusable , delete ≰m₀ unusable , delete ≰m₀ unusable
∤d⁻¹-preserves-~d⊞ unusable (delete ≰m₀ (weakening Wk∈m₀)) = _ , _ , to-left , delete ≰m₀ (weakening Wk∈m₀) , delete ≰m₀ unusable -- arbitrary choice???

∤-preserves-++ : ∀ Δ →
                 Δ ++ Ψ ∤[ m ] Γ →
                 ∃₂ (λ Δ′ Ψ′ → Γ ≡ Δ′ ++ Ψ′ × Δ ∤[ m ] Δ′ × Ψ ∤[ m ] Ψ′)
∤-preserves-++ []      Ψ∤                            = _ , _ , refl , [] , Ψ∤
∤-preserves-++ (_ ∷ Δ) (d∤ ∷ ΔΨ∤)
  with _ , _ , refl , Δ∤ , Ψ∤ ← ∤-preserves-++ Δ ΔΨ∤ = _ , _ , refl , d∤ ∷ Δ∤ , Ψ∤

∤⁻¹-preserves-~⊞ : Γ ~ Γ₀ ⊞ Γ₁ →
                   Γ′ ∤[ m ] Γ → 
                   ∃₂ (λ Γ′₀ Γ′₁ → Γ′ ~ Γ′₀ ⊞ Γ′₁ × Γ′₀ ∤[ m ] Γ₀ × Γ′₁ ∤[ m ] Γ₁)
∤⁻¹-preserves-~⊞ []        []                             = _ , _ , [] , [] , []
∤⁻¹-preserves-~⊞ (d~ ∷ Γ~) (∤d ∷ ∤Γ)
  with _ , _ , Γ′~ , ∤Γ₀ , ∤Γ₁ ← ∤⁻¹-preserves-~⊞ Γ~ ∤Γ
     | _ , _ , d′~ , ∤d₀ , ∤d₁ ← ∤d⁻¹-preserves-~d⊞ d~ ∤d = _ , _ , d′~ ∷ Γ′~ , ∤d₀ ∷ ∤Γ₀ , ∤d₁ ∷ ∤Γ₁

~d⊞⁻¹-preserves-∤d : d₀ [ m₀ ]∤[ m ]d dS₀ → 
                     d₁ [ m₀ ]∤[ m ]d dS₁ → 
                     d [ m₀ ]~d d₀ ⊞ d₁ →
                     ∃ (λ dS → d [ m₀ ]∤[ m ]d dS × dS [ m₀ ]~d dS₀ ⊞ dS₁)
~d⊞⁻¹-preserves-∤d (delete m≰ d₀Del) (delete _  d₁Del) d~ = _ , delete m≰ (~d⊞⁻¹-preserves-is-del d₀Del d₁Del d~) , unusable
~d⊞⁻¹-preserves-∤d (delete m≰ d₀Del) (keep m≤)         d~ with () ← m≰ m≤
~d⊞⁻¹-preserves-∤d (keep m≤)         (delete m≰ d₁Del) d~ with () ← m≰ m≤
~d⊞⁻¹-preserves-∤d (keep m≤)         (keep _)          d~ = _ , keep m≤ , d~

~⊞⁻¹-preserves-∤ : Γ₀ ∤[ m ] Δ₀ → 
                   Γ₁ ∤[ m ] Δ₁ → 
                   Γ ~ Γ₀ ⊞ Γ₁ →
                   ∃ (λ Δ → Γ ∤[ m ] Δ × Δ ~ Δ₀ ⊞ Δ₁)
~⊞⁻¹-preserves-∤ []          []          [] = _ , [] , []
~⊞⁻¹-preserves-∤ (d₀∤ ∷ Γ₀∤) (d₁∤ ∷ Γ₁∤) (d~ ∷ Γ~)
  with _ , d∤ , dS~ ← ~d⊞⁻¹-preserves-∤d d₀∤ d₁∤ d~
     | _ , Γ∤ , Δ~ ← ~⊞⁻¹-preserves-∤ Γ₀∤ Γ₁∤ Γ~ = _ , d∤ ∷ Γ∤ , dS~ ∷ Δ~

assoc-∤d : d [ m₀ ]∤[ m ]d d′ →
           d′ [ m₀ ]∤[ m′ ]d d″ →
           ∃ (λ d‴ → d [ m₀ ]∤[ m′ ]d d‴ × d‴ [ m₀ ]∤[ m ]d d″)
assoc-∤d (delete m≰ eDel) (delete m₀≰ e′Del) = _ , delete m₀≰ eDel , delete m≰ e′Del
assoc-∤d (delete m≰ eDel) (keep m₀≤)         = _ , keep m₀≤ , delete m≰ eDel
assoc-∤d (keep m≤)        d′∤                = _ , d′∤ , keep m≤

assoc-∤ : Γ ∤[ m ] Γ′ →
          Γ′ ∤[ m₀ ] Γ″ →
          ∃ (λ Γ‴ → Γ ∤[ m₀ ] Γ‴ × Γ‴ ∤[ m ] Γ″)
assoc-∤ []        []          = _ , [] , []
assoc-∤ (d∤ ∷ Γ∤) (d′∤ ∷ Γ′∤)
  with _ , d∤′ , ∤d″ ← assoc-∤d d∤ d′∤
     | _ , Γ∤′ , ∤Γ″ ← assoc-∤ Γ∤ Γ′∤ = _ , d∤′ ∷ Γ∤′ , ∤d″ ∷ ∤Γ″

∤-++⁺ : Γ ∤[ m ] Γ′ →
        Δ ∤[ m ] Δ′ →
        Γ ++ Δ ∤[ m ] Γ′ ++ Δ′
∤-++⁺ []        Δ∤ = Δ∤
∤-++⁺ (e∤ ∷ Γ∤) Δ∤ = e∤ ∷ ∤-++⁺ Γ∤ Δ∤

∤d-preserves-is-del : d [ m₀ ]is-del →
                      d [ m₀ ]∤[ m ]d d′ →
                      ---------------------
                      d′ [ m₀ ]is-del
∤d-preserves-is-del dDel              (keep m≤)        = dDel
∤d-preserves-is-del unusable          (delete m≰ dDel) = dDel
∤d-preserves-is-del (weakening Wk∈m₀) (delete m≰ dDel) = unusable

∤d⁻¹-preserves-is-del : d′ [ m₀ ]is-del →
                        d [ m₀ ]∤[ m ]d d′ →
                        ---------------------
                        d [ m₀ ]is-del
∤d⁻¹-preserves-is-del dDel     (keep m≤)        = dDel
∤d⁻¹-preserves-is-del unusable (delete m≰ dDel) = dDel

∤-preserves-is-all-del : Γ is-all-del →
                         Γ ∤[ m ] Γ′ →
                         ---------------
                         Γ′ is-all-del
∤-preserves-is-all-del []            []        = []
∤-preserves-is-all-del (dDel ∷ ΓDel) (d∤ ∷ Γ∤) = ∤d-preserves-is-del dDel d∤ ∷ ∤-preserves-is-all-del ΓDel Γ∤

∤⁻¹-preserves-is-all-del : Γ′ is-all-del →
                           Γ ∤[ m ] Γ′ →
                           ----------------
                           Γ is-all-del
∤⁻¹-preserves-is-all-del []              []        = []
∤⁻¹-preserves-is-all-del (d′Del ∷ Γ′Del) (d∤ ∷ Γ∤) = ∤d⁻¹-preserves-is-del d′Del d∤ ∷ ∤⁻¹-preserves-is-all-del Γ′Del Γ∤

∤⁻¹-preserves-∈ : ∀ Δ →
                  x ⦂[ m ] S ∈ Δ ++ Γ′ →
                  Γ ∤[ m₀ ] Γ′ →
                  -----------------------
                  x ⦂[ m ] S ∈ Δ ++ Γ
∤⁻¹-preserves-∈ []      (here Γ′Del)    (keep _ ∷ Γ∤) = here (∤⁻¹-preserves-is-all-del Γ′Del Γ∤)
∤⁻¹-preserves-∈ []      (there dDel x∈) (d∤ ∷ Γ∤)     = there (∤d⁻¹-preserves-is-del dDel d∤) (∤⁻¹-preserves-∈ [] x∈ Γ∤)
∤⁻¹-preserves-∈ (_ ∷ Δ) (here ΔΓ′Del)   Γ∤            = here (All.++⁺ (All.++⁻ˡ Δ ΔΓ′Del) (∤⁻¹-preserves-is-all-del (All.++⁻ʳ Δ ΔΓ′Del) Γ∤))
∤⁻¹-preserves-∈ (_ ∷ Δ) (there dDel x∈) Γ∤            = there dDel (∤⁻¹-preserves-∈ Δ x∈ Γ∤)

∤⁻¹-preserves-⊢ : ∀ Δ →
                  Δ ++ Γ′ ⊢[ m ] L ⦂ S →
                  Γ ∤[ m₀ ] Γ′ →
                  -----------------------
                  Δ ++ Γ ⊢[ m ] L ⦂ S
∤⁻¹-preserves-⊢ Δ (`unit ΔΓ′Del)                          Γ∤ = `unit (All.++⁺ (All.++⁻ˡ Δ ΔΓ′Del) (∤⁻¹-preserves-is-all-del (All.++⁻ʳ Δ ΔΓ′Del) Γ∤))
∤⁻¹-preserves-⊢ Δ (`λ⦂-∘ ⊢L)                              Γ∤ = `λ⦂-∘ (∤⁻¹-preserves-⊢ (_ ∷ Δ) ⊢L Γ∤)
∤⁻¹-preserves-⊢ Δ (ΔΓ′~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)                  Γ∤
  with _ , _ , _ , _ , refl , refl , Δ~ , Γ′~ ← ~⊞-preserves-++ Δ ΔΓ′~
    with _ , _ , Γ~ , Γ₀∤ , Γ₁∤ ← ∤⁻¹-preserves-~⊞ Γ′~ Γ∤    = ~⊞-++⁺ Δ~ Γ~ ⊢ ∤⁻¹-preserves-⊢ _ ⊢L Γ₀∤ ⦂ ⊢⊸ `$ ∤⁻¹-preserves-⊢ _ ⊢M Γ₁∤
∤⁻¹-preserves-⊢ Δ (`lift[-⇒-] ⊢L)                         Γ∤ = `lift[-⇒-] ∤⁻¹-preserves-⊢ Δ ⊢L Γ∤
∤⁻¹-preserves-⊢ Δ (ΔΓ′∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)            Γ∤
  with _ , _ , refl , Δ∤ , Γ′∤ ← ∤-preserves-++ Δ ΔΓ′∤
    with _ , Γ∤′ , ∤Γ″ ← assoc-∤ Γ∤ Γ′∤                      = ∤-++⁺ Δ∤ Γ∤′ ⊢`unlift[-⇒-] ∤⁻¹-preserves-⊢ _ ⊢L ∤Γ″ ⦂ ⊢↑
∤⁻¹-preserves-⊢ Δ (ΔΓ′∤ ⊢`return[-⇒-] ⊢L)                 Γ∤
  with _ , _ , refl , Δ∤ , Γ′∤ ← ∤-preserves-++ Δ ΔΓ′∤
    with _ , Γ∤′ , ∤Γ″ ← assoc-∤ Γ∤ Γ′∤                      = ∤-++⁺ Δ∤ Γ∤′ ⊢`return[-⇒-] ∤⁻¹-preserves-⊢ _ ⊢L ∤Γ″
∤⁻¹-preserves-⊢ Δ (ΔΓ′~ ⊢`let-return[-⇒-] ⊢L ⦂ ⊢↓ `in ⊢M) Γ∤
  with _ , _ , _ , _ , refl , refl , Δ~ , Γ′~ ← ~⊞-preserves-++ Δ ΔΓ′~
    with _ , _ , Γ~ , Γ₀∤ , Γ₁∤ ← ∤⁻¹-preserves-~⊞ Γ′~ Γ∤    = ~⊞-++⁺ Δ~ Γ~ ⊢`let-return[-⇒-] ∤⁻¹-preserves-⊢ _ ⊢L Γ₀∤ ⦂ ⊢↓ `in ∤⁻¹-preserves-⊢ _ ⊢M Γ₁∤
∤⁻¹-preserves-⊢ Δ (`# x∈)                                 Γ∤ = `# ∤⁻¹-preserves-∈ Δ x∈ Γ∤

∈⇒+-∈-++ : Ψ is-all-del →
           x ⦂[ m ] S ∈ Γ →
           length Ψ + x ⦂[ m ] S ∈ Ψ ++ Γ
∈⇒+-∈-++ []            x∈ = x∈
∈⇒+-∈-++ (eDel ∷ ΨDel) x∈ = there eDel (∈⇒+-∈-++ ΨDel x∈)

<∧∈-++⇒∈-++-++ : ∀ Δ →
                 Ψ is-all-del →
                 x ⦂[ m ] S ∈ Δ ++ Γ →
                 x ℕ.< length Δ →
                 x ⦂[ m ] S ∈ Δ ++ Ψ ++ Γ
<∧∈-++⇒∈-++-++ (_ ∷ Δ) ΨDel (here ΔΓDel)    x<       = here (All.++⁺ (All.++⁻ˡ Δ ΔΓDel) (All.++⁺ ΨDel (All.++⁻ʳ Δ ΔΓDel)))
<∧∈-++⇒∈-++-++ (e ∷ Δ) ΨDel (there eDel x∈) (s≤s x<) = there eDel (<∧∈-++⇒∈-++-++ Δ ΨDel x∈ x<)

≥∧∈-++⇒+-∈-++-++ : ∀ Δ →
                   Ψ is-all-del →
                   x ⦂[ m ] S ∈ Δ ++ Γ →
                   x ℕ.≥ length Δ →
                   length Ψ + x ⦂[ m ] S ∈ Δ ++ Ψ ++ Γ
≥∧∈-++⇒+-∈-++-++                     []      ΨDel x∈              x≥       = ∈⇒+-∈-++ ΨDel x∈
≥∧∈-++⇒+-∈-++-++ {Ψ = Ψ} {x = suc x} (e ∷ Δ) ΨDel (there eDel x∈) (s≤s x≥)
  rewrite ℕ.+-suc (length Ψ) x                                             = there eDel (≥∧∈-++⇒+-∈-++-++ Δ ΨDel x∈ x≥)

len∈-inversion : ∀ Δ →
                 length Δ ⦂[ m ] S ∈ Δ ++ (T , m₀ , d) ∷ Γ →
                 (Δ ++ Γ) is-all-del × T ≡ S × m₀ ≡ m × d ≡ true
len∈-inversion []      (here ΓDel) = ΓDel , refl , refl , refl
len∈-inversion (_ ∷ Δ) (there dDel lenΔ∈)
  with ΔΓDel , refl , refl , refl ← len∈-inversion Δ lenΔ∈ = dDel ∷ ΔΓDel , refl , refl , refl

<∧∈-++-++⇒∈-++ : ∀ Δ Γ →
                 x ⦂[ m ] T ∈ Δ ++ Γ ++ Ψ →
                 x ℕ.< length Δ →
                 x ⦂[ m ] T ∈ Δ ++ Ψ
<∧∈-++-++⇒∈-++ (_ ∷ Δ) Γ (here ΔΓΨDel)   x<       = here (All.++⁺ (All.++⁻ˡ Δ ΔΓΨDel) (All.++⁻ʳ Γ (All.++⁻ʳ Δ ΔΓΨDel)))
<∧∈-++-++⇒∈-++ (_ ∷ Δ) Γ (there dDel x∈) (s≤s x<) = there dDel (<∧∈-++-++⇒∈-++ Δ Γ x∈ x<)

≥∧∈-++⇒∈ : ∀ Δ →
           x ⦂[ m ] T ∈ Δ ++ Ψ →
           x ℕ.≥ length Δ →
           x ℕ.∸ length Δ ⦂[ m ] T ∈ Ψ
≥∧∈-++⇒∈ []      x∈           x≥       = x∈
≥∧∈-++⇒∈ (_ ∷ Δ) (there _ x∈) (s≤s x≥) = ≥∧∈-++⇒∈ Δ x∈ x≥

≥∧∈-++-++⇒∈-++ : ∀ Δ Γ →
                 x ⦂[ m ] T ∈ Δ ++ Γ ++ Ψ →
                 x ℕ.≥ length Δ + length Γ →
                 x ℕ.∸ length Γ ⦂[ m ] T ∈ Δ ++ Ψ
≥∧∈-++-++⇒∈-++ []      Γ x∈              x≥         = ≥∧∈-++⇒∈ Γ x∈ x≥
≥∧∈-++-++⇒∈-++ (_ ∷ Δ) Γ (there dDel x∈) (s≤s x≥)
  rewrite ℕ.+-∸-assoc 1 (ℕ.m+n≤o⇒n≤o (length Δ) x≥) = there dDel (≥∧∈-++-++⇒∈-++ Δ Γ x∈ x≥)

<∧∈-++⇒is-all-del : ∀ Δ →
                    x ⦂[ m ] T ∈ Δ ++ Ψ →
                    x ℕ.< length Δ →
                    Ψ is-all-del
<∧∈-++⇒is-all-del (_ ∷ Δ) (T.here ΔΨDel) x<       = All.++⁻ʳ Δ ΔΨDel
<∧∈-++⇒is-all-del (_ ∷ Δ) (T.there _ x∈) (s≤s x<) = <∧∈-++⇒is-all-del Δ x∈ x<

≥∧∈-++⇒is-all-del : ∀ Δ →
                    x ⦂[ m ] T ∈ Δ ++ Ψ →
                    x ℕ.≥ length Δ →
                    Δ is-all-del
≥∧∈-++⇒is-all-del []      x∈              x≥       = []
≥∧∈-++⇒is-all-del (_ ∷ Δ) (there dDel x∈) (s≤s x≥) = dDel ∷ ≥∧∈-++⇒is-all-del Δ x∈ x≥
