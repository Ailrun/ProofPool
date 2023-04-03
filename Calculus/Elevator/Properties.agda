open import Calculus.Elevator.ModeSpec

module Calculus.Elevator.Properties ℓ₁ ℓ₂ (ℳ : ModeSpec ℓ₁ ℓ₂) where
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

⊢e∧<ₘ⇒⊢e : ⊢[ m ]e e →
           m₀ <ₘ m →
           ----------------
           ⊢[ m₀ ]e e
⊢e∧<ₘ⇒⊢e (valid ⊢S m≤) <m = valid ⊢S (≤-trans (<⇒≤ <m) m≤)
⊢e∧<ₘ⇒⊢e (unusable ⊢S) <m = unusable ⊢S

⊢∧<ₘ⇒⊢ : ⊢[ m ] Γ →
         m₀ <ₘ m →
         ----------------
         ⊢[ m₀ ] Γ
⊢∧<ₘ⇒⊢ []        <m = []
⊢∧<ₘ⇒⊢ (⊢e ∷ ⊢Γ) <m = ⊢e∧<ₘ⇒⊢e ⊢e <m ∷ ⊢∧<ₘ⇒⊢ ⊢Γ <m

⊢e∧-~e⊞-⇒⊢e : ⊢[ m ]e e →
              e ~e e₀ ⊞ e₁ →
              ------------------------
              ⊢[ m ]e e₀ × ⊢[ m ]e e₁
⊢e∧-~e⊞-⇒⊢e (valid ⊢S m≤) (contraction Co∈m₀) = valid ⊢S m≤ , valid ⊢S m≤
⊢e∧-~e⊞-⇒⊢e (valid ⊢S m≤) to-left             = valid ⊢S m≤ , unusable ⊢S
⊢e∧-~e⊞-⇒⊢e (valid ⊢S m≤) to-right            = unusable ⊢S , valid ⊢S m≤
⊢e∧-~e⊞-⇒⊢e (unusable ⊢S) unusable            = unusable ⊢S , unusable ⊢S

⊢∧-~⊞-⇒⊢ : ⊢[ m ] Γ →
           Γ ~ Γ₀ ⊞ Γ₁ →
           ----------------------
           ⊢[ m ] Γ₀ × ⊢[ m ] Γ₁
⊢∧-~⊞-⇒⊢ []        []                = [] , []
⊢∧-~⊞-⇒⊢ (⊢e ∷ ⊢Γ) (e~ ∷ Γ~)
  with ⊢e₀ , ⊢e₁ ← ⊢e∧-~e⊞-⇒⊢e ⊢e e~
     | ⊢Γ₀ , ⊢Γ₁ ← ⊢∧-~⊞-⇒⊢ ⊢Γ Γ~    = ⊢e₀ ∷ ⊢Γ₀ , ⊢e₁ ∷ ⊢Γ₁

⊢∧-~⊞-⇒⊢₀ : ⊢[ m ] Γ →
             Γ ~ Γ₀ ⊞ Γ₁ →
             ----------------
             ⊢[ m ] Γ₀
⊢∧-~⊞-⇒⊢₀ ⊢Γ Γ~ = proj₁ (⊢∧-~⊞-⇒⊢ ⊢Γ Γ~)

⊢∧-~⊞-⇒⊢₁ : ⊢[ m ] Γ →
             Γ ~ Γ₀ ⊞ Γ₁ →
             ----------------
             ⊢[ m ] Γ₁
⊢∧-~⊞-⇒⊢₁ ⊢Γ Γ~ = proj₂ (⊢∧-~⊞-⇒⊢ ⊢Γ Γ~)

⊢e∧∤e⇒⊢e : ⊢[ m ]e e →
           e ∤[ m₀ ]e e′ →
           ----------------
           ⊢[ m₀ ]e e′
⊢e∧∤e⇒⊢e (valid ⊢S m≤) (delete m₀≰ eDel) = unusable ⊢S
⊢e∧∤e⇒⊢e (valid ⊢S m≤) (keep m₀≤)        = valid ⊢S m₀≤
⊢e∧∤e⇒⊢e (unusable ⊢S) (delete m₀≰ eDel) = unusable ⊢S
⊢e∧∤e⇒⊢e (unusable ⊢S) (keep m₀≤)        = unusable ⊢S

⊢∧∤⇒⊢ : ⊢[ m ] Γ →
        Γ ∤[ m₀ ] Γ′ →
        ----------------
        ⊢[ m₀ ] Γ′
⊢∧∤⇒⊢ []        []        = []
⊢∧∤⇒⊢ (⊢e ∷ ⊢Γ) (e∤ ∷ Γ∤) = ⊢e∧∤e⇒⊢e ⊢e e∤ ∷ ⊢∧∤⇒⊢ ⊢Γ Γ∤

left-bias-~e⊞ : ∀ e →
                ∃ (λ e₁ → e ~e e ⊞ e₁)
left-bias-~e⊞ (S , m , false) = _ , unusable
left-bias-~e⊞ (S , m , true)  = _ , to-left

left-bias-~⊞ : ∀ Γ →
               ∃ (λ Γ₁ → Γ ~ Γ ⊞ Γ₁)
left-bias-~⊞ []      = _ , []
left-bias-~⊞ (e ∷ Γ)
  with _ , e~ ← left-bias-~e⊞ e
     | _ , Γ~ ← left-bias-~⊞ Γ = _ , e~ ∷ Γ~

length-respects-~⊞ : Γ ~ Γ₀ ⊞ Γ₁ →
                     length Γ₀ ≡ length Γ × length Γ₁ ≡ length Γ
length-respects-~⊞ []       = refl , refl
length-respects-~⊞ (_ ∷ Γ~)
  with eq₀ , eq₁ ← length-respects-~⊞ Γ~
    rewrite eq₀
          | eq₁             = refl , refl

swap-~e⊞ : e ~e e₀ ⊞ e₁ →
           e ~e e₁ ⊞ e₀
swap-~e⊞ (contraction Co∈m) = contraction Co∈m
swap-~e⊞ to-left            = to-right
swap-~e⊞ to-right           = to-left
swap-~e⊞ unusable           = unusable

swap-~⊞ : Γ ~ Γ₀ ⊞ Γ₁ →
          Γ ~ Γ₁ ⊞ Γ₀
swap-~⊞ []        = []
swap-~⊞ (e~ ∷ Γ~) = swap-~e⊞ e~ ∷ swap-~⊞ Γ~

~⊞-preserves-++ : ∀ Δ →
                  Δ ++ Ψ ~ Γ₀ ⊞ Γ₁ →
                  ∃₂ (λ Δ₀ Δ₁ →
                    ∃₂ (λ Ψ₀ Ψ₁ → Γ₀ ≡ Δ₀ ++ Ψ₀ × Γ₁ ≡ Δ₁ ++ Ψ₁ × Δ ~ Δ₀ ⊞ Δ₁ × Ψ ~ Ψ₀ ⊞ Ψ₁))
~⊞-preserves-++ []      Ψ~          = _ , _ , _ , _ , refl , refl , [] , Ψ~
~⊞-preserves-++ (e ∷ Δ) (e~ ∷ ΔΨ~)
  with _ , _ , _ , _ , refl , refl , Δ~ , Ψ~ ← ~⊞-preserves-++ Δ ΔΨ~ = _ , _ , _ , _ , refl , refl , e~ ∷ Δ~ , Ψ~

++-mono-~⊞ : Γ ~ Γ₀ ⊞ Γ₁ →
             Δ ~ Δ₀ ⊞ Δ₁ →
             Γ ++ Δ ~ Γ₀ ++ Δ₀ ⊞ Γ₁ ++ Δ₁
++-mono-~⊞ []        Δ~ = Δ~
++-mono-~⊞ (e~ ∷ Γ~) Δ~ = e~ ∷ ++-mono-~⊞ Γ~ Δ~

~e⊞-preserves-is-deletable : e is-deletable →
                             e ~e e₀ ⊞ e₁ →
                             e₀ is-deletable × e₁ is-deletable
~e⊞-preserves-is-deletable eDel (contraction Co∈m) = eDel , eDel
~e⊞-preserves-is-deletable eDel to-left            = eDel , unusable
~e⊞-preserves-is-deletable eDel to-right           = unusable , eDel
~e⊞-preserves-is-deletable eDel unusable           = eDel , eDel

~e⊞-backward-preserves-is-deletable : e₀ is-deletable →
                                      e₁ is-deletable →
                                      e ~e e₀ ⊞ e₁ →
                                      e is-deletable
~e⊞-backward-preserves-is-deletable e₀Del e₁Del (contraction Co∈m) = e₀Del
~e⊞-backward-preserves-is-deletable e₀Del e₁Del to-left            = e₀Del
~e⊞-backward-preserves-is-deletable e₀Del e₁Del to-right           = e₁Del
~e⊞-backward-preserves-is-deletable e₀Del e₁Del unusable           = e₀Del

~⊞-preserves-is-all-deletable : Γ is-all-deletable →
                                Γ ~ Γ₀ ⊞ Γ₁ →
                                Γ₀ is-all-deletable × Γ₁ is-all-deletable
~⊞-preserves-is-all-deletable []            []               = [] , []
~⊞-preserves-is-all-deletable (eDel ∷ ΓDel) (e~ ∷ Γ~)
  with e₀Del , e₁Del ← ~e⊞-preserves-is-deletable eDel e~
     | Γ₀Del , Γ₁Del ← ~⊞-preserves-is-all-deletable ΓDel Γ~ = e₀Del ∷ Γ₀Del , e₁Del ∷ Γ₁Del

~⊞-backward-preserves-is-all-deletable : Γ₀ is-all-deletable →
                                         Γ₁ is-all-deletable →
                                         Γ ~ Γ₀ ⊞ Γ₁ →
                                         Γ is-all-deletable
~⊞-backward-preserves-is-all-deletable []              []              []        = []
~⊞-backward-preserves-is-all-deletable (e₀Del ∷ Γ₀Del) (e₁Del ∷ Γ₁Del) (e~ ∷ Γ~) = ~e⊞-backward-preserves-is-deletable e₀Del e₁Del e~ ∷ ~⊞-backward-preserves-is-all-deletable Γ₀Del Γ₁Del Γ~

is-deletable⇒∤e : ∀ m →
                  e is-deletable →
                  ∃ (λ e′ → e ∤[ m ]e e′)
is-deletable⇒∤e {_ , m₀ , _} m eDel
  with m ≤?ₘ m₀
...  | no  ≰m₀ = _ , delete ≰m₀ eDel
...  | yes ≤m₀ = _ , keep ≤m₀

is-all-deletable⇒∤ : ∀ m →
                     Γ is-all-deletable →
                     ∃ (λ Γ′ → Γ ∤[ m ] Γ′)
is-all-deletable⇒∤ m []                   = _ , []
is-all-deletable⇒∤ m (eDel ∷ ΓDel)
  with _ , e∤ ← is-deletable⇒∤e m eDel
     | _ , Γ∤ ← is-all-deletable⇒∤ m ΓDel = _ , e∤ ∷ Γ∤

length-respects-∤ : Γ ∤[ m ] Γ′ →
                    length Γ′ ≡ length Γ
length-respects-∤ []        = refl
length-respects-∤ (e∤ ∷ Γ∤) = cong suc (length-respects-∤ Γ∤)

∤e-backward-preserves-~e⊞ : e ~e e₀ ⊞ e₁ →
                            e′ ∤[ m ]e e → 
                            ∃₂ (λ e′₀ e′₁ → e′ ~e e′₀ ⊞ e′₁ × e′₀ ∤[ m ]e e₀ × e′₁ ∤[ m ]e e₁)
∤e-backward-preserves-~e⊞ (contraction Co∈m) (keep ≤m)                    = _ , _ , contraction Co∈m , keep ≤m , keep ≤m
∤e-backward-preserves-~e⊞ to-left            (keep ≤m)                    = _ , _ , to-left , keep ≤m , keep ≤m
∤e-backward-preserves-~e⊞ to-right           (keep ≤m)                    = _ , _ , to-right , keep ≤m , keep ≤m
∤e-backward-preserves-~e⊞ unusable           (delete ≰m unusable)         = _ , _ , unusable , delete ≰m unusable , delete ≰m unusable
∤e-backward-preserves-~e⊞ unusable           (delete ≰m (weakening Wk∈m)) = _ , _ , to-left , delete ≰m (weakening Wk∈m) , delete ≰m unusable -- arbitrary choice???
∤e-backward-preserves-~e⊞ unusable           (keep ≤m)                    = _ , _ , unusable , keep ≤m , keep ≤m

∤-preserves-++ : ∀ Δ →
                 Δ ++ Ψ ∤[ m ] Γ →
                 ∃₂ (λ Δ′ Ψ′ → Γ ≡ Δ′ ++ Ψ′ × Δ ∤[ m ] Δ′ × Ψ ∤[ m ] Ψ′)
∤-preserves-++ []      Ψ∤ = _ , _ , refl , [] , Ψ∤
∤-preserves-++ (e ∷ Δ) (e∤ ∷ ΔΨ∤)
  with _ , _ , refl , Δ∤ , Ψ∤ ← ∤-preserves-++ Δ ΔΨ∤ = _ , _ , refl , e∤ ∷ Δ∤ , Ψ∤

∤-backward-preserves-~⊞ : Γ ~ Γ₀ ⊞ Γ₁ →
                          Γ′ ∤[ m ] Γ → 
                          ∃₂ (λ Γ′₀ Γ′₁ → Γ′ ~ Γ′₀ ⊞ Γ′₁ × Γ′₀ ∤[ m ] Γ₀ × Γ′₁ ∤[ m ] Γ₁)
∤-backward-preserves-~⊞ []        []        = _ , _ , [] , [] , []
∤-backward-preserves-~⊞ (e~ ∷ Γ~) (∤e ∷ ∤Γ)
  with _ , _ , Γ′~ , ∤Γ₀ , ∤Γ₁ ← ∤-backward-preserves-~⊞ Γ~ ∤Γ
     | _ , _ , e′~ , ∤e₀ , ∤e₁ ← ∤e-backward-preserves-~e⊞ e~ ∤e = _ , _ , e′~ ∷ Γ′~ , ∤e₀ ∷ ∤Γ₀ , ∤e₁ ∷ ∤Γ₁

assoc-∤e : e ∤[ m ]e e′ →
           e′ ∤[ m₀ ]e e″ →
           ∃ (λ e‴ → e ∤[ m₀ ]e e‴ × e‴ ∤[ m ]e e″)
assoc-∤e (delete m≰ eDel)  (delete m₀≰ e′Del) = _ , delete m₀≰ eDel , delete m≰ e′Del
assoc-∤e (delete m≰ eDel)  (keep m₀≤)         = _ , keep m₀≤ , delete m≰ eDel
assoc-∤e (keep m≤)         (delete m₀≰ e′Del) = _ , delete m₀≰ e′Del , keep m≤
assoc-∤e (keep m≤)         (keep m₀≤)         = _ , keep m₀≤ , keep m≤

assoc-∤ : Γ ∤[ m ] Γ′ →
          Γ′ ∤[ m₀ ] Γ″ →
          ∃ (λ Γ‴ → Γ ∤[ m₀ ] Γ‴ × Γ‴ ∤[ m ] Γ″)
assoc-∤ []        [] = _ , [] , []
assoc-∤ (e∤ ∷ Γ∤) (e′∤ ∷ Γ′∤)
  with _ , e∤′ , ∤e″ ← assoc-∤e e∤ e′∤
     | _ , Γ∤′ , ∤Γ″ ← assoc-∤ Γ∤ Γ′∤ = _ , e∤′ ∷ Γ∤′ , ∤e″ ∷ ∤Γ″

++-mono-∤ : Γ ∤[ m ] Γ′ →
            Δ ∤[ m ] Δ′ →
            Γ ++ Δ ∤[ m ] Γ′ ++ Δ′
++-mono-∤ []        Δ∤ = Δ∤
++-mono-∤ (e∤ ∷ Γ∤) Δ∤ = e∤ ∷ ++-mono-∤ Γ∤ Δ∤

∤e-preserves-is-deletable : e is-deletable →
                            e ∤[ m ]e e′ →
                            e′ is-deletable
∤e-preserves-is-deletable eDel              (keep m≤)        = eDel
∤e-preserves-is-deletable unusable          (delete m≰ eDel) = eDel
∤e-preserves-is-deletable (weakening Wk∈m₀) (delete m≰ eDel) = unusable

∤e-backward-preserves-is-deletable : e′ is-deletable →
                                     e ∤[ m ]e e′ →
                                     e is-deletable
∤e-backward-preserves-is-deletable unusable          (delete m≰ eDel) = eDel
∤e-backward-preserves-is-deletable unusable          (keep m≤)        = unusable
∤e-backward-preserves-is-deletable (weakening Wk∈m₀) (keep m≤)        = weakening Wk∈m₀

∤-preserves-is-all-deletable : Γ is-all-deletable →
                               Γ ∤[ m ] Γ′ →
                               ---------------------
                               Γ′ is-all-deletable
∤-preserves-is-all-deletable []            []        = []
∤-preserves-is-all-deletable (eDel ∷ ΓDel) (e∤ ∷ Γ∤) = ∤e-preserves-is-deletable eDel e∤ ∷ ∤-preserves-is-all-deletable ΓDel Γ∤

∤-backward-preserves-is-all-deletable : Γ′ is-all-deletable →
                                        Γ ∤[ m ] Γ′ →
                                        ----------------------
                                        Γ is-all-deletable
∤-backward-preserves-is-all-deletable []              []        = []
∤-backward-preserves-is-all-deletable (e′Del ∷ Γ′Del) (e∤ ∷ Γ∤) = ∤e-backward-preserves-is-deletable e′Del e∤ ∷ ∤-backward-preserves-is-all-deletable Γ′Del Γ∤

∤-backward-preserves-∈ : ∀ Δ →
                         x ⦂[ m ] S ∈ Δ ++ Γ′ →
                         Γ ∤[ m₀ ] Γ′ →
                         -----------------------
                         x ⦂[ m ] S ∈ Δ ++ Γ
∤-backward-preserves-∈ []      (here Γ′Del)    (keep _ ∷ Γ∤) = here (∤-backward-preserves-is-all-deletable Γ′Del Γ∤)
∤-backward-preserves-∈ []      (there eDel x∈) (e∤ ∷ Γ∤)     = there (∤e-backward-preserves-is-deletable eDel e∤) (∤-backward-preserves-∈ [] x∈ Γ∤)
∤-backward-preserves-∈ (e ∷ Δ) (here ΔΓ′Del)   Γ∤            = here (All.++⁺ (All.++⁻ˡ Δ ΔΓ′Del) (∤-backward-preserves-is-all-deletable (All.++⁻ʳ Δ ΔΓ′Del) Γ∤))
∤-backward-preserves-∈ (e ∷ Δ) (there eDel x∈) Γ∤            = there eDel (∤-backward-preserves-∈ Δ x∈ Γ∤)

∤-backward-preserves-⊢ : ∀ Δ →
                         Δ ++ Γ′ ⊢[ m ] L ⦂ S →
                         Γ ∤[ m₀ ] Γ′ →
                         -----------------------
                         Δ ++ Γ ⊢[ m ] L ⦂ S
∤-backward-preserves-⊢ Δ (`unit ΔΓ′Del)                          Γ∤ = `unit (All.++⁺ (All.++⁻ˡ Δ ΔΓ′Del) (∤-backward-preserves-is-all-deletable (All.++⁻ʳ Δ ΔΓ′Del) Γ∤))
∤-backward-preserves-⊢ Δ (`λ⦂-∘ ⊢L)                              Γ∤ = `λ⦂-∘ (∤-backward-preserves-⊢ (_ ∷ Δ) ⊢L Γ∤)
∤-backward-preserves-⊢ Δ (ΔΓ′~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)                  Γ∤
  with _ , _ , _ , _ , refl , refl , Δ~ , Γ′~ ← ~⊞-preserves-++ Δ ΔΓ′~
    with _ , _ , Γ~ , Γ₀∤ , Γ₁∤ ← ∤-backward-preserves-~⊞ Γ′~ Γ∤    = ++-mono-~⊞ Δ~ Γ~ ⊢ ∤-backward-preserves-⊢ _ ⊢L Γ₀∤ ⦂ ⊢⊸ `$ ∤-backward-preserves-⊢ _ ⊢M Γ₁∤
∤-backward-preserves-⊢ Δ (`lift[-⇒-] ⊢L)                         Γ∤ = `lift[-⇒-] ∤-backward-preserves-⊢ Δ ⊢L Γ∤
∤-backward-preserves-⊢ Δ (ΔΓ′∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)            Γ∤
  with _ , _ , refl , Δ∤ , Γ′∤ ← ∤-preserves-++ Δ ΔΓ′∤
    with _ , Γ∤′ , ∤Γ″ ← assoc-∤ Γ∤ Γ′∤                              = ++-mono-∤ Δ∤ Γ∤′ ⊢`unlift[-⇒-] ∤-backward-preserves-⊢ _ ⊢L ∤Γ″ ⦂ ⊢↑
∤-backward-preserves-⊢ Δ (ΔΓ′∤ ⊢`return[-⇒-] ⊢L)                 Γ∤
  with _ , _ , refl , Δ∤ , Γ′∤ ← ∤-preserves-++ Δ ΔΓ′∤
    with _ , Γ∤′ , ∤Γ″ ← assoc-∤ Γ∤ Γ′∤                              = ++-mono-∤ Δ∤ Γ∤′ ⊢`return[-⇒-] ∤-backward-preserves-⊢ _ ⊢L ∤Γ″
∤-backward-preserves-⊢ Δ (ΔΓ′~ ⊢`let-return[-⇒-] ⊢L ⦂ ⊢↓ `in ⊢M) Γ∤
  with _ , _ , _ , _ , refl , refl , Δ~ , Γ′~ ← ~⊞-preserves-++ Δ ΔΓ′~
    with _ , _ , Γ~ , Γ₀∤ , Γ₁∤ ← ∤-backward-preserves-~⊞ Γ′~ Γ∤    = ++-mono-~⊞ Δ~ Γ~ ⊢`let-return[-⇒-] ∤-backward-preserves-⊢ _ ⊢L Γ₀∤ ⦂ ⊢↓ `in ∤-backward-preserves-⊢ _ ⊢M Γ₁∤
∤-backward-preserves-⊢ Δ (`# x∈)                                 Γ∤ = `# ∤-backward-preserves-∈ Δ x∈ Γ∤

∈⇒+-∈-++ : Ψ is-all-deletable →
           x ⦂[ m ] S ∈ Γ →
           length Ψ + x ⦂[ m ] S ∈ Ψ ++ Γ
∈⇒+-∈-++ []            x∈ = x∈
∈⇒+-∈-++ (eDel ∷ ΨDel) x∈ = there eDel (∈⇒+-∈-++ ΨDel x∈)

<∧∈-++⇒∈-++-++ : ∀ Δ →
                     Ψ is-all-deletable →
                     x ⦂[ m ] S ∈ Δ ++ Γ →
                     x ℕ.< length Δ →
                     x ⦂[ m ] S ∈ Δ ++ Ψ ++ Γ
<∧∈-++⇒∈-++-++ (_ ∷ Δ) ΨDel (here ΔΓDel)    x<       = here (All.++⁺ (All.++⁻ˡ Δ ΔΓDel) (All.++⁺ ΨDel (All.++⁻ʳ Δ ΔΓDel)))
<∧∈-++⇒∈-++-++ (e ∷ Δ) ΨDel (there eDel x∈) (s≤s x<) = there eDel (<∧∈-++⇒∈-++-++ Δ ΨDel x∈ x<)

≥∧∈-++⇒+-∈-++-++ : ∀ Δ →
                   Ψ is-all-deletable →
                   x ⦂[ m ] S ∈ Δ ++ Γ →
                   x ℕ.≥ length Δ →
                   length Ψ + x ⦂[ m ] S ∈ Δ ++ Ψ ++ Γ
≥∧∈-++⇒+-∈-++-++                     []      ΨDel x∈              x≥       = ∈⇒+-∈-++ ΨDel x∈
≥∧∈-++⇒+-∈-++-++ {Ψ = Ψ} {x = suc x} (e ∷ Δ) ΨDel (there eDel x∈) (s≤s x≥)
  rewrite ℕ.+-suc (length Ψ) x                                             = there eDel (≥∧∈-++⇒+-∈-++-++ Δ ΨDel x∈ x≥)

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
       | _    , eqΨ₁ ← length-respects-~⊞ Ψ~ = ΔΨΓ~ ⊢ ⊢L′ ⦂ ⊢⊸ `$ ⊢M′
  where
    ΔΨΓ~ = ++-mono-~⊞ Δ~ (++-mono-~⊞ Ψ~ Γ~)

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
     | Ψ′ , Ψ∤ ← is-all-deletable⇒∤ m₀ ΨDel
    with eqΔ′ ← length-respects-∤ Δ∤
       | eqΨ′ ← length-respects-∤ Ψ∤ = ΔΨΓ∤ ⊢`unlift[-⇒-] ⊢L′ ⦂ ⊢↑
  where
    ΔΨΓ∤ = ++-mono-∤ Δ∤ (++-mono-∤ Ψ∤ Γ∤)

    ⊢L′ : Δ′ ++ Ψ′ ++ Γ′ ⊢[ m₀ ] wk[ length Ψ ↑ length Δ ] L ⦂ `↑[ m ⇒ m₀ ] S
    ⊢L′
      rewrite sym eqΔ′
            | sym eqΨ′ = wk[↑]-preserves-⊢ Δ′ (∤-preserves-is-all-deletable ΨDel Ψ∤) ⊢L
wk[↑]-preserves-⊢ {Ψ} {Γ} {m} {`return[ m₀ ⇒ _ ] L} {`↓[ _ ⇒ _ ] S}Δ ΨDel (ΔΓ∤ ⊢`return[-⇒-] ⊢L)
  with Δ′ , Γ′ , refl , Δ∤ , Γ∤ ← ∤-preserves-++ Δ ΔΓ∤
     | Ψ′ , Ψ∤ ← is-all-deletable⇒∤ m₀ ΨDel
    with eqΔ′ ← length-respects-∤ Δ∤
       | eqΨ′ ← length-respects-∤ Ψ∤ = ΔΨΓ∤ ⊢`return[-⇒-] ⊢L′
  where
    ΔΨΓ∤ = ++-mono-∤ Δ∤ (++-mono-∤ Ψ∤ Γ∤)

    ⊢L′ : Δ′ ++ Ψ′ ++ Γ′ ⊢[ m₀ ] wk[ length Ψ ↑ length Δ ] L ⦂ S
    ⊢L′
      rewrite sym eqΔ′
            | sym eqΨ′ = wk[↑]-preserves-⊢ Δ′ (∤-preserves-is-all-deletable ΨDel Ψ∤) ⊢L
wk[↑]-preserves-⊢ {Ψ} {Γ} {m} {`let-return[ _ ⇒ m₀ ] L `in M} {S} Δ ΨDel (ΔΓ~ ⊢`let-return[-⇒-] ⊢L ⦂ ⊢↓@(`↓[-⇒_][_]_ {S = T} _ _ _) `in ⊢M)
  with Δ₀ , Δ₁ , Γ₀ , Γ₁ , refl , refl , Δ~ , Γ~ ← ~⊞-preserves-++ Δ ΔΓ~
     | Ψ₁ , Ψ~ ← left-bias-~⊞ Ψ
    with _    , Ψ₁Del ← ~⊞-preserves-is-all-deletable ΨDel Ψ~
       | eqΔ₀ , eqΔ₁ ← length-respects-~⊞ Δ~
       | _    , eqΨ₁ ← length-respects-~⊞ Ψ~ = ΔΨΓ~ ⊢`let-return[-⇒-] ⊢L′ ⦂ ⊢↓ `in ⊢M′
  where
    ΔΨΓ~ = ++-mono-~⊞ Δ~ (++-mono-~⊞ Ψ~ Γ~)

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

~e⊞-contraction-assoc : e ~e e₀ ⊞ e₁ →
                        e₀ ~e e₂ ⊞ e₃ →
                        ⊢[ m ]e e₁ →
                        Bool.T (stₘ m ``Co) →
                        ∃₂ (λ e₂′ e₃′ → e₂′ ~e e₂ ⊞ e₁ × e₃′ ~e e₃ ⊞ e₁ × e ~e e₂′ ⊞ e₃′)
~e⊞-contraction-assoc (contraction Co∈m₀) (contraction _)     ⊢e₁           Co∈m = _ , _ , contraction Co∈m₀ , contraction Co∈m₀ , contraction Co∈m₀
~e⊞-contraction-assoc (contraction Co∈m₀) to-left             ⊢e₁           Co∈m = _ , _ , contraction Co∈m₀ , to-right , contraction Co∈m₀
~e⊞-contraction-assoc (contraction Co∈m₀) to-right            ⊢e₁           Co∈m = _ , _ , to-right , contraction Co∈m₀ , contraction Co∈m₀
~e⊞-contraction-assoc to-left             (contraction Co∈m₀) ⊢e₁           Co∈m = _ , _ , to-left , to-left , contraction Co∈m₀
~e⊞-contraction-assoc to-left             to-left             ⊢e₁           Co∈m = _ , _ , to-left , unusable , to-left
~e⊞-contraction-assoc to-left             to-right            ⊢e₁           Co∈m = _ , _ , unusable , to-left , to-right
~e⊞-contraction-assoc to-right            unusable            (valid ⊢S m≤) Co∈m = _ , _ , to-right , to-right , contraction (isWellStructured _ _ ``Co m≤ Co∈m)
~e⊞-contraction-assoc unusable            unusable            ⊢e₁           Co∈m = _ , _ , unusable , unusable , unusable

~⊞-contraction-assoc : Γ ~ Γ₀ ⊞ Γ₁ →
                       Γ₀ ~ Γ₂ ⊞ Γ₃ →
                       ⊢[ m ] Γ₁ →
                       Bool.T (stₘ m ``Co) →
                       ∃₂ (λ Γ₂′ Γ₃′ → Γ₂′ ~ Γ₂ ⊞ Γ₁ × Γ₃′ ~ Γ₃ ⊞ Γ₁ × Γ ~ Γ₂′ ⊞ Γ₃′)
~⊞-contraction-assoc []        []          []          Co∈m = _ , _ , [] , [] , []
~⊞-contraction-assoc (e~ ∷ Γ~) (e₀~ ∷ Γ₀~) (⊢e₁ ∷ ⊢Γ₁) Co∈m
  with _ , _ , e₂′~ , e₃′~ , e~′ ← ~e⊞-contraction-assoc e~ e₀~ ⊢e₁ Co∈m
     | _ , _ , Γ₂′~ , Γ₃′~ , Γ~′ ← ~⊞-contraction-assoc Γ~ Γ₀~ ⊢Γ₁ Co∈m = _ , _ , e₂′~ ∷ Γ₂′~ , e₃′~ ∷ Γ₃′~ , e~′ ∷ Γ~′

deletable-wk-var : Γ ~ Γ₀ ⊞ Γ₁ →
                   Γ₀ is-all-deletable →
                   x ⦂[ m ] S ∈ Γ₁ →
                   x ⦂[ m ] S ∈ Γ
deletable-wk-var (contraction Co∈m ∷ Γ~) (e₀Del ∷ Γ₀Del) (here Γ₁Del)       = here (~⊞-backward-preserves-is-all-deletable Γ₀Del Γ₁Del Γ~)
deletable-wk-var (to-right ∷ Γ~)         (e₀Del ∷ Γ₀Del) (here Γ₁Del)       = here (~⊞-backward-preserves-is-all-deletable Γ₀Del Γ₁Del Γ~)
deletable-wk-var (e~ T.∷ Γ~)             (e₀Del ∷ Γ₀Del) (T.there e₁Del x∈) = there (~e⊞-backward-preserves-is-deletable e₀Del e₁Del e~) (deletable-wk-var Γ~ Γ₀Del x∈)

deletable-wk : Γ ~ Γ₀ ⊞ Γ₁ →
               Γ₀ is-all-deletable →
               Γ₁ ⊢[ m ] L ⦂ S →
               Γ ⊢[ m ] L ⦂ S
deletable-wk Γ~ Γ₀Del (`unit Γ₁Del)                          = `unit (~⊞-backward-preserves-is-all-deletable Γ₀Del Γ₁Del Γ~)
deletable-wk Γ~ Γ₀Del (`λ⦂-∘ ⊢L)                             = `λ⦂-∘ deletable-wk (to-right ∷ Γ~) (unusable ∷ Γ₀Del) ⊢L
deletable-wk Γ~ Γ₀Del (Γ₁~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)                  = {!!} ⊢ deletable-wk {!!} Γ₀Del ⊢L ⦂ ⊢⊸ `$ ⊢M
deletable-wk Γ~ Γ₀Del (`lift[-⇒-] ⊢L)                        = `lift[-⇒-] (deletable-wk Γ~ Γ₀Del ⊢L)
deletable-wk Γ~ Γ₀Del (Γ₁∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)            = {!!} ⊢`unlift[-⇒-] {!!} ⦂ ⊢↑
deletable-wk Γ~ Γ₀Del (Γ₁∤ ⊢`return[-⇒-] ⊢L)                 = {!!} ⊢`return[-⇒-] {!!}
deletable-wk Γ~ Γ₀Del (Γ₁~ ⊢`let-return[-⇒-] ⊢L ⦂ ⊢↓ `in ⊢M) = {!!}
deletable-wk Γ~ Γ₀Del (`# x∈) = `# deletable-wk-var Γ~ Γ₀Del x∈

[/]-preserves-⊢ : ∀ Δ₀ →
                  Γ ~ Δ₀ ++ Ψ₀ ⊞ Γ₁ →
                  ⊢[ m₀ ] Γ₁ →
                  Γ₁ ⊢[ m₀ ] L ⦂ S →
                  ⊢[ m ] T ⦂⋆ →
                  Δ₀ ++ (S , m₀ , true) ∷ Ψ₀ ⊢[ m ] M ⦂ T →
                  --------------------------------------------
                  Γ ⊢[ m ] [ L /[ m₀ ] length Δ₀ ] M ⦂ T
[/]-preserves-⊢ Δ₀ Γ~ ⊢Γ₁ ⊢L ⊢T (`unit Δ₀eΨ₀Del)
  with Δ₀Del , weakening Wk∈m₀ ∷ Ψ₀Del ← All.++⁻ Δ₀ Δ₀eΨ₀Del = `unit (~⊞-backward-preserves-is-all-deletable (All.++⁺ Δ₀Del Ψ₀Del) {!!} Γ~)
[/]-preserves-⊢ Δ₀ Γ~ ⊢Γ₁ ⊢L (⊢T₀ `⊸[ _ ] ⊢T₁) (`λ⦂-∘ ⊢M) = `λ⦂-∘ ([/]-preserves-⊢ (_ ∷ Δ₀) (to-left ∷ Γ~) (unusable ⊢T₀ ∷ ⊢Γ₁) (wk[↑]-preserves-⊢ [] (unusable ∷ []) ⊢L) ⊢T₁ ⊢M)
[/]-preserves-⊢ Δ₀ Γ~ ⊢Γ₁ ⊢L ⊢T (Δ₀SΓ₀~ ⊢ ⊢M ⦂ ⊢⊸ `$ ⊢N) = {!!} ⊢ {!!} ⦂ ⊢⊸ `$ {!!}
[/]-preserves-⊢ Δ₀ Γ~ ⊢Γ₁ ⊢L (`↑[-⇒ _ ][ _ ] ⊢T) (`lift[-⇒-] ⊢M) = `lift[-⇒-] [/]-preserves-⊢ Δ₀ Γ~ ⊢Γ₁ ⊢L ⊢T ⊢M
[/]-preserves-⊢ Δ₀ Γ~ ⊢Γ₁ ⊢L ⊢T (Δ₀SΓ₀∤ ⊢`unlift[-⇒-] ⊢M ⦂ ⊢↑) = {!!}
[/]-preserves-⊢ Δ₀ Γ~ ⊢Γ₁ ⊢L ⊢T (Δ₀SΓ₀∤ ⊢`return[-⇒-] ⊢M) = {!!}
[/]-preserves-⊢ Δ₀ Γ~ ⊢Γ₁ ⊢L ⊢T (Δ₀SΓ₀~ ⊢`let-return[-⇒-] ⊢M ⦂ ⊢↓ `in ⊢N) = {!!}
[/]-preserves-⊢ Δ₀ Γ~ ⊢Γ₁ ⊢L ⊢T (`#_ {x = y} y∈)
  with y ℕ.≥? length Δ₀
...  | no  y≱ = `# {!!}
...  | yes y≥
    with y ℕ.≟ length Δ₀
...    | no  y≢ = `# {!!}
...    | yes y≡ = deletable-wk Γ~ {!!} {!!} -- from y∈ and y≡ we get (Δ₀ ++ Ψ₀) is-all-deletable and m ≡ m₀

-- [/]-preserves-⊢ : ∀ Δ Δ₀ Δ₁ →
--                   Δ ++ Γ ~ Δ₀ ++ Γ₀ ⊞ Δ₁ ++ Γ₁ →
--                   ⊢[ m₀ ] Δ₁ ++ Γ₁ →
--                   Δ₁ ++ Γ₁ ⊢[ m₀ ] L ⦂ S →
--                   ⊢[ m ] T ⦂⋆ →
--                   Δ₀ ++ (S , m₀ , true) ∷ Γ₀ ⊢[ m ] M ⦂ T →
--                   --------------------------------------------
--                   Δ ++ Γ ⊢[ m ] [ L /[ m₀ ] length Δ₀ ] M ⦂ T
-- [/]-preserves-⊢ Δ Δ₀ Δ₁ ΔΓ~ ⊢Δ₁Γ₁ ⊢L ⊢T (`unit Δ₀SΓ₀Del) = `unit {!!}
-- [/]-preserves-⊢ Δ Δ₀ Δ₁ ΔΓ~ ⊢Δ₁Γ₁ ⊢L (⊢T₀ `⊸[ x ] ⊢T₁) (`λ⦂-∘ ⊢M) = `λ⦂-∘ ([/]-preserves-⊢ (_ ∷ Δ) (_ ∷ Δ₀) (_ ∷ Δ₁) (to-left ∷ ΔΓ~) (unusable ⊢T₀ ∷ ⊢Δ₁Γ₁) (wk[↑]-preserves-⊢ [] (unusable ∷ []) ⊢L) ⊢T₁ ⊢M)
-- [/]-preserves-⊢ Δ Δ₀ Δ₁ ΔΓ~ ⊢Δ₁Γ₁ ⊢L ⊢T (Δ₀SΓ₀~ ⊢ ⊢M ⦂ ⊢⊸ `$ ⊢N)
--   with Δ₀₀ , Δ₀₁ , e ∷ Γ₀₀ , _ ∷ Γ₀₁ , refl , refl , Δ₀~ , e~ ∷ Γ₀~ ← ~⊞-preserves-++ Δ₀ Δ₀SΓ₀~
--     with e~
-- ...    | contraction Co∈m₀
--       with _ , _ , ΔΓ₀₀′~ , ΔΓ₀₁′~ , ΔΓ~′ ← ~⊞-contraction-assoc ΔΓ~ (++-mono-~⊞ Δ₀~ Γ₀~) ⊢Δ₁Γ₁ Co∈m₀ = ΔΓ~′ ⊢ {!!} ⦂ ⊢⊸ `$ {!!}
-- ...    | to-left           = {!!} ⊢ {!!} ⦂ ⊢⊸ `$ {!!}
-- ...    | to-right          = {!!} ⊢ {!!} ⦂ ⊢⊸ `$ {!!}
-- [/]-preserves-⊢ Δ Δ₀ Δ₁ ΔΓ~ ⊢Δ₁Γ₁ ⊢L (`↑[-⇒ _ ][ _ ] ⊢T) (`lift[-⇒-] ⊢M) = `lift[-⇒-] [/]-preserves-⊢ Δ Δ₀ Δ₁ ΔΓ~ ⊢Δ₁Γ₁ ⊢L ⊢T ⊢M
-- [/]-preserves-⊢ {m₀ = m₀} Δ Δ₀ Δ₁ ΔΓ~ ⊢Δ₁Γ₁ ⊢L ⊢T (_⊢`unlift[-⇒-]_⦂_ {m₀ = m₁} Δ₀SΓ₀∤ ⊢M ⊢↑)
--   with m₁ ≤?ₘ m₀
-- ...  | no  _ = {!!} ⊢`unlift[-⇒-] {!!} ⦂ ⊢↑ -- prove that Wk∈m₀ and from there prove that Δ₁ ++ Γ₁ is all deletable. Then weaken ⊢M by that fact
-- ...  | yes _ = {!!} ⊢`unlift[-⇒-] {!!} ⦂ ⊢↑
-- [/]-preserves-⊢ {m₀ = m₀} Δ Δ₀ Δ₁ ΔΓ~ ⊢Δ₁Γ₁ ⊢L ⊢T (_⊢`return[-⇒-]_ {m₀ = m₁} Δ₀SΓ∤ ⊢M)
--   with m₁ ≤?ₘ m₀
-- ...  | no  _ = {!!} ⊢`return[-⇒-] {!!} -- prove that Wk∈m₀ and from there prove that Δ₁ ++ Γ₁ is all deletable. Then weaken ⊢M by that fact
-- ...  | yes _ = {!!} ⊢`return[-⇒-] {!!}
-- [/]-preserves-⊢ Δ Δ₀ Δ₁ ΔΓ~ ⊢Δ₁Γ₁ ⊢L ⊢T (Δ₀SΓ₀~ ⊢`let-return[-⇒-] ⊢M ⦂ ⊢↓ `in ⊢N)
--   with _ , _ , _ , _ , refl , refl , Δ₀~ , e~ ∷ Γ₀~ ← ~⊞-preserves-++ Δ₀ Δ₀SΓ₀~
--     with e~
-- ...    | contraction Co∈m₀ = {!!} ⊢`let-return[-⇒-] {!!} ⦂ {!!} `in {!!}
-- ...    | to-left           = {!!} ⊢`let-return[-⇒-] {!!} ⦂ {!!} `in {!!}
-- ...    | to-right          = {!!} ⊢`let-return[-⇒-] {!!} ⦂ {!!} `in {!!}
-- [/]-preserves-⊢ Δ Δ₀ Δ₁ ΔΓ~ ⊢Δ₁Γ₁ ⊢L ⊢T (`# x∈) = {!!}

-- Lemma : Γ ∤[ m ] Γ′ satisfies Γ ~ Γ′ ⊞ Γ″ × All _is-deletable Γ″ for some Γ″

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
preservation ⊢Γ ⊢S                     (Γ~ ⊢ `λ⦂-∘ ⊢L ⦂ ⊢⊸ `$ ⊢M)                               β-⊸                        = {![/]-preserves-⊢ [] [] [] Γ~ (proj₂ (⊢∧-~⊞-⇒⊢ ⊢Γ Γ~)) ⊢M ⊢S ⊢L!}
preservation ⊢Γ (`↑[-⇒ <m ][ ↑∈m ] ⊢S) (`lift[-⇒-] ⊢L)                                          (ξ-`lift[-⇒-] L⟶[≤])       = `lift[-⇒-] preservation[≤] (⊢∧<ₘ⇒⊢ ⊢Γ <m) ⊢S ⊢L (ℳ.<⇒≱ <m) L⟶[≤]
preservation ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)                               (ξ-`unlift[-⇒-] L⟶)        = Γ∤ ⊢`unlift[-⇒-] preservation (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢↑ ⊢L L⟶ ⦂ ⊢↑
preservation ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] `lift[-⇒-] ⊢L ⦂ ⊢↑)                    (β-↑ WL)                   = ∤-backward-preserves-⊢ [] ⊢L Γ∤
preservation ⊢Γ (`↓[-⇒ m< ][ ↓∈m ] ⊢S) (Γ∤ ⊢`return[-⇒-] ⊢L)                                    (ξ-`return[-⇒-] L⟶)        = Γ∤ ⊢`return[-⇒-] preservation (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢S ⊢L L⟶
preservation ⊢Γ ⊢S                     (Γ~ ⊢`let-return[-⇒-] ⊢L ⦂ ⊢↓ `in ⊢M)                    ξ-`let-return[-⇒-] L⟶ `in- = Γ~ ⊢`let-return[-⇒-] preservation (⊢∧-~⊞-⇒⊢₀ ⊢Γ Γ~) ⊢↓ ⊢L L⟶ ⦂ ⊢↓ `in ⊢M
preservation ⊢Γ ⊢S                     (Γ~ ⊢`let-return[-⇒-] (Γ₀∤ ⊢`return[-⇒-] ⊢L) ⦂ ⊢↓ `in ⊢M) (β-↓ VL)                  = {![/]-preserves-⊢ [] [] [] ? ? ⊢L ? ⊢M!} -- Weakening from  Γ″ ⊢ [ L / 0 ] M  to  Γ ⊢ [ L / 0 ] M using Γ ∤[ m ] Γ″ (where Γ″ ~ Γ′ ⊞ Γ₁)


preservation[≤] ⊢Γ ⊢S                     (Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)                  ≮m ξ- L⟶[≤] `$?                       = Γ~ ⊢ preservation[≤] (⊢∧-~⊞-⇒⊢₀ ⊢Γ Γ~) ⊢⊸ ⊢L ≮m L⟶[≤] ⦂ ⊢⊸ `$ ⊢M
preservation[≤] ⊢Γ ⊢S                     (Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)                  ≮m (ξ-! WL `$ M⟶[≤])
  with ⊢T `⊸[ m ] ⊢S′ ← ⊢⊸                                                                                            = Γ~ ⊢ ⊢L ⦂ ⊢T `⊸[ m ] ⊢S′ `$ preservation[≤] (⊢∧-~⊞-⇒⊢₁ ⊢Γ Γ~) ⊢T ⊢M ≮m M⟶[≤]
preservation[≤] ⊢Γ (`↑[-⇒ <m ][ ↑∈m ] ⊢S) (`lift[-⇒-] ⊢L)                       ≮m (ξ-`lift[-⇒-] L⟶[≤])               = `lift[-⇒-] preservation[≤] (⊢∧<ₘ⇒⊢ ⊢Γ <m) ⊢S ⊢L (λ m₁≤ → ≮m (ℳ.≤-trans m₁≤ (ℳ.<⇒≤ <m))) L⟶[≤] 
preservation[≤] ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)            ≮m (ξ-`unlift[≰ ≰m₀ ⇒-] L⟶[≤])        = Γ∤ ⊢`unlift[-⇒-] preservation[≤] (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢↑ ⊢L ≰m₀ L⟶[≤] ⦂ ⊢↑
preservation[≤] ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)            ≮m (ξ-`unlift[≤ ≤m₀ ⇒-] L⟶)           = Γ∤ ⊢`unlift[-⇒-] preservation (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢↑ ⊢L L⟶ ⦂ ⊢↑
preservation[≤] ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] `lift[-⇒-] ⊢L ⦂ ⊢↑) ≮m (β-↑ m₀≤ WL)                       = ∤-backward-preserves-⊢ [] ⊢L Γ∤
preservation[≤] ⊢Γ (`↓[-⇒ m< ][ ↓∈m ] ⊢S) (Γ∤ ⊢`return[-⇒-] ⊢L)                 ≮m (ξ-`return[≰ ≰m₀ ⇒-] L⟶[≤])        = Γ∤ ⊢`return[-⇒-] preservation[≤] (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢S ⊢L ≰m₀ L⟶[≤]
preservation[≤] ⊢Γ (`↓[-⇒ m< ][ ↓∈m ] ⊢S) (Γ∤ ⊢`return[-⇒-] ⊢L)                 ≮m (ξ-`return[≤ ≤m₀ ⇒-] L⟶)           = Γ∤ ⊢`return[-⇒-] preservation (⊢∧∤⇒⊢ ⊢Γ Γ∤) ⊢S ⊢L L⟶
preservation[≤] ⊢Γ ⊢S                     (Γ~ ⊢`let-return[-⇒-] ⊢L ⦂ ⊢↓ `in ⊢M) ≮m ξ-`let-return[-⇒-] L⟶[≤] `in?      = Γ~ ⊢`let-return[-⇒-] preservation[≤] (⊢∧-~⊞-⇒⊢₀ ⊢Γ Γ~) ⊢↓ ⊢L ≮m L⟶[≤] ⦂ ⊢↓ `in ⊢M
preservation[≤] ⊢Γ ⊢S                     (Γ~ ⊢`let-return[-⇒-] ⊢L ⦂ ⊢↓ `in ⊢M) ≮m (ξ-`let-return[-⇒-]! WL `in M⟶[≤])
  with `↓[-⇒ m< ][ ↓∈m ] ⊢T ← ⊢↓                                                                                      = Γ~ ⊢`let-return[-⇒-] ⊢L ⦂ (`↓[-⇒ m< ][ ↓∈m ] ⊢T) `in preservation[≤] (valid ⊢T (ℳ.<⇒≤ m<) ∷ ⊢∧-~⊞-⇒⊢₁ ⊢Γ Γ~) ⊢S ⊢M ≮m M⟶[≤]
preservation[≤] ⊢Γ (⊢S `⊸[ ⊸∈m ] ⊢T)      (`λ⦂-∘ ⊢L)                            ≮m (ξ-`λ⦂[-]-∘ L⟶[≤])                 = `λ⦂-∘ preservation[≤] (valid ⊢S ℳ.≤-refl ∷ ⊢Γ) ⊢T ⊢L ≮m L⟶[≤]
