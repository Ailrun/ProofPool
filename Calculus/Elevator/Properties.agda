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
open import Data.Nat as ℕ using (ℕ; suc; _+_)
open import Data.Product as × using (_×_; _,_; proj₁; proj₂; ∃; ∃₂)
open import Data.Unit as ⊤ using (⊤)
import Function.Equivalence as FE
open import Relation.Nullary using (yes; no; ¬_)
open import Relation.Binary.Definitions using (Monotonic₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst₂; _≢_; ≢-sym)

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

⊢e∧-~e-⊞-⇒⊢e : ⊢[ m ]e e →
               e ~e e₀ ⊞ e₁ →
               ------------------------
               ⊢[ m ]e e₀ × ⊢[ m ]e e₁
⊢e∧-~e-⊞-⇒⊢e (valid ⊢S m≤) (contraction Co∈m₀) = valid ⊢S m≤ , valid ⊢S m≤
⊢e∧-~e-⊞-⇒⊢e (valid ⊢S m≤) to-left             = valid ⊢S m≤ , unusable ⊢S
⊢e∧-~e-⊞-⇒⊢e (valid ⊢S m≤) to-right            = unusable ⊢S , valid ⊢S m≤
⊢e∧-~e-⊞-⇒⊢e (unusable ⊢S) unusable            = unusable ⊢S , unusable ⊢S

⊢∧-~-⊞-⇒⊢ : ⊢[ m ] Γ →
            Γ ~ Γ₀ ⊞ Γ₁ →
            ----------------------
            ⊢[ m ] Γ₀ × ⊢[ m ] Γ₁
⊢∧-~-⊞-⇒⊢ []        []                = [] , []
⊢∧-~-⊞-⇒⊢ (⊢e ∷ ⊢Γ) (e~ ∷ Γ~)
  with ⊢e₀ , ⊢e₁ ← ⊢e∧-~e-⊞-⇒⊢e ⊢e e~
     | ⊢Γ₀ , ⊢Γ₁ ← ⊢∧-~-⊞-⇒⊢ ⊢Γ Γ~    = ⊢e₀ ∷ ⊢Γ₀ , ⊢e₁ ∷ ⊢Γ₁

⊢∧-~-⊞-⇒⊢₀ : ⊢[ m ] Γ →
             Γ ~ Γ₀ ⊞ Γ₁ →
             ----------------
             ⊢[ m ] Γ₀
⊢∧-~-⊞-⇒⊢₀ ⊢Γ Γ~ = proj₁ (⊢∧-~-⊞-⇒⊢ ⊢Γ Γ~)

⊢∧-~-⊞-⇒⊢₁ : ⊢[ m ] Γ →
             Γ ~ Γ₀ ⊞ Γ₁ →
             ----------------
             ⊢[ m ] Γ₁
⊢∧-~-⊞-⇒⊢₁ ⊢Γ Γ~ = proj₂ (⊢∧-~-⊞-⇒⊢ ⊢Γ Γ~)

⊢e∧∤[-]e⇒⊢e : ⊢[ m ]e e →
              e ∤[ m₀ ]e e′ →
              ----------------
              ⊢[ m₀ ]e e′
⊢e∧∤[-]e⇒⊢e (valid ⊢S m≤) (delete m₀≰ eDel) = unusable ⊢S
⊢e∧∤[-]e⇒⊢e (valid ⊢S m≤) (keep m₀≤)        = valid ⊢S m₀≤
⊢e∧∤[-]e⇒⊢e (unusable ⊢S) (delete m₀≰ eDel) = unusable ⊢S
⊢e∧∤[-]e⇒⊢e (unusable ⊢S) (keep m₀≤)        = unusable ⊢S

⊢∧∤[-]⇒⊢ : ⊢[ m ] Γ →
           Γ ∤[ m₀ ] Γ′ →
           ----------------
           ⊢[ m₀ ] Γ′
⊢∧∤[-]⇒⊢ []        []        = []
⊢∧∤[-]⇒⊢ (⊢e ∷ ⊢Γ) (e∤ ∷ Γ∤) = ⊢e∧∤[-]e⇒⊢e ⊢e e∤ ∷ ⊢∧∤[-]⇒⊢ ⊢Γ Γ∤

-- ~⊞-preserves-∷ : e ∷ Δ ~ Γ₀ ⊞ Γ₁ →
--                  ∃₂ (λ e₀ e₁ →
--                    ∃₂ (λ Δ₀ Δ₁ → Γ₀ ≡ e₀ ∷ Δ₀ × Γ₁ ≡ e₁ ∷ Δ₁ × e ~e e₀ ⊞ e₁ × Δ ~ Δ₀ ⊞ Δ₁))
-- ~⊞-preserves-∷ (e~ ∷ Δ~) = _ , _ , _ , _ , refl , refl , e~ , Δ~

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

flip-∤e : e ∤[ m ]e e′ →
          e′ ∤[ m₀ ]e e″ →
          ∃ (λ e‴ → e ∤[ m₀ ]e e‴ × e‴ ∤[ m ]e e″)
flip-∤e (delete m≰ eDel)  (delete m₀≰ e′Del) = _ , delete m₀≰ eDel , delete m≰ e′Del
flip-∤e (delete m≰ eDel)  (keep m₀≤)         = _ , keep m₀≤ , delete m≰ eDel
flip-∤e (keep m≤)         (delete m₀≰ e′Del) = _ , delete m₀≰ e′Del , keep m≤
flip-∤e (keep m≤)         (keep m₀≤)         = _ , keep m₀≤ , keep m≤

flip-∤ : Γ ∤[ m ] Γ′ →
         Γ′ ∤[ m₀ ] Γ″ →
         ∃ (λ Γ‴ → Γ ∤[ m₀ ] Γ‴ × Γ‴ ∤[ m ] Γ″)
flip-∤ []        [] = _ , [] , []
flip-∤ (e∤ ∷ Γ∤) (e′∤ ∷ Γ′∤)
  with _ , e∤′ , ∤e″ ← flip-∤e e∤ e′∤
     | _ , Γ∤′ , ∤Γ″ ← flip-∤ Γ∤ Γ′∤ = _ , e∤′ ∷ Γ∤′ , ∤e″ ∷ ∤Γ″

++-mono-∤ : Γ ∤[ m ] Γ′ →
            Δ ∤[ m ] Δ′ →
            Γ ++ Δ ∤[ m ] Γ′ ++ Δ′
++-mono-∤ []        Δ∤ = Δ∤
++-mono-∤ (e∤ ∷ Γ∤) Δ∤ = e∤ ∷ ++-mono-∤ Γ∤ Δ∤

∤e-backward-preserves-is-deletable : e′ is-deletable →
                                     e ∤[ m ]e e′ →
                                     e is-deletable
∤e-backward-preserves-is-deletable unusable          (delete m≰ eDel) = eDel
∤e-backward-preserves-is-deletable unusable          (keep m≤)        = unusable
∤e-backward-preserves-is-deletable (weakening Wk∈m₀) (keep m≤)        = weakening Wk∈m₀

∤-backward-preserves-is-deletable : All _is-deletable Γ′ →
                                    Γ ∤[ m ] Γ′ →
                                    All _is-deletable Γ
∤-backward-preserves-is-deletable []              []        = []
∤-backward-preserves-is-deletable (e′Del ∷ Γ′Del) (e∤ ∷ Γ∤) = ∤e-backward-preserves-is-deletable e′Del e∤ ∷ ∤-backward-preserves-is-deletable Γ′Del Γ∤

∤-backward-preserves-∈ : ∀ Δ →
                         x ⦂[ m ] S ∈ Δ ++ Γ′ →
                         Γ ∤[ m₀ ] Γ′ →
                         x ⦂[ m ] S ∈ Δ ++ Γ
∤-backward-preserves-∈ []      (here Γ′Del)    (keep _ ∷ Γ∤) = here (∤-backward-preserves-is-deletable Γ′Del Γ∤)
∤-backward-preserves-∈ []      (there eDel x∈) (e∤ ∷ Γ∤)        = there (∤e-backward-preserves-is-deletable eDel e∤) (∤-backward-preserves-∈ [] x∈ Γ∤)
∤-backward-preserves-∈ (e ∷ Δ) (here ΔΓ′Del)   Γ∤               = here (All.++⁺ (All.++⁻ˡ Δ ΔΓ′Del) (∤-backward-preserves-is-deletable (All.++⁻ʳ Δ ΔΓ′Del) Γ∤))
∤-backward-preserves-∈ (e ∷ Δ) (there eDel x∈) Γ∤               = there eDel (∤-backward-preserves-∈ Δ x∈ Γ∤)

∤-backward-preserves-⊢ : ∀ Δ →
                         Δ ++ Γ′ ⊢[ m ] L ⦂ S →
                         Γ ∤[ m₀ ] Γ′ →
                         Δ ++ Γ ⊢[ m ] L ⦂ S
∤-backward-preserves-⊢ Δ `unit                                   Γ∤ = `unit
∤-backward-preserves-⊢ Δ (`λ⦂-∘ ⊢L)                              Γ∤ = `λ⦂-∘ (∤-backward-preserves-⊢ (_ ∷ Δ) ⊢L Γ∤)
∤-backward-preserves-⊢ Δ (ΔΓ′~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)                  Γ∤
  with _ , _ , _ , _ , refl , refl , Δ~ , Γ′~ ← ~⊞-preserves-++ Δ ΔΓ′~
    with _ , _ , Γ~ , Γ₀∤ , Γ₁∤ ← ∤-backward-preserves-~⊞ Γ′~ Γ∤    = ++-mono-~⊞ Δ~ Γ~ ⊢ ∤-backward-preserves-⊢ _ ⊢L Γ₀∤ ⦂ ⊢⊸ `$ ∤-backward-preserves-⊢ _ ⊢M Γ₁∤
∤-backward-preserves-⊢ Δ (`lift[-⇒-] ⊢L)                         Γ∤ = `lift[-⇒-] ∤-backward-preserves-⊢ Δ ⊢L Γ∤
∤-backward-preserves-⊢ Δ (ΔΓ′∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)            Γ∤
  with _ , _ , refl , Δ∤ , Γ′∤ ← ∤-preserves-++ Δ ΔΓ′∤
    with _ , Γ∤′ , ∤Γ″ ← flip-∤ Γ∤ Γ′∤                              = ++-mono-∤ Δ∤ Γ∤′ ⊢`unlift[-⇒-] ∤-backward-preserves-⊢ _ ⊢L ∤Γ″ ⦂ ⊢↑
∤-backward-preserves-⊢ Δ (ΔΓ′∤ ⊢`return[-⇒-] ⊢L)                 Γ∤
  with _ , _ , refl , Δ∤ , Γ′∤ ← ∤-preserves-++ Δ ΔΓ′∤
    with _ , Γ∤′ , ∤Γ″ ← flip-∤ Γ∤ Γ′∤                              = ++-mono-∤ Δ∤ Γ∤′ ⊢`return[-⇒-] ∤-backward-preserves-⊢ _ ⊢L ∤Γ″
∤-backward-preserves-⊢ Δ (ΔΓ′~ ⊢`let-return[-⇒-] ⊢L ⦂ ⊢↓ `in ⊢M) Γ∤
  with _ , _ , _ , _ , refl , refl , Δ~ , Γ′~ ← ~⊞-preserves-++ Δ ΔΓ′~
    with _ , _ , Γ~ , Γ₀∤ , Γ₁∤ ← ∤-backward-preserves-~⊞ Γ′~ Γ∤    = ++-mono-~⊞ Δ~ Γ~ T.⊢`let-return[-⇒-] ∤-backward-preserves-⊢ _ ⊢L Γ₀∤ ⦂ ⊢↓ `in ∤-backward-preserves-⊢ _ ⊢M Γ₁∤
∤-backward-preserves-⊢ Δ (`# x∈)                                 Γ∤ = `# ∤-backward-preserves-∈ Δ x∈ Γ∤

[/]-preserves-⊢ : ∀ Δ Δ₀ Δ₁ →
                  Δ ++ Γ ~ Δ₀ ++ Γ₀ ⊞ Δ₁ ++ Γ₁ →
                  Δ₁ ++ Γ₁ ⊢[ m₀ ] L ⦂ S →
                  Δ₀ ++ (S , m₀ , true) ∷ Γ₀ ⊢[ m ] M ⦂ T →
                  Δ ++ Γ ⊢[ m ] [ L /[ m₀ ] length Δ₀ ] M ⦂ T
[/]-preserves-⊢ Δ Δ₀ Δ₁ ΔΓ~ ⊢L `unit = `unit
[/]-preserves-⊢ Δ Δ₀ Δ₁ ΔΓ~ ⊢L (`λ⦂-∘ ⊢M) = `λ⦂-∘ ([/]-preserves-⊢ (_ ∷ Δ) (_ ∷ Δ₀) (_ ∷ Δ₁) (to-left ∷ ΔΓ~) {!!} ⊢M)
[/]-preserves-⊢ Δ Δ₀ Δ₁ ΔΓ~ ⊢L (Δ₀SΓ₀~ ⊢ ⊢M ⦂ ⊢⊸ `$ ⊢N)
  with _ , _ , _ , _ , refl , refl , Δ₀~ , e~ ∷ Γ₀~ ← ~⊞-preserves-++ Δ₀ Δ₀SΓ₀~
    with e~
...    | contraction Co∈m₀ = {!!} ⊢ {!!} ⦂ ⊢⊸ `$ {!!}
...    | to-left           = {!!} ⊢ {!!} ⦂ ⊢⊸ `$ {!!}
...    | to-right          = {!!} ⊢ {!!} ⦂ ⊢⊸ `$ {!!}
[/]-preserves-⊢ Δ Δ₀ Δ₁ ΔΓ~ ⊢L (`lift[-⇒-] ⊢M) = `lift[-⇒-] [/]-preserves-⊢ Δ Δ₀ Δ₁ ΔΓ~ ⊢L ⊢M
[/]-preserves-⊢ {m₀ = m₀} Δ Δ₀ Δ₁ ΔΓ~ ⊢L (_⊢`unlift[-⇒-]_⦂_ {m₀ = m₁} Δ₀SΓ₀∤ ⊢M ⊢↑)
  with m₁ ≤?ₘ m₀
...  | no  _ = {!!} T.⊢`unlift[-⇒-] {!!} ⦂ {!!} -- prove that Wk∈m₀ and from there prove that Δ₁ ++ Γ₁ is all deletable. Then weaken ⊢M by that fact
...  | yes _ = {!!} T.⊢`unlift[-⇒-] {!!} ⦂ {!!}
[/]-preserves-⊢ {m₀ = m₀} Δ Δ₀ Δ₁ ΔΓ~ ⊢L (_⊢`return[-⇒-]_ {m₀ = m₁} Δ₀SΓ∤ ⊢M)
  with m₁ ≤?ₘ m₀
...  | no  _ = {!!} T.⊢`return[-⇒-] {!!} -- prove that Wk∈m₀ and from there prove that Δ₁ ++ Γ₁ is all deletable. Then weaken ⊢M by that fact
...  | yes _ = {!!} T.⊢`return[-⇒-] {!!}
[/]-preserves-⊢ Δ Δ₀ Δ₁ ΔΓ~ ⊢L (Δ₀SΓ₀~ ⊢`let-return[-⇒-] ⊢M ⦂ ⊢↓ `in ⊢N)
  with _ , _ , _ , _ , refl , refl , Δ₀~ , e~ ∷ Γ₀~ ← ~⊞-preserves-++ Δ₀ Δ₀SΓ₀~
    with e~
...    | contraction Co∈m₀ = {!!} T.⊢`let-return[-⇒-] {!!} ⦂ {!!} `in {!!}
...    | to-left           = {!!} T.⊢`let-return[-⇒-] {!!} ⦂ {!!} `in {!!}
...    | to-right          = {!!} T.⊢`let-return[-⇒-] {!!} ⦂ {!!} `in {!!}
[/]-preserves-⊢ Δ Δ₀ Δ₁ ΔΓ~ ⊢L (`# x∈) = {!!}

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

preservation ⊢Γ ⊢S                     (Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)                                     ξ- L⟶ `$?                  = Γ~ ⊢ preservation (⊢∧-~-⊞-⇒⊢₀ ⊢Γ Γ~) ⊢⊸ ⊢L L⟶ ⦂ ⊢⊸ `$ ⊢M
preservation ⊢Γ ⊢S                     (Γ~ ⊢ ⊢L ⦂ ⊢T `⊸[ m ] ⊢S′ `$ ⊢M)                         (ξ-! VL `$ M⟶)             = Γ~ ⊢ ⊢L ⦂ ⊢T `⊸[ m ] ⊢S′ `$ preservation (⊢∧-~-⊞-⇒⊢₁ ⊢Γ Γ~) ⊢T ⊢M M⟶
preservation ⊢Γ ⊢S                     (Γ~ ⊢ `λ⦂-∘ ⊢L ⦂ ⊢⊸ `$ ⊢M)                               β-⊸                        = [/]-preserves-⊢ [] [] [] Γ~ ⊢M ⊢L
preservation ⊢Γ (`↑[-⇒ <m ][ ↑∈m ] ⊢S) (`lift[-⇒-] ⊢L)                                          (ξ-`lift[-⇒-] L⟶[≤])       = `lift[-⇒-] preservation[≤] (⊢∧<ₘ⇒⊢ ⊢Γ <m) ⊢S ⊢L (ℳ.<⇒≱ <m) L⟶[≤]
preservation ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)                               (ξ-`unlift[-⇒-] L⟶)        = Γ∤ ⊢`unlift[-⇒-] preservation (⊢∧∤[-]⇒⊢ ⊢Γ Γ∤) ⊢↑ ⊢L L⟶ ⦂ ⊢↑
preservation ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] `lift[-⇒-] ⊢L ⦂ ⊢↑)                    (β-↑ WL)                   = ∤-backward-preserves-⊢ [] ⊢L Γ∤
preservation ⊢Γ (`↓[-⇒ m< ][ ↓∈m ] ⊢S) (Γ∤ ⊢`return[-⇒-] ⊢L)                                    (ξ-`return[-⇒-] L⟶)        = Γ∤ ⊢`return[-⇒-] preservation (⊢∧∤[-]⇒⊢ ⊢Γ Γ∤) ⊢S ⊢L L⟶
preservation ⊢Γ ⊢S                     (Γ~ ⊢`let-return[-⇒-] ⊢L ⦂ ⊢↓ `in ⊢M)                    ξ-`let-return[-⇒-] L⟶ `in- = Γ~ ⊢`let-return[-⇒-] preservation (⊢∧-~-⊞-⇒⊢₀ ⊢Γ Γ~) ⊢↓ ⊢L L⟶ ⦂ ⊢↓ `in ⊢M
preservation ⊢Γ ⊢S                     (Γ~ ⊢`let-return[-⇒-] (Γ₀∤ ⊢`return[-⇒-] ⊢L) ⦂ ⊢↓ `in ⊢M) (β-↓ VL)                  = {![/]-preserves-⊢ [] [] [] ? ⊢L ⊢M!} -- Weakening from  Γ″ ⊢ [ L / 0 ] M  to  Γ ⊢ [ L / 0 ] M using Γ ∤[ m ] Γ″ (where Γ″ ~ Γ′ ⊞ Γ₁)


preservation[≤] ⊢Γ ⊢S                     (Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)                  ≮m ξ- L⟶[≤] `$?                       = Γ~ ⊢ preservation[≤] (⊢∧-~-⊞-⇒⊢₀ ⊢Γ Γ~) ⊢⊸ ⊢L ≮m L⟶[≤] ⦂ ⊢⊸ `$ ⊢M
preservation[≤] ⊢Γ ⊢S                     (Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)                  ≮m (ξ-! WL `$ M⟶[≤])
  with ⊢T `⊸[ m ] ⊢S′ ← ⊢⊸                                                                                            = Γ~ ⊢ ⊢L ⦂ ⊢T `⊸[ m ] ⊢S′ `$ preservation[≤] (⊢∧-~-⊞-⇒⊢₁ ⊢Γ Γ~) ⊢T ⊢M ≮m M⟶[≤]
preservation[≤] ⊢Γ (`↑[-⇒ <m ][ ↑∈m ] ⊢S) (`lift[-⇒-] ⊢L)                       ≮m (ξ-`lift[-⇒-] L⟶[≤])               = `lift[-⇒-] preservation[≤] (⊢∧<ₘ⇒⊢ ⊢Γ <m) ⊢S ⊢L (λ m₁≤ → ≮m (ℳ.≤-trans m₁≤ (ℳ.<⇒≤ <m))) L⟶[≤] 
preservation[≤] ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)            ≮m (ξ-`unlift[≰ ≰m₀ ⇒-] L⟶[≤])        = Γ∤ ⊢`unlift[-⇒-] preservation[≤] (⊢∧∤[-]⇒⊢ ⊢Γ Γ∤) ⊢↑ ⊢L ≰m₀ L⟶[≤] ⦂ ⊢↑
preservation[≤] ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢↑)            ≮m (ξ-`unlift[≤ ≤m₀ ⇒-] L⟶)           = Γ∤ ⊢`unlift[-⇒-] preservation (⊢∧∤[-]⇒⊢ ⊢Γ Γ∤) ⊢↑ ⊢L L⟶ ⦂ ⊢↑
preservation[≤] ⊢Γ ⊢S                     (Γ∤ ⊢`unlift[-⇒-] `lift[-⇒-] ⊢L ⦂ ⊢↑) ≮m (β-↑ m₀≤ WL)                       = ∤-backward-preserves-⊢ [] ⊢L Γ∤
preservation[≤] ⊢Γ (`↓[-⇒ m< ][ ↓∈m ] ⊢S) (Γ∤ ⊢`return[-⇒-] ⊢L)                 ≮m (ξ-`return[≰ ≰m₀ ⇒-] L⟶[≤])        = Γ∤ ⊢`return[-⇒-] preservation[≤] (⊢∧∤[-]⇒⊢ ⊢Γ Γ∤) ⊢S ⊢L ≰m₀ L⟶[≤]
preservation[≤] ⊢Γ (`↓[-⇒ m< ][ ↓∈m ] ⊢S) (Γ∤ ⊢`return[-⇒-] ⊢L)                 ≮m (ξ-`return[≤ ≤m₀ ⇒-] L⟶)           = Γ∤ ⊢`return[-⇒-] preservation (⊢∧∤[-]⇒⊢ ⊢Γ Γ∤) ⊢S ⊢L L⟶
preservation[≤] ⊢Γ ⊢S                     (Γ~ ⊢`let-return[-⇒-] ⊢L ⦂ ⊢↓ `in ⊢M) ≮m ξ-`let-return[-⇒-] L⟶[≤] `in?      = Γ~ ⊢`let-return[-⇒-] preservation[≤] (⊢∧-~-⊞-⇒⊢₀ ⊢Γ Γ~) ⊢↓ ⊢L ≮m L⟶[≤] ⦂ ⊢↓ `in ⊢M
preservation[≤] ⊢Γ ⊢S                     (Γ~ ⊢`let-return[-⇒-] ⊢L ⦂ ⊢↓ `in ⊢M) ≮m (ξ-`let-return[-⇒-]! WL `in M⟶[≤])
  with `↓[-⇒ m< ][ ↓∈m ] ⊢T ← ⊢↓                                                                                      = Γ~ ⊢`let-return[-⇒-] ⊢L ⦂ (`↓[-⇒ m< ][ ↓∈m ] ⊢T) `in preservation[≤] (valid ⊢T (ℳ.<⇒≤ m<) ∷ ⊢∧-~-⊞-⇒⊢₁ ⊢Γ Γ~) ⊢S ⊢M ≮m M⟶[≤]
preservation[≤] ⊢Γ (⊢S `⊸[ ⊸∈m ] ⊢T)      (`λ⦂-∘ ⊢L)                            ≮m (ξ-`λ⦂[-]-∘ L⟶[≤])                 = `λ⦂-∘ preservation[≤] (valid ⊢S ℳ.≤-refl ∷ ⊢Γ) ⊢T ⊢L ≮m L⟶[≤]
