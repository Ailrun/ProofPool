module Calculus.LinearSide.Rules.Properties where

open import Data.Nat hiding (_/_)
import Data.Nat.Properties as ℕ
open import Data.Fin using (Fin; zero; suc)
import Data.Fin as Fin
import Data.Fin.Properties as Fin
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Product
open import Data.Sum
open import Data.Unit hiding (_≟_)
open import Data.Vec using (Vec; []; _∷_; _++_)
import Data.Vec as Vec
import Data.Vec.Properties as Vec
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise; []; _∷_)
import Data.Vec.Relation.Binary.Pointwise.Inductive as VecPointwise
import Data.Vec.Relation.Unary.All as VecAll
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Relation.Binary.PropositionalEquality as ≡
open import Relation.Nullary

open import Calculus.LinearSide.Syntax
open import Calculus.LinearSide.Syntax.Properties
open import Calculus.LinearSide.Rules

<⇒unused-in⇒unused-inVar↑⋆ : ∀ {n m m′} {x} {M : 𝕄 (n + m)} {ρ : Sub Fin m m′} →
                             x unused-in M →
                             Fin.toℕ x < n →
                             Fin.lift n (Vec.lookup ρ) x unused-in (M /Var ρ VarSubst.↑⋆ n)
<⇒unused-in⇒unused-inVar↑⋆ {n = n} {ρ = ρ} (varₗ {y = y} x≢)     x<
  rewrite VarLemmas.lookup-↑⋆ (Vec.lookup ρ) {ρ = ρ} (λ _ → refl) n y
    with x≡liftx ← <⇒lift≡ {f = Vec.lookup ρ} x<
      with Fin.toℕ y <? n
...      | yes y<
        with lifty≡y ← ≡.sym (<⇒lift≡ {f = Vec.lookup ρ} y<)         = varₗ
                                                                         λ liftx≡lifty →
                                                                             x≢
                                                                               (Fin.toℕ-injective
                                                                                 (≡.trans
                                                                                   x≡liftx
                                                                                   (≡.trans
                                                                                     (≡.cong Fin.toℕ liftx≡lifty)
                                                                                     lifty≡y)))
...      | no  y≮
        with liftx≡x ← ≡.sym x≡liftx
           | y≥ ← ℕ.≮⇒≥ y≮
          with lifty≥ ← ≥⇒lift≥ {f = Vec.lookup ρ} y≥               = varₗ
                                                                        λ liftx≡lifty →
                                                                          ℕ.<⇒≢
                                                                            (ℕ.<-transʳ (ℕ.≤-reflexive liftx≡x) (ℕ.<-transˡ x< lifty≥))
                                                                            (≡.cong Fin.toℕ liftx≡lifty)
<⇒unused-in⇒unused-inVar↑⋆                 (λₗ*∘ₗ M∅)            x< = λₗ*∘ₗ <⇒unused-in⇒unused-inVar↑⋆ M∅ (s≤s x<)
<⇒unused-in⇒unused-inVar↑⋆                 (M∅ $∘ₗ N∅)           x< = <⇒unused-in⇒unused-inVar↑⋆ M∅ x< $∘ₗ <⇒unused-in⇒unused-inVar↑⋆ N∅ x<
<⇒unused-in⇒unused-inVar↑⋆                 (bangₗ M∅)            x< = bangₗ (<⇒unused-in⇒unused-inVar↑⋆ M∅ x<)
<⇒unused-in⇒unused-inVar↑⋆                 (let-bangₗ M∅ inₗ N∅) x< = let-bangₗ <⇒unused-in⇒unused-inVar↑⋆ M∅ x< inₗ <⇒unused-in⇒unused-inVar↑⋆ N∅ (s≤s x<)

<⇒unused-in⇒unused-inVarwk⋆↑⋆ : ∀ {n m l} {x} (M : 𝕄 (m + l)) →
                                Fin.toℕ x < n →
                                m Fin.↑ʳ x unused-in (M /Var VarSubst.wk⋆ n VarSubst.↑⋆ m)
<⇒unused-in⇒unused-inVarwk⋆↑⋆ {n = n} {m} {l} {x} (varₗ y) x<
  with Fin.toℕ y <? m
...  | yes y<
    rewrite <⇒var/Varwk⋆↑⋆≡var n y< = varₗ λ m↑x≡ → ℕ.<⇒≢ (ℕ.<-transˡ y< (ℕ.m≤m+n _ _)) (≡.trans (≡.sym (Fin.toℕ-fromℕ< _)) (≡.trans (≡.cong Fin.toℕ (≡.sym m↑x≡)) (Fin.toℕ-↑ʳ m x)))
...  | no  y≮
    with y≥ ← ℕ.≮⇒≥ y≮
      rewrite ↑ʳreduce≥≡id y≥
            | var/Varσ↑⋆≡var/Varσ/Varwk⋆ m (Fin.reduce≥ _ y≥) (V.wk⋆ n) = varₗ
                                                                            λ m↑x≡ →
                                                                              let y′ = Fin.reduce≥ _ y≥ in
                                                                              ℕ.<⇒≢
                                                                                (ℕ.+-monoʳ-< m (ℕ.<-transˡ x< (ℕ.m≤m+n _ _)))
                                                                                (begin
    m + Fin.toℕ x                                                                ≡˘⟨ Fin.toℕ-↑ʳ m x ⟩
    Fin.toℕ (m Fin.↑ʳ x)                                                         ≡⟨ ≡.cong Fin.toℕ (begin
      _                                                                                             ≡⟨ m↑x≡ ⟩
      Vec.lookup (V.wk⋆ m) (Vec.lookup (V.wk⋆ n) y′)                                                ≡⟨ ≡.cong (Vec.lookup (V.wk⋆ m)) (varₗ-injective (var/Varwk⋆≡var n y′)) ⟩
      Vec.lookup (V.wk⋆ m) (n Fin.↑ʳ y′)                                                            ≡⟨ varₗ-injective (var/Varwk⋆≡var m (n Fin.↑ʳ y′)) ⟩
      _                                                                                             ∎) ⟩
    Fin.toℕ (m Fin.↑ʳ (n Fin.↑ʳ y′))                                             ≡⟨ Fin.toℕ-↑ʳ m (n Fin.↑ʳ y′) ⟩
    m + Fin.toℕ (n Fin.↑ʳ y′)                                                    ≡⟨ ≡.cong (m +_) (Fin.toℕ-↑ʳ n y′) ⟩
    m + (n + Fin.toℕ y′)                                                         ∎)
  where
    open ≡.≡-Reasoning
<⇒unused-in⇒unused-inVarwk⋆↑⋆ {n = n} (λₗ T ∘ₗ M) x< = λₗ*∘ₗ <⇒unused-in⇒unused-inVarwk⋆↑⋆ M x<
<⇒unused-in⇒unused-inVarwk⋆↑⋆ {n = n} (M $∘ₗ N) x< = <⇒unused-in⇒unused-inVarwk⋆↑⋆ M x< $∘ₗ <⇒unused-in⇒unused-inVarwk⋆↑⋆ N x<
<⇒unused-in⇒unused-inVarwk⋆↑⋆ {n = n} (bangₗ M) x< = bangₗ (<⇒unused-in⇒unused-inVarwk⋆↑⋆ M x<)
<⇒unused-in⇒unused-inVarwk⋆↑⋆ {n = n} (let-bangₗ M inₗ N) x< = let-bangₗ <⇒unused-in⇒unused-inVarwk⋆↑⋆ M x< inₗ <⇒unused-in⇒unused-inVarwk⋆↑⋆ N x<

<⇒unused-inwk⋆ : ∀ {n m} {x} (M : 𝕄 m) →
                 Fin.toℕ x < n →
                 x unused-in (M / wk⋆ n)
<⇒unused-inwk⋆ {n} {m} M x<
  rewrite /-wk⋆ n {m = m} {M = M} = <⇒unused-in⇒unused-inVarwk⋆↑⋆ M x<

<⇒unused-in⇒unused-in↑⋆ : ∀ {n m m′} {x} {M : 𝕄 (n + m)} (σ : 𝕊 m m′) →
                          x unused-in M →
                          (x< : Fin.toℕ x < n) →
                          Fin.fromℕ< (ℕ.<-transˡ x< (ℕ.m≤m+n _ _)) unused-in (M / σ ↑⋆ n)
<⇒unused-in⇒unused-in↑⋆ {n = n} {m} {m′} σ (varₗ {x = x} {y = y} x≢) x<
  with Fin.toℕ y <? n
...  | yes y<
  rewrite <⇒var/≡var σ y<                                                                         = varₗ (λ fromx≡fromy → x≢ (Fin.toℕ-injective (Fin.fromℕ<-injective _ _ _ _ fromx≡fromy)))
...  | no  y≮
    with y≥ ← ℕ.≮⇒≥ y≮
      rewrite ↑ʳreduce≥≡id y≥
            | var/σ↑⋆≡var/σ/wk⋆ n (Fin.reduce≥ _ y≥) σ                                            = <⇒unused-inwk⋆ (varₗ (Fin.reduce≥ y y≥) / σ) (ℕ.≤-trans (ℕ.≤-reflexive (≡.cong suc (Fin.toℕ-fromℕ< (ℕ.<-transˡ x< (ℕ.m≤m+n _ _))))) x<)
<⇒unused-in⇒unused-in↑⋆ {n = n} {m} {m′} σ (λₗ*∘ₗ M∅)                x<
  rewrite Fin.fromℕ<-cong _ _ refl (ℕ.<-transˡ x< (ℕ.m≤m+n n m′)) (ℕ.≤-trans x< (ℕ.m≤m+n n m′))   = λₗ*∘ₗ <⇒unused-in⇒unused-in↑⋆ σ M∅ (s≤s x<)
<⇒unused-in⇒unused-in↑⋆ {n = n}          σ (M∅ $∘ₗ N∅)               x<                           = <⇒unused-in⇒unused-in↑⋆ σ M∅ x< $∘ₗ <⇒unused-in⇒unused-in↑⋆ σ N∅ x<
<⇒unused-in⇒unused-in↑⋆ {n = n} {m} {m′} σ (bangₗ M∅)                x<                           = bangₗ (<⇒unused-in⇒unused-in↑⋆ σ M∅ x<)
<⇒unused-in⇒unused-in↑⋆ {n = n} {m} {m′} σ (let-bangₗ M∅ inₗ N∅)     x<
  with M∅′ ← <⇒unused-in⇒unused-in↑⋆ σ M∅ x<
    rewrite Fin.fromℕ<-cong _ _ refl (ℕ.<-transˡ x< (ℕ.m≤m+n n m′)) (ℕ.≤-trans x< (ℕ.m≤m+n n m′)) = let-bangₗ M∅′ inₗ <⇒unused-in⇒unused-in↑⋆ σ N∅ (s≤s x<)

<⇒linear-in⇒linear-inVar↑⋆ : ∀ {n m m′} {x} {M : 𝕄 (n + m)} {ρ : Sub Fin m m′} →
                             x linear-in M →
                             Fin.toℕ x < n →
                             Fin.lift n (Vec.lookup ρ) x linear-in (M /Var ρ VarSubst.↑⋆ n)
<⇒linear-in⇒linear-inVar↑⋆ {n = n} {ρ = ρ} (varₗ {x = x} refl)    x<
  rewrite VarLemmas.lookup-↑⋆ (Vec.lookup ρ) {ρ = ρ} (λ _ → refl) n x = varₗ refl
<⇒linear-in⇒linear-inVar↑⋆                 (λₗ*∘ₗ Mₗ)             x< = λₗ*∘ₗ <⇒linear-in⇒linear-inVar↑⋆ Mₗ (s≤s x<)
<⇒linear-in⇒linear-inVar↑⋆                 (Mₗ $∘ₗ∅ N∅)           x< = <⇒linear-in⇒linear-inVar↑⋆ Mₗ x< $∘ₗ∅ <⇒unused-in⇒unused-inVar↑⋆ N∅ x<
<⇒linear-in⇒linear-inVar↑⋆                 (∅ M∅ $∘ₗ Nₗ)          x< = ∅ <⇒unused-in⇒unused-inVar↑⋆ M∅ x< $∘ₗ <⇒linear-in⇒linear-inVar↑⋆ Nₗ x<
<⇒linear-in⇒linear-inVar↑⋆                 (let-bangₗ Mₗ inₗ∅ N∅) x< = let-bangₗ <⇒linear-in⇒linear-inVar↑⋆ Mₗ x< inₗ∅ <⇒unused-in⇒unused-inVar↑⋆ N∅ (s≤s x<)
<⇒linear-in⇒linear-inVar↑⋆                 (let-bangₗ∅ M∅ inₗ Nₗ) x< = let-bangₗ∅ <⇒unused-in⇒unused-inVar↑⋆ M∅ x< inₗ <⇒linear-in⇒linear-inVar↑⋆ Nₗ (s≤s x<)

<⇒linear-in⇒linear-in↑⋆ : ∀ {n m m′} {x} {M : 𝕄 (n + m)} (σ : 𝕊 m m′) →
                          x linear-in M →
                          (x< : Fin.toℕ x < n) →
                          Fin.fromℕ< (ℕ.<-transˡ x< (ℕ.m≤m+n _ _)) linear-in (M / σ ↑⋆ n)
<⇒linear-in⇒linear-in↑⋆              σ (varₗ refl)            x<
  rewrite <⇒var/≡var σ x<                                                                        = varₗ refl
<⇒linear-in⇒linear-in↑⋆ {n} {m} {m′} σ (λₗ*∘ₗ Mₗ)             x<
  rewrite Fin.fromℕ<-cong _ _ refl (ℕ.<-transˡ x< (ℕ.m≤m+n n m′)) (ℕ.≤-trans x< (ℕ.m≤m+n _ _))   = λₗ*∘ₗ <⇒linear-in⇒linear-in↑⋆ σ Mₗ (s≤s x<)
<⇒linear-in⇒linear-in↑⋆              σ (Mₗ $∘ₗ∅ N∅)           x<                                 = <⇒linear-in⇒linear-in↑⋆ σ Mₗ x< $∘ₗ∅ <⇒unused-in⇒unused-in↑⋆ σ N∅ x<
<⇒linear-in⇒linear-in↑⋆              σ (∅ M∅ $∘ₗ Nₗ)          x<                                 = ∅ <⇒unused-in⇒unused-in↑⋆ σ M∅ x< $∘ₗ <⇒linear-in⇒linear-in↑⋆ σ Nₗ x<
<⇒linear-in⇒linear-in↑⋆ {n} {m} {m′} σ (let-bangₗ Mₗ inₗ∅ N∅) x<
  with Mₗ′ ← <⇒linear-in⇒linear-in↑⋆ σ Mₗ x<
    rewrite Fin.fromℕ<-cong _ _ refl (ℕ.<-transˡ x< (ℕ.m≤m+n n m′)) (ℕ.≤-trans x< (ℕ.m≤m+n _ _)) = let-bangₗ Mₗ′ inₗ∅ <⇒unused-in⇒unused-in↑⋆ σ N∅ (s≤s x<)
<⇒linear-in⇒linear-in↑⋆ {n} {m} {m′} σ (let-bangₗ∅ M∅ inₗ Nₗ) x<
  with M∅′ ← <⇒unused-in⇒unused-in↑⋆ σ M∅ x<
    rewrite Fin.fromℕ<-cong _ _ refl (ℕ.<-transˡ x< (ℕ.m≤m+n n m′)) (ℕ.≤-trans x< (ℕ.m≤m+n _ _)) = let-bangₗ∅ M∅′ inₗ <⇒linear-in⇒linear-in↑⋆ σ Nₗ (s≤s x<)

⊢ₗ⇒⊢ₗ/Var : Vec.map (Vec.lookup Γ) ρ ⊢ₗ M ⦂ T →
            --------------------------------------------------
            Γ ⊢ₗ M /Var ρ ⦂ T
⊢ₗ⇒⊢ₗ/Var {Γ = Γ} {ρ = ρ}                 (varₗ refl) = varₗ (≡.sym (Vec.lookup-map _ (Vec.lookup Γ) ρ))
⊢ₗ⇒⊢ₗ/Var {Γ = Γ} {ρ = ρ} {M = λₗ U ∘ₗ _} (λₗ*∘ₗ ⊢M ∣ₗ Mₗ)
  rewrite ≡.trans refl (Vec.map-∘ (Vec.lookup (U ∷ Γ)) suc ρ) = λₗ*∘ₗ ⊢ₗ⇒⊢ₗ/Var ⊢M ∣ₗ <⇒linear-in⇒linear-inVar↑⋆ Mₗ (ℕ.0<1+n {n = 0})
⊢ₗ⇒⊢ₗ/Var (⊢M $∘ₗ ⊢N) = ⊢ₗ⇒⊢ₗ/Var ⊢M $∘ₗ ⊢ₗ⇒⊢ₗ/Var ⊢N
⊢ₗ⇒⊢ₗ/Var (bangₗ ⊢M) = bangₗ (⊢ₗ⇒⊢ₗ/Var ⊢M)
⊢ₗ⇒⊢ₗ/Var {Γ = Γ} {ρ = ρ} (let-bangₗ_inₗ_ {T = T} ⊢M ⊢N)
  rewrite ≡.cong (T Vec.∷_) (≡.trans refl (Vec.map-∘ (Vec.lookup (T ∷ Γ)) suc ρ)) = let-bangₗ ⊢ₗ⇒⊢ₗ/Var ⊢M inₗ ⊢ₗ⇒⊢ₗ/Var ⊢N

⊢ₗ⇒⊢ₗweaken : Γ ⊢ₗ M ⦂ T →
              --------------------------------------------------
              U ∷ Γ ⊢ₗ weaken M ⦂ T
⊢ₗ⇒⊢ₗweaken {Γ = Γ} {U = U} ⊢M = ⊢ₗ⇒⊢ₗ/Var {Γ = U ∷ Γ} {ρ = VarSubst.wk} (≡.subst (_⊢ₗ _ ⦂ _) lemma′ ⊢M)
  where
    lemma : ∀ {n} {Γ : ℂ n} → Γ ≡ Vec.map (Vec.lookup Γ) VarSubst.id
    lemma {Γ = []} = refl
    lemma {Γ = T ∷ Γ} = ≡.cong (T ∷_) (≡.trans lemma (Vec.map-∘ (Vec.lookup (T ∷ Γ)) suc VarSubst.id))

    lemma′ : Γ ≡ Vec.map (Vec.lookup (U ∷ Γ)) VarSubst.wk
    lemma′ = ≡.trans (≡.trans lemma refl) (Vec.map-∘ (Vec.lookup (U ∷ Γ)) suc VarSubst.id)

s⊢ₗ⇒s⊢ₗweaken : Γ s⊢ₗ σ ⦂ Δ →
                T ∷ Γ s⊢ₗ Vec.map weaken σ ⦂ Δ
s⊢ₗ⇒s⊢ₗweaken {_} {_} {_} {[]}    {[]}     ⊢σ = []
s⊢ₗ⇒s⊢ₗweaken {_} {_} {_} {M ∷ σ} {T ∷ Γ} (⊢M ∷ ⊢σ) = ⊢ₗ⇒⊢ₗweaken ⊢M ∷ s⊢ₗ⇒s⊢ₗweaken ⊢σ

s⊢ₗ⇒s⊢ₗ↑ : Γ s⊢ₗ σ ⦂ Δ →
           T ∷ Γ s⊢ₗ σ ↑ ⦂ T ∷ Δ
s⊢ₗ⇒s⊢ₗ↑ ⊢σ = varₗ refl ∷ s⊢ₗ⇒s⊢ₗweaken ⊢σ

s⊢ₗwk⋆ : ∀ {Γ : Vec 𝕋 n} {Δ : Vec 𝕋 n′} → Γ ++ Δ s⊢ₗ wk⋆ (len Γ) {len Δ} ⦂ Δ
s⊢ₗwk⋆ {Γ = []}    {Δ = []}    = []
s⊢ₗwk⋆ {Γ = []}    {Δ = _ ∷ Δ} = varₗ refl ∷ s⊢ₗwk⋆
s⊢ₗwk⋆ {Γ = T ∷ Γ} {Δ = Δ}     = s⊢ₗ⇒s⊢ₗweaken s⊢ₗwk⋆

⊢ₗ⇒s⊢ₗ⇒⊢ₗ/ : Γ ⊢ₗ M ⦂ T →
             Δ s⊢ₗ σ ⦂ Γ →
             --------------------------------------------------
             Δ ⊢ₗ M / σ ⦂ T
⊢ₗ⇒s⊢ₗ⇒⊢ₗ/ {Δ = Δ}         (varₗ refl)           ⊢σ = VecPointwise.lookup {_∼_ = Δ ⊢ₗ_⦂_} ⊢σ _
⊢ₗ⇒s⊢ₗ⇒⊢ₗ/         {σ = σ} (λₗ*∘ₗ ⊢M ∣ₗ Mₗ)      ⊢σ = λₗ*∘ₗ ⊢ₗ⇒s⊢ₗ⇒⊢ₗ/ ⊢M (s⊢ₗ⇒s⊢ₗ↑ ⊢σ) ∣ₗ <⇒linear-in⇒linear-in↑⋆ σ Mₗ (ℕ.0<1+n {n = 0})
⊢ₗ⇒s⊢ₗ⇒⊢ₗ/                 (⊢M $∘ₗ ⊢N)           ⊢σ = ⊢ₗ⇒s⊢ₗ⇒⊢ₗ/ ⊢M ⊢σ $∘ₗ ⊢ₗ⇒s⊢ₗ⇒⊢ₗ/ ⊢N ⊢σ
⊢ₗ⇒s⊢ₗ⇒⊢ₗ/                 (bangₗ ⊢M)            ⊢σ = bangₗ (⊢ₗ⇒s⊢ₗ⇒⊢ₗ/ ⊢M ⊢σ)
⊢ₗ⇒s⊢ₗ⇒⊢ₗ/                 (let-bangₗ ⊢M inₗ ⊢N) ⊢σ = let-bangₗ (⊢ₗ⇒s⊢ₗ⇒⊢ₗ/ ⊢M ⊢σ) inₗ ⊢ₗ⇒s⊢ₗ⇒⊢ₗ/ ⊢N (s⊢ₗ⇒s⊢ₗ↑ ⊢σ)

type-preservation : Γ ⊢ₗ M ⦂ T →
                    M ↝ₗ M′ →
                    ------------
                    Γ ⊢ₗ M′ ⦂ T
type-preservation (⊢M $∘ₗ ⊢N)                   (M↝ₗ $∘ₗ?)           = type-preservation ⊢M M↝ₗ $∘ₗ ⊢N
type-preservation ((λₗ*∘ₗ ⊢M ∣ₗ Mₗ) $∘ₗ ⊢N)     (!$∘ₗ N↝ₗ)           = (λₗ*∘ₗ ⊢M ∣ₗ Mₗ) $∘ₗ type-preservation ⊢N N↝ₗ
type-preservation ((λₗ*∘ₗ ⊢M ∣ₗ Mₗ) $∘ₗ ⊢N)     (β-⊸ₗ VN)            = ⊢ₗ⇒s⊢ₗ⇒⊢ₗ/ ⊢M (⊢N ∷ s⊢ₗwk⋆)
type-preservation (bangₗ ⊢M)                    (bangₗ M↝ₗ)          = bangₗ (type-preservation ⊢M M↝ₗ)
type-preservation (let-bangₗ ⊢M inₗ ⊢N)         (let-bangₗ M↝ₗ inₗ?) = let-bangₗ type-preservation ⊢M M↝ₗ inₗ ⊢N
type-preservation (let-bangₗ (bangₗ ⊢M) inₗ ⊢N) (β-!ₗ VM)            = ⊢ₗ⇒s⊢ₗ⇒⊢ₗ/ ⊢N (⊢M ∷ s⊢ₗwk⋆)

progress : [] ⊢ₗ M ⦂ T → (∃ λ M′ → M ↝ₗ M′) ⊎ Valueₗ M
progress (λₗ*∘ₗ ⊢M ∣ₗ Mₗ)      = inj₂ λₗ?∘ₗ?
progress (⊢M $∘ₗ ⊢N)
  with progress ⊢M
...  | inj₁ (_ , M↝)           = inj₁ (_ , M↝ $∘ₗ?)
progress ((λₗ*∘ₗ ⊢M ∣ₗ x) $∘ₗ ⊢N)
     | inj₂ λₗ?∘ₗ?
    with progress ⊢N
...    | inj₁ (_ , N↝)         = inj₁ (_ , !$∘ₗ N↝)
...    | inj₂ VN               = inj₁ (_ , β-⊸ₗ VN)
progress (bangₗ ⊢M)
  with progress ⊢M
...  | inj₁ (_ , M↝)           = inj₁ (_ , bangₗ M↝)
...  | inj₂ VM                 = inj₂ (bangₗ VM)
progress (let-bangₗ ⊢M inₗ ⊢N)
  with progress ⊢M
...  | inj₁ (_ , M↝)           = inj₁ (_ , let-bangₗ M↝ inₗ?)
progress (let-bangₗ bangₗ ⊢M inₗ ⊢N)
     | inj₂ (bangₗ VM)         = inj₁ (_ , β-!ₗ VM)
