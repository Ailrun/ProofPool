module Calculus.LinearSide.Syntax.Properties where

open import Data.Nat hiding (_/_)
import Data.Nat.Properties as ℕ
open import Data.Fin using (Fin; zero; suc)
import Data.Fin as Fin
import Data.Fin.Properties as Fin
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Sum
import Data.Sum as Σ
open import Data.Unit hiding (_≟_)
open import Data.Vec using (Vec)
import Data.Vec as Vec
import Data.Vec.Properties as Vec
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Relation.Binary.PropositionalEquality as ≡
open import Relation.Nullary

open import Calculus.LinearSide.Syntax

<⇒lift≡ : ∀ {f : Fin n → Fin n′} →
          Fin.toℕ x < m →
          Fin.toℕ x ≡ Fin.toℕ (Fin.lift m f x)
<⇒lift≡ {m = suc m} {x = zero}  (s≤s x<) = refl
<⇒lift≡ {m = suc m} {x = suc x} (s≤s x<) = ≡.cong suc (<⇒lift≡ x<)

≥⇒lift≥ : ∀ {f : Fin n → Fin n′} →
          Fin.toℕ x ≥ m →
          Fin.toℕ (Fin.lift m f x) ≥ m
≥⇒lift≥ {m = zero}  {x = _}     x≥       = z≤n
≥⇒lift≥ {m = suc m} {x = suc x} (s≤s x≥) = s≤s (≥⇒lift≥ x≥)

↑ʳreduce≥≡id : ∀ {n m} {x : Fin (n + m)} →
               (x≥ : Fin.toℕ x ≥ n) →
               x ≡ (n Fin.↑ʳ (Fin.reduce≥ x x≥))
↑ʳreduce≥≡id {zero}  {_} {_} x≥ = refl
↑ʳreduce≥≡id {suc n} {_} {suc x} (s≤s x≥) = ≡.cong suc (↑ʳreduce≥≡id x≥)

varₗ-injective : varₗ x ≡ varₗ y →
                 x ≡ y
varₗ-injective refl = refl

module 𝕄App {ℓ} {T : ℕ → Set ℓ} (l : Lift T 𝕄) where
  open Lift l hiding (var) public

  infixl 8 _/_

  _/_ : 𝕄 m → Sub T m n → 𝕄 n
  varₗ x            / σ = lift (Vec.lookup σ x)
  λₗ T ∘ₗ M         / σ = λₗ T ∘ₗ (M / σ ↑)
  M $∘ₗ N           / σ = (M / σ) $∘ₗ (N / σ)
  bangₗ M           / σ = bangₗ (M / σ)
  let-bangₗ M inₗ N / σ = let-bangₗ (M / σ) inₗ (N / σ ↑)

  open Application (record { _/_ = _/_ }) using (_/✶_) public

  λₗ∘ₗ-/✶-↑✶ : ∀ k {m n U M} (σs : Subs T m n) →
               λₗ U ∘ₗ M /✶ σs ↑✶ k ≡ λₗ U ∘ₗ (M /✶ σs ↑✶ suc k)
  λₗ∘ₗ-/✶-↑✶ k ε        = refl
  λₗ∘ₗ-/✶-↑✶ k (σ ◅ σs) = ≡.cong₂ _/_ (λₗ∘ₗ-/✶-↑✶ k σs) refl

  $∘ₗ-/✶-↑✶ : ∀ k {m n M N} (σs : Subs T m n) →
              M $∘ₗ N /✶ σs ↑✶ k ≡ (M /✶ σs ↑✶ k) $∘ₗ (N /✶ σs ↑✶ k)
  $∘ₗ-/✶-↑✶ k ε        = refl
  $∘ₗ-/✶-↑✶ k (σ ◅ σs) = ≡.cong₂ _/_ ($∘ₗ-/✶-↑✶ k σs) refl

  bangₗ-/✶-↑✶ : ∀ k {m n M} (σs : Subs T m n) →
               bangₗ M /✶ σs ↑✶ k ≡ bangₗ (M /✶ σs ↑✶ k)
  bangₗ-/✶-↑✶ k ε        = refl
  bangₗ-/✶-↑✶ k (σ ◅ σs) = ≡.cong₂ _/_ (bangₗ-/✶-↑✶ k σs) refl

  let-bangₗ-inₗ-/✶-↑✶ : ∀ k {m n M N} (σs : Subs T m n) →
                        let-bangₗ M inₗ N /✶ σs ↑✶ k ≡ let-bangₗ (M /✶ σs ↑✶ k) inₗ (N /✶ σs ↑✶ suc k)
  let-bangₗ-inₗ-/✶-↑✶ k ε        = refl
  let-bangₗ-inₗ-/✶-↑✶ k (σ ◅ σs) = ≡.cong₂ _/_ (let-bangₗ-inₗ-/✶-↑✶ k σs) refl

𝕄Subst : TermSubst 𝕄
𝕄Subst = record { var = varₗ; app = 𝕄App._/_ }

open TermSubst 𝕄Subst using (_/Var_) public

module 𝕄Lemma {T₁ T₂} {l₁ : Lift T₁ 𝕄} {l₂ : Lift T₂ 𝕄} where
  open TermSubst 𝕄Subst
  open Lifted l₁ using () renaming (_↑✶_ to _↑✶₁_; _/✶_ to _/✶₁_)
  open Lifted l₂ using () renaming (_↑✶_ to _↑✶₂_; _/✶_ to _/✶₂_)
  open ≡.≡-Reasoning

  /✶-↑✶ : ∀ {m n} (σs₁ : Subs T₁ m n) (σs₂ : Subs T₂ m n) →
          (∀ k x → varₗ x /✶₁ σs₁ ↑✶₁ k ≡ varₗ x /✶₂ σs₂ ↑✶₂ k) →
          --------------------------------------------------------
          ∀ k M → M /✶₁ σs₁ ↑✶₁ k ≡ M /✶₂ σs₂ ↑✶₂ k
  /✶-↑✶ σs₁ σs₂ hyp k (varₗ x)                            = hyp k x
  /✶-↑✶ σs₁ σs₂ hyp k (λₗ T ∘ₗ M)                         = begin
    λₗ T ∘ₗ M /✶₁ σs₁ ↑✶₁ k                                 ≡⟨ 𝕄App.λₗ∘ₗ-/✶-↑✶ _ k σs₁ ⟩
    λₗ T ∘ₗ (M /✶₁ σs₁ ↑✶₁ suc k)                           ≡⟨ ≡.cong λₗ _ ∘ₗ_ (/✶-↑✶ σs₁ σs₂ hyp (suc k) M) ⟩
    λₗ T ∘ₗ (M /✶₂ σs₂ ↑✶₂ suc k)                           ≡˘⟨ 𝕄App.λₗ∘ₗ-/✶-↑✶ _ k σs₂ ⟩
    λₗ T ∘ₗ M /✶₂ σs₂ ↑✶₂ k                                 ∎
  /✶-↑✶ σs₁ σs₂ hyp k (M $∘ₗ N)                           = begin
    M $∘ₗ N /✶₁ σs₁ ↑✶₁ k                                   ≡⟨ 𝕄App.$∘ₗ-/✶-↑✶ _ k σs₁ ⟩
    (M /✶₁ σs₁ ↑✶₁ k) $∘ₗ (N /✶₁ σs₁ ↑✶₁ k)                 ≡⟨ ≡.cong₂ _$∘ₗ_ (/✶-↑✶ σs₁ σs₂ hyp k M)
                                                                             (/✶-↑✶ σs₁ σs₂ hyp k N) ⟩
    (M /✶₂ σs₂ ↑✶₂ k) $∘ₗ (N /✶₂ σs₂ ↑✶₂ k)                 ≡˘⟨ 𝕄App.$∘ₗ-/✶-↑✶ _ k σs₂ ⟩
    M $∘ₗ N /✶₂ σs₂ ↑✶₂ k                                   ∎
  /✶-↑✶ σs₁ σs₂ hyp k (bangₗ M)                           = begin
    bangₗ M /✶₁ σs₁ ↑✶₁ k                                   ≡⟨ 𝕄App.bangₗ-/✶-↑✶ _ k σs₁ ⟩
    bangₗ (M /✶₁ σs₁ ↑✶₁ k)                                 ≡⟨ ≡.cong bangₗ (/✶-↑✶ σs₁ σs₂ hyp k M) ⟩
    bangₗ (M /✶₂ σs₂ ↑✶₂ k)                                 ≡˘⟨ 𝕄App.bangₗ-/✶-↑✶ _ k σs₂ ⟩
    bangₗ M /✶₂ σs₂ ↑✶₂ k                                   ∎
  /✶-↑✶ σs₁ σs₂ hyp k (let-bangₗ M inₗ N)                 = begin
    let-bangₗ M inₗ N /✶₁ σs₁ ↑✶₁ k                         ≡⟨ 𝕄App.let-bangₗ-inₗ-/✶-↑✶ _ k σs₁ ⟩
    let-bangₗ (M /✶₁ σs₁ ↑✶₁ k) inₗ (N /✶₁ σs₁ ↑✶₁ suc k)   ≡⟨ ≡.cong₂ let-bangₗ_inₗ_ (/✶-↑✶ σs₁ σs₂ hyp k M)
                                                                                      (/✶-↑✶ σs₁ σs₂ hyp (suc k) N) ⟩
    let-bangₗ (M /✶₂ σs₂ ↑✶₂ k) inₗ (N /✶₂ σs₂ ↑✶₂ suc k)   ≡˘⟨ 𝕄App.let-bangₗ-inₗ-/✶-↑✶ _ k σs₂ ⟩
    (let-bangₗ M inₗ N) /✶₂ σs₂ ↑✶₂ k                       ∎

𝕄Lemmas : TermLemmas 𝕄
𝕄Lemmas = record
  { termSubst = 𝕄Subst
  ; app-var   = refl
  ; /✶-↑✶     = 𝕄Lemma./✶-↑✶
  }

open TermLemmas 𝕄Lemmas public hiding (var)
module V where
  open VarLemmas public

<⇒var/≡var : ∀ {n m m′} {x : Fin (n + m)} (σ : 𝕊 m m′) →
             (x< : Fin.toℕ x < n) →
             varₗ x / σ ↑⋆ n ≡ varₗ (Fin.fromℕ< (ℕ.<-transˡ x< (ℕ.m≤m+n _ _)))
<⇒var/≡var {suc _} {_} {_} {zero}  σ (s≤s z≤n)              = refl
<⇒var/≡var {suc n} {_} {_} {suc x} σ (s≤s x<)
  rewrite suc-/-↑ {ρ = σ ↑⋆ n} x                            = begin
    varₗ x / σ ↑⋆ n / wk                                      ≡⟨ ≡.cong (_/ wk) (<⇒var/≡var σ x<) ⟩
    varₗ (Fin.fromℕ< (ℕ.<-transˡ x< (ℕ.m≤m+n _ _))) / wk      ≡⟨ ≡.cong (_/ wk) (≡.cong varₗ (Fin.fromℕ<-cong _ _ refl _ _)) ⟩
    varₗ (Fin.fromℕ< (ℕ.≤-trans x< (ℕ.m≤m+n _ _))) / wk       ≡⟨ /-wk ⟩
    weaken (varₗ (Fin.fromℕ< (ℕ.≤-trans x< (ℕ.m≤m+n _ _))))   ≡⟨ weaken-var ⟩
    varₗ (suc (Fin.fromℕ< (ℕ.≤-trans x< (ℕ.m≤m+n _ _))))      ∎
  where
    open ≡.≡-Reasoning

var/Varwk⋆≡var : ∀ n {m} (x : Fin m) →
                 varₗ x /Var V.wk⋆ n ≡ varₗ (n Fin.↑ʳ x)
var/Varwk⋆≡var zero    {m} x        = ≡.cong varₗ (V.id-vanishes _)
var/Varwk⋆≡var (suc n) {m} x        = begin
    varₗ x /Var V.wk⋆ (suc n)         ≡⟨ ≡.cong (varₗ x /Var_) (V.map-weaken {ρ = V.wk⋆ n}) ⟩
    varₗ x /Var V.wk⋆ n V.⊙ V.wk      ≡⟨ ≡.cong varₗ (V./-⊙ {ρ₁ = V.wk⋆ n} {ρ₂ = V.wk} x) ⟩
    (varₗ x /Var V.wk⋆ n) /Var V.wk   ≡⟨ ≡.cong (_/Var V.wk) (var/Varwk⋆≡var n x) ⟩
    varₗ (n Fin.↑ʳ x) /Var V.wk       ≡⟨⟩
    weaken (varₗ (n Fin.↑ʳ x))        ≡⟨ weaken-var ⟩
    varₗ (suc (n Fin.↑ʳ x))           ∎
  where
    open ≡.≡-Reasoning

var/wk⋆≡var : ∀ n {m} (x : Fin m) →
              varₗ x / wk⋆ n ≡ varₗ (n Fin.↑ʳ x)
var/wk⋆≡var zero    {m} x      = id-vanishes _
var/wk⋆≡var (suc n) {m} x      = begin
    varₗ x / wk⋆ (suc n)       ≡⟨ ≡.cong (varₗ x /_) (map-weaken {ρ = wk⋆ n}) ⟩
    varₗ x / wk⋆ n ⊙ wk        ≡⟨ /-⊙ {ρ₁ = wk⋆ n} {ρ₂ = wk} (varₗ x) ⟩
    varₗ x / wk⋆ n / wk        ≡⟨ ≡.cong (_/ wk) (var/wk⋆≡var n x) ⟩
    varₗ (n Fin.↑ʳ x) / wk     ≡⟨ /-wk ⟩
    weaken (varₗ (n Fin.↑ʳ x)) ≡⟨ weaken-var ⟩
    varₗ (suc (n Fin.↑ʳ x))    ∎
  where
    open ≡.≡-Reasoning

<⇒var/Varwk⋆↑⋆≡var : ∀ n {m l} {x : Fin (m + l)} →
                     (x< : Fin.toℕ x < m) →
                     varₗ x /Var V.wk⋆ n V.↑⋆ m ≡ varₗ (Fin.fromℕ< (ℕ.<-transˡ x< (ℕ.m≤m+n _ _))) -- (Fin.join m (n + l) (map₂ (n Fin.↑ʳ_) (Fin.splitAt m x)))
<⇒var/Varwk⋆↑⋆≡var n {suc m} {l} {zero}  (s≤s z≤n) = refl
<⇒var/Varwk⋆↑⋆≡var n {suc m} {l} {suc x} (s≤s x<)
  with eq ← varₗ-injective (<⇒var/Varwk⋆↑⋆≡var n x<)
    rewrite Vec.lookup-map x Fin.suc (V.wk⋆ n V.↑⋆ m)
          | Fin.fromℕ<-cong _ _ refl (ℕ.<-transˡ x< (ℕ.m≤m+n m (n + l))) (ℕ.≤-trans x< (ℕ.m≤m+n m (n + l))) = ≡.cong varₗ (≡.cong suc eq)

<⇒var/wk⋆↑⋆≡var : ∀ n {m l} {x : Fin (m + l)} →
                  (x< : Fin.toℕ x < m) →
                  varₗ x / wk⋆ n ↑⋆ m ≡ varₗ (Fin.fromℕ< (ℕ.<-transˡ x< (ℕ.m≤m+n _ _))) -- (Fin.join m (n + l) (map₂ (n Fin.↑ʳ_) (Fin.splitAt m x)))
<⇒var/wk⋆↑⋆≡var n {suc m} {l} {zero}  (s≤s z≤n) = refl
<⇒var/wk⋆↑⋆≡var n {suc m} {l} {suc x} (s≤s x<)
  with eq ← <⇒var/wk⋆↑⋆≡var n x<
    rewrite Vec.lookup-map x weaken (wk⋆ n ↑⋆ m)
          | Fin.fromℕ<-cong _ _ refl (ℕ.<-transˡ x< (ℕ.m≤m+n m (n + l))) (ℕ.≤-trans x< (ℕ.m≤m+n m (n + l)))
          | ≡.sym (var-/-wk-↑⋆ 0 (Fin.fromℕ< (ℕ.≤-trans x< (ℕ.m≤m+n m (n + l)))))
          | /-wk {t = varₗ (Fin.fromℕ< (ℕ.≤-trans x< (ℕ.m≤m+n m (n + l))))} = ≡.cong weaken eq

var/Varσ↑⋆≡var/Varσ/Varwk⋆ : ∀ n {m m′} x (ρ : Sub Fin m m′) →
                             varₗ (n Fin.↑ʳ x) /Var ρ V.↑⋆ n ≡ (varₗ x /Var ρ) /Var V.wk⋆ n
var/Varσ↑⋆≡var/Varσ/Varwk⋆ zero    {m} {l} x ρ = ≡.cong varₗ (≡.sym (V.id-vanishes (x V./ ρ)))
var/Varσ↑⋆≡var/Varσ/Varwk⋆ (suc n) {m} {l} x ρ = begin
  varₗ (suc (n Fin.↑ʳ x)) /Var ρ V.↑⋆ n V.↑      ≡⟨ ≡.cong varₗ (V.suc-/-↑ {ρ = ρ V.↑⋆ n} (n Fin.↑ʳ x)) ⟩
  (varₗ (n Fin.↑ʳ x) /Var ρ V.↑⋆ n) /Var V.wk    ≡⟨ ≡.cong (_/Var V.wk) (var/Varσ↑⋆≡var/Varσ/Varwk⋆ n x ρ) ⟩
  ((varₗ x /Var ρ) /Var V.wk⋆ n) /Var V.wk       ≡˘⟨ ≡.cong varₗ (V./-weaken {ρ = V.wk⋆ n} (x V./ ρ)) ⟩
  (varₗ x /Var ρ) /Var V.wk⋆ (suc n)             ∎
  where
    open ≡.≡-Reasoning

var/σ↑⋆≡var/σ/wk⋆ : ∀ n {m m′} x (σ : 𝕊 m m′) →
                    varₗ (n Fin.↑ʳ x) / σ ↑⋆ n ≡ varₗ x / σ / wk⋆ n
var/σ↑⋆≡var/σ/wk⋆ zero    x σ = ≡.sym (id-vanishes (varₗ x / σ))
var/σ↑⋆≡var/σ/wk⋆ (suc n) x σ = ≡.trans (suc-/-↑ {ρ = σ ↑⋆ n} (n Fin.↑ʳ x)) (≡.trans (≡.cong (_/ wk) (var/σ↑⋆≡var/σ/wk⋆ n x σ)) (≡.sym (/-weaken {ρ = wk⋆ n} (varₗ x / σ))))

/-wk⋆ : ∀ n {m} {M : 𝕄 m} →
        M / wk⋆ n ≡ M /Var V.wk⋆ n
/-wk⋆ n {m} {M} = /✶-↑✶ (ε ▻ wk⋆ n) (ε ▻ V.wk⋆ n) lemma 0 M
  where
    open ≡.≡-Reasoning

    lemma : ∀ k x →
            varₗ x / wk⋆ n ↑⋆ k ≡ varₗ x /Var V.wk⋆ n V.↑⋆ k
    lemma k x
      with Fin.toℕ x <? k
    ...  | yes x< = begin
                    varₗ x / wk⋆ n ↑⋆ k ≡⟨ <⇒var/wk⋆↑⋆≡var n x< ⟩
                    varₗ (Fin.fromℕ< (ℕ.<-transˡ x< (ℕ.m≤m+n k (n + m)))) ≡˘⟨ <⇒var/Varwk⋆↑⋆≡var n x< ⟩
                    varₗ x /Var V.wk⋆ n V.↑⋆ k ∎
    ...  | no  x≮
        with x≥ ← ℕ.≮⇒≥ x≮
          rewrite ↑ʳreduce≥≡id x≥ = begin
                                    varₗ (k Fin.↑ʳ Fin.reduce≥ x x≥) / wk⋆ n ↑⋆ k ≡⟨ var/σ↑⋆≡var/σ/wk⋆ k (Fin.reduce≥ x x≥) (wk⋆ n) ⟩
                                    varₗ (Fin.reduce≥ x x≥) / wk⋆ n / wk⋆ k ≡⟨ ≡.cong (_/ wk⋆ k) (var/wk⋆≡var n (Fin.reduce≥ x x≥)) ⟩
                                    varₗ (n Fin.↑ʳ (Fin.reduce≥ x x≥)) / wk⋆ k ≡⟨ var/wk⋆≡var k (n Fin.↑ʳ Fin.reduce≥ x x≥) ⟩
                                    varₗ (k Fin.↑ʳ n Fin.↑ʳ (Fin.reduce≥ x x≥)) ≡˘⟨ var/Varwk⋆≡var k (n Fin.↑ʳ Fin.reduce≥ x x≥) ⟩
                                    varₗ (n Fin.↑ʳ (Fin.reduce≥ x x≥)) /Var V.wk⋆ k ≡˘⟨ ≡.cong (_/Var V.wk⋆ k) (var/Varwk⋆≡var n (Fin.reduce≥ x x≥)) ⟩
                                    (varₗ (Fin.reduce≥ x x≥) /Var V.wk⋆ n) /Var V.wk⋆ k ≡˘⟨ var/Varσ↑⋆≡var/Varσ/Varwk⋆ k (Fin.reduce≥ x x≥) (V.wk⋆ n) ⟩
                                    varₗ (k Fin.↑ʳ Fin.reduce≥ x x≥) /Var V.wk⋆ n V.↑⋆ k ∎

infixr 9 _→ₗ_
infixr 9 λₗ_∙ₗ_

_→ₗ_ : 𝕋 → 𝕋 → 𝕋
T →ₗ U = !ₗ T ⊸ₗ U

λₗ_∙ₗ_ : 𝕋 → 𝕄 (suc n) → 𝕄 n
λₗ T ∙ₗ M = λₗ !ₗ T ∘ₗ let-bangₗ (varₗ 0) inₗ (M / wk ↑)
