module Calculus.LinearSide.Syntax.Properties where

open import Data.Nat hiding (_/_)
import Data.Nat.Properties as ℕ
open import Data.Fin using (Fin; zero; suc)
import Data.Fin as Fin
import Data.Fin.Properties as Fin
open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Product using (_×_; -,_; <_,_>; uncurry)
open import Data.Sum using (_⊎_; inj₁; inj₂)
import Data.Sum as Σ
import Data.Vec as Vec
import Data.Vec.Properties as Vec
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (ε; _◅_; _▻_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Relation.Binary.PropositionalEquality as ≡
open import Relation.Nullary using (Dec; yes; no)
import Relation.Nullary.Decidable as Dec

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

/-id : ∀ n {m} {M : 𝕄 (n + m)} →
       M / id ↑⋆ n ≡ M /Var V.id V.↑⋆ n
/-id n {_} {M} = /✶-↑✶ (ε ▻ id) (ε ▻ V.id) lemma n M
  where
    open ≡.≡-Reasoning

    lemma : ∀ k x →
            varₗ x / id ↑⋆ k ≡ varₗ x /Var V.id V.↑⋆ k
    lemma k x                 = begin
      varₗ x / id ↑⋆ k          ≡⟨ ≡.cong (varₗ x /_) (id-↑⋆ k) ⟩
      varₗ x / id               ≡⟨ id-vanishes (varₗ x) ⟩
      varₗ x                    ≡˘⟨ ≡.cong varₗ (V.id-vanishes x) ⟩
      varₗ x /Var V.id          ≡˘⟨ ≡.cong (varₗ x /Var_) (V.id-↑⋆ k) ⟩
      varₗ x /Var V.id V.↑⋆ k   ∎

/Var-⊙ : ∀ n {m l k} {M : 𝕄 (n + m)} {ρ₁ : Sub Fin m l} {ρ₂ : Sub Fin l k} →
         M /Var (ρ₁ V.⊙ ρ₂) V.↑⋆ n ≡ (M /Var ρ₁ V.↑⋆ n) /Var ρ₂ V.↑⋆ n
/Var-⊙ n {M = M} {ρ₁} {ρ₂} = /✶-↑✶ (ε ▻ ρ₁ V.⊙ ρ₂) (ε ▻ ρ₁ ▻ ρ₂) lemma n M
  where
    open ≡.≡-Reasoning

    lemma : ∀ k x →
            varₗ x /Var (ρ₁ V.⊙ ρ₂) V.↑⋆ k ≡ (varₗ x /Var ρ₁ V.↑⋆ k) /Var ρ₂ V.↑⋆ k
    lemma k x                                = begin
      varₗ x /Var (ρ₁ V.⊙ ρ₂) V.↑⋆ k           ≡⟨ ≡.cong (λ f → varₗ (Vec.lookup f x)) (V.↑⋆-distrib k) ⟩
      varₗ x /Var (ρ₁ V.↑⋆ k V.⊙ ρ₂ V.↑⋆ k)    ≡⟨ ≡.cong varₗ (V.lookup-⨀ x (ε ▻ ρ₁ V.↑⋆ k ▻ ρ₂ V.↑⋆ k)) ⟩
      (varₗ x /Var ρ₁ V.↑⋆ k) /Var ρ₂ V.↑⋆ k   ∎

/-wk⋆↑⋆ : ∀ n m {l} {M : 𝕄 (m + l)} →
          M / wk⋆ n ↑⋆ m ≡ M /Var V.wk⋆ n V.↑⋆ m
/-wk⋆↑⋆ zero    m {l} {M} = /-id m {M = M}
/-wk⋆↑⋆ (suc n) m {l} {M} = begin
  M / wk⋆ (suc n) ↑⋆ m                     ≡⟨ ≡.cong (λ σ → M / σ ↑⋆ m) map-weaken ⟩
  M / (wk⋆ n ⊙ wk) ↑⋆ m                    ≡⟨ ≡.cong (M /_) (↑⋆-distrib m) ⟩
  M / wk⋆ n ↑⋆ m ⊙ wk ↑⋆ m                 ≡⟨ /-⨀ M (ε ▻ wk⋆ n ↑⋆ m ▻ wk ↑⋆ m) ⟩
  M / wk⋆ n ↑⋆ m / wk ↑⋆ m                 ≡⟨ ≡.cong (_/ wk ↑⋆ m) (/-wk⋆↑⋆ n m {M = M}) ⟩
  (M /Var V.wk⋆ n V.↑⋆ m) / wk ↑⋆ m        ≡⟨ /✶-↑✶
                                                (ε ▻ wk)
                                                (ε ▻ V.wk)
                                                (λ k x →
                                                  begin
    varₗ x / wk ↑⋆ k                              ≡⟨ var-/-wk-↑⋆ k x ⟩
    varₗ (Fin.lift k suc x)                       ≡˘⟨ ≡.cong varₗ (V.var-/-wk-↑⋆ k x) ⟩
    varₗ x /Var V.wk V.↑⋆ k                       ∎)
                                                m
                                                (M /Var V.wk⋆ n V.↑⋆ m) ⟩
  (M /Var V.wk⋆ n V.↑⋆ m) /Var V.wk V.↑⋆ m ≡˘⟨ /Var-⊙ m {M = M} {ρ₁ = V.wk⋆ n} {ρ₂ = V.wk} ⟩
  M /Var (V.wk⋆ n V.⊙ V.wk) V.↑⋆ m         ≡⟨ ≡.cong (λ ρ → M /Var ρ V.↑⋆ m)
                                                (V.extensionality
                                                  λ x →
                                                    begin
    x V./ V.wk⋆ n V.⊙ V.wk                          ≡⟨ Vec.lookup-map x (V._/ V.wk) (V.wk⋆ n) ⟩
    x V./ V.wk⋆ n V./ V.wk                          ≡⟨ V./-wk ⟩
    suc (x V./ V.wk⋆ n)                             ≡˘⟨ Vec.lookup-map x suc (V.wk⋆ n) ⟩
    x V./ V.wk⋆ (suc n)                             ∎) ⟩
  M /Var V.wk⋆ (suc n) V.↑⋆ m              ∎
  where
    open ≡.≡-Reasoning

<⇒var/Var≡var : ∀ {n m m′} {x : Fin (n + m)} (ρ : Sub Fin m m′) →
             (x< : Fin.toℕ x < n) →
             varₗ x /Var ρ V.↑⋆ n ≡ varₗ (Fin.fromℕ< (ℕ.<-≤-trans x< (ℕ.m≤m+n _ _)))
<⇒var/Var≡var {suc _} {_} {_} {zero}  ρ (s≤s z≤n)           = refl
<⇒var/Var≡var {suc n} {_} {_} {suc x} ρ (s≤s x<)
  rewrite V.suc-/-↑ {ρ = ρ V.↑⋆ n} x                        = begin
    weaken (varₗ (x V./ ρ V.↑⋆ n))                            ≡⟨ ≡.cong weaken (<⇒var/Var≡var ρ x<) ⟩
    weaken (varₗ (Fin.fromℕ< (ℕ.<-≤-trans x< (ℕ.m≤m+n _ _))))  ≡⟨ ≡.cong weaken (≡.cong varₗ (Fin.fromℕ<-cong _ _ refl _ _)) ⟩
    weaken (varₗ (Fin.fromℕ< (ℕ.≤-trans x< (ℕ.m≤m+n _ _))))   ≡⟨ weaken-var ⟩
    varₗ (suc (Fin.fromℕ< (ℕ.≤-trans x< (ℕ.m≤m+n _ _))))      ∎
  where
    open ≡.≡-Reasoning

<⇒var/≡var : ∀ {n m m′} {x : Fin (n + m)} (σ : 𝕊 m m′) →
             (x< : Fin.toℕ x < n) →
             varₗ x / σ ↑⋆ n ≡ varₗ (Fin.fromℕ< (ℕ.<-≤-trans x< (ℕ.m≤m+n _ _)))
<⇒var/≡var {suc _} {_} {_} {zero}  σ (s≤s z≤n)              = refl
<⇒var/≡var {suc n} {_} {_} {suc x} σ (s≤s x<)
  rewrite suc-/-↑ {ρ = σ ↑⋆ n} x                            = begin
    varₗ x / σ ↑⋆ n / wk                                      ≡⟨ ≡.cong (_/ wk) (<⇒var/≡var σ x<) ⟩
    varₗ (Fin.fromℕ< (ℕ.<-≤-trans x< (ℕ.m≤m+n _ _))) / wk      ≡⟨ ≡.cong (_/ wk) (≡.cong varₗ (Fin.fromℕ<-cong _ _ refl _ _)) ⟩
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
    weaken (varₗ x /Var V.wk⋆ n)      ≡⟨ ≡.cong weaken (var/Varwk⋆≡var n x) ⟩
    weaken (varₗ (n Fin.↑ʳ x))        ≡⟨ weaken-var ⟩
    varₗ (suc (n Fin.↑ʳ x))           ∎
  where
    open ≡.≡-Reasoning

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
var/σ↑⋆≡var/σ/wk⋆ zero    x σ          = ≡.sym (id-vanishes (varₗ x / σ))
var/σ↑⋆≡var/σ/wk⋆ (suc n) x σ          = begin
  varₗ (suc (n Fin.↑ʳ x)) / σ ↑⋆ suc n   ≡⟨ suc-/-↑ {ρ = σ ↑⋆ n} (n Fin.↑ʳ x) ⟩
  varₗ (n Fin.↑ʳ x) / σ ↑⋆ n / wk        ≡⟨ ≡.cong (_/ wk) (var/σ↑⋆≡var/σ/wk⋆ n x σ) ⟩
  varₗ x / σ / wk⋆ n / wk                ≡˘⟨ /-weaken {ρ = wk⋆ n} (varₗ x / σ) ⟩
  varₗ x / σ / wk⋆ (suc n)               ∎
  where
    open ≡.≡-Reasoning

infixr 9 _→ₗ_
infixr 9 λₗ_∙ₗ_

_→ₗ_ : 𝕋 → 𝕋 → 𝕋
T →ₗ U = !ₗ T ⊸ₗ U

λₗ_∙ₗ_ : 𝕋 → 𝕄 (suc n) → 𝕄 n
λₗ T ∙ₗ M = λₗ !ₗ T ∘ₗ let-bangₗ (varₗ 0) inₗ (M / wk ↑)

!ₗ-injective : ∀ {T₀ T₁ : 𝕋} →
               !ₗ T₀ ≡ !ₗ T₁ →
               T₀ ≡ T₁
!ₗ-injective refl = refl

⊸ₗ-injectiveˡ : ∀ {T₀ U₀ T₁ U₁ : 𝕋} →
                T₀ ⊸ₗ U₀ ≡ T₁ ⊸ₗ U₁ →
                T₀ ≡ T₁
⊸ₗ-injectiveˡ refl = refl

⊸ₗ-injectiveʳ : ∀ {T₀ U₀ T₁ U₁ : 𝕋} →
                T₀ ⊸ₗ U₀ ≡ T₁ ⊸ₗ U₁ →
                U₀ ≡ U₁
⊸ₗ-injectiveʳ refl = refl

⊸ₗ-injective : ∀ {T₀ U₀ T₁ U₁ : 𝕋} →
               T₀ ⊸ₗ U₀ ≡ T₁ ⊸ₗ U₁ →
               (T₀ ≡ T₁) × (U₀ ≡ U₁)
⊸ₗ-injective = < ⊸ₗ-injectiveˡ , ⊸ₗ-injectiveʳ >

infix  4 _𝕋≟_
_𝕋≟_ : ∀ (T₀ T₁ : 𝕋) →
       Dec (T₀ ≡ T₁)
baseₗ      𝕋≟ baseₗ      = yes refl
baseₗ      𝕋≟ (T₁ ⊸ₗ U₁) = no (λ ())
baseₗ      𝕋≟ !ₗ T₁      = no (λ ())
(T₀ ⊸ₗ U₀) 𝕋≟ baseₗ      = no (λ ())
(T₀ ⊸ₗ U₀) 𝕋≟ (T₁ ⊸ₗ U₁) = Dec.map′ (uncurry (≡.cong₂ _⊸ₗ_)) ⊸ₗ-injective ((T₀ 𝕋≟ T₁) Dec.×? (U₀ 𝕋≟ U₁))
(T₀ ⊸ₗ U₀) 𝕋≟ !ₗ T₁      = no (λ ())
!ₗ T₀      𝕋≟ baseₗ      = no (λ ())
!ₗ T₀      𝕋≟ (T₁ ⊸ₗ U₁) = no (λ ())
!ₗ T₀      𝕋≟ !ₗ T₁      = Dec.map′ (≡.cong !ₗ) !ₗ-injective (T₀ 𝕋≟ T₁)
