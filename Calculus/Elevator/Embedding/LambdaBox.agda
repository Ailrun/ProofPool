module Calculus.Elevator.Embedding.LambdaBox where

open import Agda.Primitive
open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_; length)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Nat as ℕ using (ℕ; suc; z≤n; s≤s)
import Data.Nat.Properties as ℕ
import Data.Nat.Induction as ℕ
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃; -,_)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary using (Rel; Antisymmetric; IsPartialOrder; IsDecPartialOrder)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import Relation.Nullary using (Dec; yes; no)

open import Calculus.Elevator.Embedding.LambdaBox.ModeSpec
import Calculus.Elevator.Syntax as S
import Calculus.Elevator.Typing as T
import Calculus.Elevator.OpSem as O
open S ℳ²
open T ℳ²
open O ℳ²
import Calculus.LambdaBox.Syntax as DP
import Calculus.LambdaBox.OpSem as DP
import Calculus.LambdaBox.Typing as DP

open ⟶* using (_◅◅_)

infix 4 _~ᵀ_
infix 4 _⍮_~ˣ_
infix 4 _⊢_~ᴹ_

pattern `↓ S = `↓[ cMode ⇒ pMode ] S
pattern `↑ S = `↑[ pMode ⇒ cMode ] S

pattern ⊢`↓ neq ⊢S = `↓[-⇒ p≤c , neq ][ _ ] ⊢S
pattern ⊢`↑ neq ⊢S = `↑[-⇒ p≤c , neq ][ _ ] ⊢S

pattern `lift L = `lift[ pMode ⇒ cMode ] L
pattern `unlift L = `unlift[ cMode ⇒ pMode ] L

pattern `return L = `return[ cMode ⇒ pMode ] L
pattern `let-return_`in_ L M = `let-return[ pMode ⇒ cMode ] L `in M

pattern `λ⦂ᵖ_∘_ S L = `λ⦂[ pMode ] S ∘ L

pattern ⊢`lift ⊢L = `lift[-⇒-] ⊢L
pattern _⊢`unlift_⦂_ Γ∤ ⊢L ⊢S = Γ∤ ⊢`unlift[-⇒-] ⊢L ⦂ ⊢S
pattern _⊢`return_ Γ∤ ⊢L = Γ∤ ⊢`return[-⇒-] ⊢L
pattern _⊢`let-return_⦂_`in_ Γ~ ⊢L ⊢S ⊢M = Γ~ ⊢`let-return[-⇒-] ⊢L ⦂ ⊢S `in ⊢M

pattern `unlift≤ VL = `unlift[≤ refl ⇒ pMode ] VL
pattern `return≤ VL = `return[≤ refl ⇒ pMode ] VL
pattern ξ-`lift L⟶ = ξ-`lift[-⇒-] L⟶
pattern ξ-`unlift L⟶ = ξ-`unlift[-⇒-] L⟶
pattern ξ-`unlift≤ L⟶ = ξ-`unlift[≤ refl ⇒-] L⟶
pattern ξ-`return L⟶ = ξ-`return[-⇒-] L⟶
pattern ξ-`return≤ L⟶ = ξ-`return[≤ refl ⇒-] L⟶
pattern ξ-`let-return_`in- L⟶ = ξ-`let-return[-⇒-] L⟶ `in-
pattern ξ-`let-return_`in? L⟶ = ξ-`let-return[-⇒-] L⟶ `in?
pattern ξ-`let-return!_`in_ WL M⟶ = ξ-`let-return[-⇒-]! WL `in M⟶

data _~ᵀ_ : DP.Type → Type → Set where
  `⊤   : ---------------------
         DP.`⊤ ~ᵀ `⊤

  `□   : DP.S ~ᵀ S →
         ------------------------
         DP.`□ DP.S ~ᵀ `↓ (`↑ S)

  _`→_ : DP.S ~ᵀ S →
         DP.T ~ᵀ T →
         --------------------------
         DP.S DP.`→ DP.T ~ᵀ S `⊸ T

data _⍮_~ˣ_ : DP.Context → DP.Context → Context → Set where
  []   : --------------
         [] ⍮ [] ~ˣ []

  _!∷ᶜ_ : DP.S ~ᵀ S →
          DP.Δ ⍮ DP.Γ ~ˣ Γ →
          ------------------------------------------------
          DP.S ∷ DP.Δ ⍮ DP.Γ ~ˣ (`↑ S , cMode , true) ∷ Γ

  ?∷ᶜ_  : DP.Δ ⍮ DP.Γ ~ˣ Γ →
          ------------------------------------------
          DP.Δ ⍮ DP.Γ ~ˣ (`↑ S , cMode , false) ∷ Γ

  _!∷ᵖ_ : DP.S ~ᵀ S →
          DP.Δ ⍮ DP.Γ ~ˣ Γ →
          ---------------------------------------------
          DP.Δ ⍮ DP.S ∷ DP.Γ ~ˣ (S , pMode , true) ∷ Γ

  ?∷ᵖ_  : DP.Δ ⍮ DP.Γ ~ˣ Γ →
          ---------------------------------------
          DP.Δ ⍮ DP.Γ ~ˣ (S , pMode , false) ∷ Γ

data _⍮_~ˣ⁻- : ℕ → ℕ → Set where
  []   : -----------
         0 ⍮ 0 ~ˣ⁻-

  !∷ᶜ_ : k ⍮ k′ ~ˣ⁻- →
         ----------------
         suc k ⍮ k′ ~ˣ⁻-

  ?∷ᶜ_ : k ⍮ k′ ~ˣ⁻- →
         --------------
         k ⍮ k′ ~ˣ⁻-

  !∷ᵖ_ : k ⍮ k′ ~ˣ⁻- →
         ----------------
         k ⍮ suc k′ ~ˣ⁻-

  ?∷ᵖ_ : k ⍮ k′ ~ˣ⁻- →
         --------------
         k ⍮ k′ ~ˣ⁻-

variable
  kk′~ : k ⍮ k′ ~ˣ⁻-

eraseˣ : DP.Δ ⍮ DP.Γ ~ˣ Γ →
         length DP.Δ ⍮ length DP.Γ ~ˣ⁻-
eraseˣ []          = []
eraseˣ (_ !∷ᶜ ΔΓ~) = !∷ᶜ eraseˣ ΔΓ~
eraseˣ   (?∷ᶜ ΔΓ~) = ?∷ᶜ eraseˣ ΔΓ~
eraseˣ (_ !∷ᵖ ΔΓ~) = !∷ᵖ eraseˣ ΔΓ~
eraseˣ   (?∷ᵖ ΔΓ~) = ?∷ᵖ eraseˣ ΔΓ~

extractˣ⁻ᶜ : k ⍮ k′ ~ˣ⁻- →
            k ⍮ 0 ~ˣ⁻-
extractˣ⁻ᶜ []         = []
extractˣ⁻ᶜ (!∷ᶜ kk′~) = !∷ᶜ extractˣ⁻ᶜ kk′~
extractˣ⁻ᶜ (?∷ᶜ kk′~) = ?∷ᶜ extractˣ⁻ᶜ kk′~
extractˣ⁻ᶜ (!∷ᵖ kk′~) = ?∷ᵖ extractˣ⁻ᶜ kk′~
extractˣ⁻ᶜ (?∷ᵖ kk′~) = ?∷ᵖ extractˣ⁻ᶜ kk′~

extractˣᶜ : DP.Δ ⍮ DP.Γ ~ˣ Γ →
            ∃ (λ Γ′ → DP.Δ ⍮ [] ~ˣ Γ′)
extractˣᶜ []                         = _ , []
extractˣᶜ (S~ !∷ᶜ ΔΓ~)               = _ , S~ !∷ᶜ proj₂ (extractˣᶜ ΔΓ~)
extractˣᶜ (?∷ᶜ_ {_} {_} {_} {S} ΔΓ~) = (`↑ S , _ , _) ∷ _ , ?∷ᶜ proj₂ (extractˣᶜ ΔΓ~)
extractˣᶜ (_!∷ᵖ_ {_} {S} S~ ΔΓ~)     = (S , _ , _) ∷ _ , ?∷ᵖ proj₂ (extractˣᶜ ΔΓ~)
extractˣᶜ (?∷ᵖ_ {_} {_} {_} {S} ΔΓ~) = (S , _ , _) ∷ _ , ?∷ᵖ proj₂ (extractˣᶜ ΔΓ~)

idxˣ⁻ᶜ : {u : ℕ} → k ⍮ k′ ~ˣ⁻- → u ℕ.< k → ℕ
idxˣ⁻ᶜ             (?∷ᵖ kk′~) u<         = suc (idxˣ⁻ᶜ kk′~ u<)
idxˣ⁻ᶜ             (!∷ᵖ kk′~) u<         = suc (idxˣ⁻ᶜ kk′~ u<)
idxˣ⁻ᶜ             (?∷ᶜ kk′~) u<         = suc (idxˣ⁻ᶜ kk′~ u<)
idxˣ⁻ᶜ {u = 0}     (!∷ᶜ kk′~) (ℕ.s≤s u<) = 0
idxˣ⁻ᶜ {u = suc u} (!∷ᶜ kk′~) (ℕ.s≤s u<) = suc (idxˣ⁻ᶜ kk′~ u<)

idxˣ⁻ᵖ : {x : ℕ} → k ⍮ k′ ~ˣ⁻- → x ℕ.< k′ → ℕ
idxˣ⁻ᵖ             (?∷ᶜ kk′~) x<         = suc (idxˣ⁻ᵖ kk′~ x<)
idxˣ⁻ᵖ             (!∷ᶜ kk′~) x<         = suc (idxˣ⁻ᵖ kk′~ x<)
idxˣ⁻ᵖ             (?∷ᵖ kk′~) x<         = suc (idxˣ⁻ᵖ kk′~ x<)
idxˣ⁻ᵖ {x = 0}     (!∷ᵖ kk′~) (ℕ.s≤s x<) = 0
idxˣ⁻ᵖ {x = suc x} (!∷ᵖ kk′~) (ℕ.s≤s x<) = suc (idxˣ⁻ᵖ kk′~ x<)

data _⊢_~ᴹ_ : k ⍮ k′ ~ˣ⁻- → DP.Term → Term → Set where
  `unit         : --------------------------------------------
                  kk′~ ⊢ DP.`unit ~ᴹ `unit

  `box          : extractˣ⁻ᶜ kk′~ ⊢ DP.L ~ᴹ L →
                  --------------------------------------------
                  kk′~ ⊢ DP.`box DP.L ~ᴹ `return (`lift L)

  `let-box_`in_ : kk′~ ⊢ DP.L ~ᴹ L →
                  !∷ᶜ kk′~ ⊢ DP.N ~ᴹ N →
                  -----------------------------------------------------------
                  kk′~ ⊢ DP.`let-box DP.L `in DP.N ~ᴹ `let-return L `in N

  `#¹_          : (u< : DP.u ℕ.< k) →
                  ---------------------------------------------------------------
                  kk′~ ⊢ DP.`#¹ DP.u ~ᴹ `unlift (`# (idxˣ⁻ᶜ kk′~ u<))

  `λ⦂_∙_        : DP.S ~ᵀ S →
                  !∷ᵖ kk′~ ⊢ DP.L ~ᴹ L →
                  -------------------------------------------
                  kk′~ ⊢ DP.`λ⦂ DP.S ∙ DP.L ~ᴹ `λ⦂ᵖ S ∘ L

  _`$_          : kk′~ ⊢ DP.L ~ᴹ L →
                  kk′~ ⊢ DP.N ~ᴹ N →
                  ------------------------------------
                  kk′~ ⊢ DP.L DP.`$ DP.N ~ᴹ L `$ N

  `#⁰_          : (x< : DP.x ℕ.< k′) →
                  -----------------------------------------------------
                  kk′~ ⊢ DP.`#⁰ DP.x ~ᴹ `# (idxˣ⁻ᵖ kk′~ x<)

  `unlift-`lift : extractˣ⁻ᶜ kk′~ ⊢ DP.L ~ᴹ L →
                  --------------------------------------
                  kk′~ ⊢ DP.L ~ᴹ `unlift (`lift L)

depth~ᴹ : kk′~ ⊢ DP.L ~ᴹ L → ℕ
depth~ᴹ `unit                = 0
depth~ᴹ (`box ~L)            = suc (depth~ᴹ ~L)
depth~ᴹ (`let-box ~L `in ~M) = suc (depth~ᴹ ~L ℕ.⊔ depth~ᴹ ~M)
depth~ᴹ (`#¹ u)              = 0
depth~ᴹ (`λ⦂ ~S ∙ ~L)        = suc (depth~ᴹ ~L)
depth~ᴹ (~L `$ ~M)           = suc (depth~ᴹ ~L ℕ.⊔ depth~ᴹ ~M)
depth~ᴹ (`#⁰ x)              = 0
depth~ᴹ (`unlift-`lift ~L)   = suc (depth~ᴹ ~L)

d-is-del² : ∀ m d →
            d [ m ]is-del
d-is-del² m false = unusable
d-is-del² m true  = weakening _

Γ-is-all-del² : ∀ Γ →
                Γ is-all-del
Γ-is-all-del² []                = []
Γ-is-all-del² ((_ , m , d) ∷ Γ) = d-is-del² m d ∷ Γ-is-all-del² Γ

extractˣᶜ-∤ : (~Γ : DP.Δ ⍮ DP.Γ ~ˣ Γ) →
              let (Γ′ , ~Γ′) = extractˣᶜ ~Γ in
              Γ ∤[ cMode ] Γ′
extractˣᶜ-∤ []          = []
extractˣᶜ-∤ (~S !∷ᶜ ~Γ) = keep refl ∷ extractˣᶜ-∤ ~Γ
extractˣᶜ-∤    (?∷ᶜ ~Γ) = keep refl ∷ extractˣᶜ-∤ ~Γ
extractˣᶜ-∤ (~S !∷ᵖ ~Γ) = delete (λ ()) (weakening _) ∷ extractˣᶜ-∤ ~Γ
extractˣᶜ-∤    (?∷ᵖ ~Γ) = delete (λ ()) unusable ∷ extractˣᶜ-∤ ~Γ

extractˣᶜ-eraseˣ-extractˣ⁻ᶜ : (~Γ : DP.Δ ⍮ DP.Γ ~ˣ Γ) →
                              let (Γ′ , ~Γ′) = extractˣᶜ ~Γ in
                              extractˣ⁻ᶜ (eraseˣ ~Γ) ≡ eraseˣ ~Γ′
extractˣᶜ-eraseˣ-extractˣ⁻ᶜ []          = refl
extractˣᶜ-eraseˣ-extractˣ⁻ᶜ (~S !∷ᶜ ~Γ) = cong !∷ᶜ_ (extractˣᶜ-eraseˣ-extractˣ⁻ᶜ ~Γ)
extractˣᶜ-eraseˣ-extractˣ⁻ᶜ    (?∷ᶜ ~Γ) = cong ?∷ᶜ_ (extractˣᶜ-eraseˣ-extractˣ⁻ᶜ ~Γ)
extractˣᶜ-eraseˣ-extractˣ⁻ᶜ (~S !∷ᵖ ~Γ) = cong ?∷ᵖ_ (extractˣᶜ-eraseˣ-extractˣ⁻ᶜ ~Γ)
extractˣᶜ-eraseˣ-extractˣ⁻ᶜ    (?∷ᵖ ~Γ) = cong ?∷ᵖ_ (extractˣᶜ-eraseˣ-extractˣ⁻ᶜ ~Γ)

idxˣ⁻ᶜ-extractˣᶜ-eraseˣ : ∀ {u : ℕ} →
                          (~Γ : DP.Δ ⍮ DP.Γ ~ˣ Γ) →
                          (u< : u ℕ.< length DP.Δ) →
                          let (Γ′ , ~Γ′) = extractˣᶜ ~Γ in
                          idxˣ⁻ᶜ (eraseˣ ~Γ) u< ≡ idxˣ⁻ᶜ (eraseˣ ~Γ′) u<
idxˣ⁻ᶜ-extractˣᶜ-eraseˣ {_ ∷ Δ} {u = 0}     (_ !∷ᶜ ~Γ) (s≤s u<) = refl
idxˣ⁻ᶜ-extractˣᶜ-eraseˣ {_ ∷ Δ} {u = suc u} (_ !∷ᶜ ~Γ) (s≤s u<) = cong suc (idxˣ⁻ᶜ-extractˣᶜ-eraseˣ ~Γ u<)
idxˣ⁻ᶜ-extractˣᶜ-eraseˣ                       (?∷ᶜ ~Γ) u<       = cong suc (idxˣ⁻ᶜ-extractˣᶜ-eraseˣ ~Γ u<)
idxˣ⁻ᶜ-extractˣᶜ-eraseˣ                     (_ !∷ᵖ ~Γ) u<       = cong suc (idxˣ⁻ᶜ-extractˣᶜ-eraseˣ ~Γ u<)
idxˣ⁻ᶜ-extractˣᶜ-eraseˣ                       (?∷ᵖ ~Γ) u<       = cong suc (idxˣ⁻ᶜ-extractˣᶜ-eraseˣ ~Γ u<)

∈⇒idxˣ⁻ᶜ-eraseˣ∈ : ∀ {u : ℕ} →
                   (~Γ : DP.Δ ⍮ DP.Γ ~ˣ Γ) →
                   DP.S ~ᵀ S →
                   (u< : u ℕ.< length DP.Δ) →
                   u DP.⦂ DP.S ∈ DP.Δ →
                   idxˣ⁻ᶜ (eraseˣ ~Γ) u< ⦂[ cMode ] `↑ S ∈ Γ
∈⇒idxˣ⁻ᶜ-eraseˣ∈ (~S !∷ᶜ ~Γ) ~S′ (s≤s z≤n) DP.here = {!   !}
∈⇒idxˣ⁻ᶜ-eraseˣ∈ (_  !∷ᶜ ~Γ) ~S (s≤s u<) (DP.there u∈) = there (weakening _) (∈⇒idxˣ⁻ᶜ-eraseˣ∈ ~Γ ~S u< u∈)
∈⇒idxˣ⁻ᶜ-eraseˣ∈    (?∷ᶜ ~Γ) ~S u< u∈ = there unusable (∈⇒idxˣ⁻ᶜ-eraseˣ∈ ~Γ ~S u< u∈)
∈⇒idxˣ⁻ᶜ-eraseˣ∈ (_  !∷ᵖ ~Γ) ~S u< u∈ = there (weakening _) (∈⇒idxˣ⁻ᶜ-eraseˣ∈ ~Γ ~S u< u∈)
∈⇒idxˣ⁻ᶜ-eraseˣ∈    (?∷ᵖ ~Γ) ~S u< u∈ = there unusable (∈⇒idxˣ⁻ᶜ-eraseˣ∈ ~Γ ~S u< u∈)

~ᴹ-soundness : (ΔΓ~ : DP.Δ ⍮ DP.Γ ~ˣ Γ) →
               DP.S ~ᵀ S →
               eraseˣ ΔΓ~ ⊢ DP.L ~ᴹ L →
               DP.Δ DP.⍮ DP.Γ ⊢ DP.L ⦂ DP.S →
               Γ ⊢[ pMode ] L ⦂ S
~ᴹ-soundness ~Γ `⊤ `unit DP.`unit = `unit (Γ-is-all-del² _)
~ᴹ-soundness ~Γ (`□ ~S) (`box ~L) (DP.`box ⊢DPL)
  with _ , ~Γ′ ← extractˣᶜ ~Γ
     | ∤Γ′ ← extractˣᶜ-∤ ~Γ
     | eq ← extractˣᶜ-eraseˣ-extractˣ⁻ᶜ ~Γ = ∤Γ′ ⊢`return ⊢`lift (~ᴹ-soundness ~Γ′ ~S (subst (_⊢ _ ~ᴹ _) eq ~L) ⊢DPL)
~ᴹ-soundness ~Γ ~S (`let-box ~L `in ~N) (DP.`let-box ⊢DPL `in ⊢DPN) = {!   !} ⊢`let-return {!   !} ⦂ {!   !} `in {!   !}
~ᴹ-soundness ~Γ ~S (`#¹ u<) (DP.`#¹ u∈)
  with _ , ~Γ′ ← extractˣᶜ ~Γ
     | ∤Γ′ ← extractˣᶜ-∤ ~Γ
     | eq ← idxˣ⁻ᶜ-extractˣᶜ-eraseˣ ~Γ u<  = ∤Γ′ ⊢`unlift (`# subst (_⦂[ _ ] _ ∈ _) (sym eq) (∈⇒idxˣ⁻ᶜ-eraseˣ∈ ~Γ′ ~S u< u∈)) ⦂ (⊢`↑ (λ ()) {!!})
~ᴹ-soundness ~Γ (~S `→ ~T) (`λ⦂ ~S′ ∙ ~L) (DP.`λ⦂-∙ ⊢DPL) = {!!}
~ᴹ-soundness ~Γ ~S (~L `$ ~N) (⊢DPL DP.`$ ⊢DPN) = {!   !} ⊢ {!   !} ⦂ {!   !} `$ {!   !}
~ᴹ-soundness ~Γ ~S (`#⁰ x<) (DP.`#⁰ x∈) = {!!}
~ᴹ-soundness ~Γ ~S (`unlift-`lift ~L) ⊢DPL
  with _ , ~Γ′ ← extractˣᶜ ~Γ
     | ∤Γ′ ← extractˣᶜ-∤ ~Γ
     | eq ← extractˣᶜ-eraseˣ-extractˣ⁻ᶜ ~Γ = ∤Γ′ ⊢`unlift ⊢`lift (~ᴹ-soundness ~Γ′ ~S (subst (_⊢ _ ~ᴹ _) eq ~L) {!   !}) ⦂ (⊢`↑ (λ ()) {!   !})

-- ~ᴹ-extractᶜ : ∀ kk′~ →
--               extractˣ⁻ᶜ kk′~ ⊢ DP.M ~ᴹ M →
--               kk′~ ⊢ DP.M ~ᴹ M
-- ~ᴹ-extractᶜ = {!!}

~ᴹ-TermWORedex[≤] : (~L : kk′~ ⊢ DP.L ~ᴹ L) →
                    ∃ λ L′ → L ⟶[ cMode ≤]* L′ × TermWORedex[ cMode ≤] L′ × Σ (kk′~ ⊢ DP.L ~ᴹ L′) λ ~L′ → depth~ᴹ ~L′ ℕ.≤ depth~ᴹ ~L
~ᴹ-TermWORedex[≤] `unit                                     = -, ε
                                                            , `unit
                                                            , `unit
                                                            , z≤n
~ᴹ-TermWORedex[≤] (`box ~L)
  with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-TermWORedex[≤] ~L = -, ξ-of-↝*-⟶[ cMode ≤]* _⟶_ `return ξ-`return≤ (ξ-of-↝*-⟶* _⟶[ cMode ≤]_ `lift ξ-`lift[-⇒-] ⟶*L′[≤])
                                                            , `return≤ (`lift WL′)
                                                            , `box ~L′
                                                            , s≤s L′≤
~ᴹ-TermWORedex[≤] (`let-box ~L `in ~M)
  with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-TermWORedex[≤] ~L
     | _ , ⟶*M′[≤] , WM′ , ~M′ , M′≤ ← ~ᴹ-TermWORedex[≤] ~M = -, ξ-of-⟶[ cMode ≤]* (`let-return_`in _) ξ-`let-return_`in? ⟶*L′[≤]
                                                                 ◅◅ ξ-of-⟶[ cMode ≤]* (`let-return _ `in_) (ξ-`let-return! WL′ `in_) ⟶*M′[≤]
                                                            , `let-return WL′ `in WM′
                                                            , `let-box ~L′ `in ~M′
                                                            , s≤s (ℕ.⊔-mono-≤ L′≤ M′≤)
~ᴹ-TermWORedex[≤] (`#¹ u<)                                  = -, ε
                                                            , `unlift≤ (`neut (`# _))
                                                            , `#¹ u<
                                                            , z≤n
~ᴹ-TermWORedex[≤] (`λ⦂ ~S ∙ ~L)
  with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-TermWORedex[≤] ~L = -, ξ-of-⟶[ cMode ≤]* (`λ⦂ᵖ _ ∘_) ξ-`λ⦂[-]-∘_ ⟶*L′[≤]
                                                            , `λ⦂ᵖ _ ∘ WL′
                                                            , `λ⦂ ~S ∙ ~L′
                                                            , s≤s L′≤
~ᴹ-TermWORedex[≤] (~L `$ ~M)
  with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-TermWORedex[≤] ~L
     | _ , ⟶*M′[≤] , WM′ , ~M′ , M′≤ ← ~ᴹ-TermWORedex[≤] ~M = -, ξ-of-⟶[ cMode ≤]* (_`$ _) ξ-_`$? ⟶*L′[≤]
                                                                 ◅◅ ξ-of-⟶[ cMode ≤]* (_ `$_) (ξ-! WL′ `$_) ⟶*M′[≤]
                                                            , WL′ `$ WM′
                                                            , ~L′ `$ ~M′
                                                            , s≤s (ℕ.⊔-mono-≤ L′≤ M′≤)
~ᴹ-TermWORedex[≤] (`#⁰ x<)                                  = -, ε
                                                            , `# _
                                                            , `#⁰ x<
                                                            , z≤n
~ᴹ-TermWORedex[≤] (`unlift-`lift ~L)
  with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-TermWORedex[≤] ~L = -, ξ-of-↝*-⟶[ cMode ≤]* _⟶_ `unlift ξ-`unlift≤ (ξ-of-↝*-⟶* (_⟶[ cMode ≤]_) `lift ξ-`lift ⟶*L′[≤]) ◅◅ β-`↑ refl WL′ ◅ ε
                                                            , WL′
                                                            , {!!}
                                                            , {!!}
-- ~ᴹ-norm¹≤ (unlift-lift ~M)
--   with _ , ⟶*M′ , VM′ , ~M′ , M′≤ ← ~ᴹ-norm¹≤ ~M = -,
--                                                    *lift-⟶⇒⟶¹≤-cong unlift cong-unlift
--                                                      (*lift-⟶¹≤⇒⟶-cong lift cong-lift ⟶*M′)
--                                                    ◅◅ β-↑ VM′
--                                                    ◅ ε
--                                                  , VM′
--                                                  , ~ᴹwk _ ~M′
--                                                  , m≤n⇒m≤1+n (respˡ _≤_ (depth~ᴹ-~ᴹwk _ ~M′) M′≤)

~ᴹ-simulation-helper : DP.M DP.⟶ DP.M′ →
                       (DPM~ : [] ⊢ DP.M ~ᴹ M) →
                       Acc ℕ._<_ (depth~ᴹ DPM~) →
                       ∃ λ M′ → M ⟶* M′ × [] ⊢ DP.M′ ~ᴹ M′
~ᴹ-simulation-helper DP.ξ-`let-box DPL⟶ `in- (`let-box ~L `in ~M) (acc r)
  with _ , ⟶*L′ , ~L′ ← ~ᴹ-simulation-helper DPL⟶ ~L (r _ (s≤s (ℕ.m≤m⊔n _ _))) = -, ξ-of-⟶* (`let-return_`in _) ξ-`let-return_`in- ⟶*L′
                                                                               , `let-box ~L′ `in ~M
~ᴹ-simulation-helper DP.β-`□                 (`let-box ~L `in ~M) r            = -, ξ-of-⟶* (`let-return_`in _) ξ-`let-return_`in- {!!}
                                                                                    ◅◅ β-`↓ {!!} ◅ ε
                                                                               , {!!}
~ᴹ-simulation-helper DP.ξ- DPL⟶ `$?          (~L `$ ~M)           (acc r)
  with _ , ⟶*L′ , ~L′ ← ~ᴹ-simulation-helper DPL⟶ ~L (r _ (s≤s (ℕ.m≤m⊔n _ _))) = -, ξ-of-⟶* (_`$ _) ξ-_`$? ⟶*L′
                                                                               , ~L′ `$ ~M
~ᴹ-simulation-helper (DP.ξ-! VDPL `$ DPM⟶)   (~L `$ ~M)           (acc r)
  with _ , ⟶*M′ , ~M′ ← ~ᴹ-simulation-helper DPM⟶ ~M (r _ (s≤s (ℕ.m≤n⊔m _ _))) = -, ξ-of-⟶* (_ `$_) (ξ-! {!!} `$_) ⟶*M′
                                                                               , ~L `$ ~M′
~ᴹ-simulation-helper (DP.β-`→ VDPM)          (~L `$ ~M)           r            = {!!}
~ᴹ-simulation-helper DPL⟶                    (`unlift-`lift ~L)   (acc r)
  with _ , ⟶*L′ , VL′ , ~L′ , L′≤ ← ~ᴹ-TermWORedex[≤] ~L
    with _ , ⟶*L″ , ~L″ ← ~ᴹ-simulation-helper DPL⟶ ~L′ (r _ (s≤s L′≤))        = -, ξ-of-⟶* `unlift ξ-`unlift (ξ-of-↝*-⟶* _⟶[ cMode ≤]_ `lift ξ-`lift ⟶*L′)
                                                                                    ◅◅ β-`↑ VL′ ◅ ⟶*L″
                                                                               , ~L″

~ᴹ-simulation : DP.L DP.⟶ DP.L′ →
                [] ⊢ DP.L ~ᴹ L →
                ∃ λ L′ → L ⟶* L′ × [] ⊢ DP.L′ ~ᴹ L′
~ᴹ-simulation DPL⟶ ~L = ~ᴹ-simulation-helper DPL⟶ ~L (ℕ.<-wellFounded _)

~ᴹ⁻¹-simulation : L ⟶ L′ →
                  [] ⊢ DP.L ~ᴹ L →
                  ∃ λ DPL′ → DP.L DP.⟶* DPL′ × [] ⊢ DPL′ ~ᴹ L′
~ᴹ⁻¹-simulation (ξ-`unlift (ξ-`lift L⟶[≤])) (`unlift-`lift ~L)        = -, ε , `unlift-`lift {!!}
-- lemma-preserve~ : [] ⊢ DP.L ~ᴹ L → L ⟶[ cMode ≤] L′ → [] ⊢ DP.L ~ᴹ L′
~ᴹ⁻¹-simulation (β-`↑ WL′)                  (`unlift-`lift ~L)        = -, ε , ~L
~ᴹ⁻¹-simulation (ξ-`return (ξ-`lift L⟶[≤])) (`box ~L)                 = -, ε , `box {!!}
-- lemma-preserve~
~ᴹ⁻¹-simulation ξ-`let-return L⟶ `in-       (`let-box ~L `in ~M)
  with _ , DPL⟶* , ~L′ ← ~ᴹ⁻¹-simulation L⟶ ~L                        = -, DP.ξ-of-⟶* (DP.`let-box_`in _) DP.ξ-`let-box_`in- DPL⟶* , `let-box ~L′ `in ~M
~ᴹ⁻¹-simulation (β-`↓ (`lift WL))           (`let-box `box ~L `in ~M) = -, DP.β-`□ ◅ ε , {!!}
-- lemma : [] ⊢ DP.L ~ᴹ L → (?∷ᶜ []) ⊢ DP.M ~ᴹ M →
--         [] ⊢ DP.[ DP.L /¹ 0 ] DP.M ~ᴹ [ `lift L /[ cMode ] 0 ] M
~ᴹ⁻¹-simulation ξ- L⟶ `$?                   (~L `$ ~M)
  with _ , DPL⟶* , ~L′ ← ~ᴹ⁻¹-simulation L⟶ ~L                        = -, DP.ξ-of-⟶* (DP._`$ _) DP.ξ-_`$? DPL⟶* , ~L′ `$ ~M
~ᴹ⁻¹-simulation (ξ-! VL′ `$ M⟶)             (~L `$ ~M)
  with _ , DPM⟶* , ~M′ ← ~ᴹ⁻¹-simulation M⟶ ~M                        = -, DP.ξ-of-⟶* (_ DP.`$_) (DP.ξ-! {!!} `$_) DPM⟶* , ~L `$ ~M′
-- lemma-value⁻¹ : [] ⊢ DPL ~ᴹ L → WeakNorm L → DP.Value DPL
~ᴹ⁻¹-simulation (β-`⊸ VM)                   ((`λ⦂ ~S ∙ ~L) `$ ~M)     = -, DP.β-`→ {!!} ◅ ε , {!!}
-- lemma-value⁻¹
-- lemma : [] ⊢ DP.L ~ᴹ L → (?∷ᵖ []) ⊢ DP.M ~ᴹ M →
--         [] ⊢ DP.[ DP.L /⁰ 0 ] DP.M ~ᴹ [ `lift L /[ pMode ] 0 ] M
 