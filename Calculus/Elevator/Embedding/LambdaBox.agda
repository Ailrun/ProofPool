module Calculus.Elevator.Embedding.LambdaBox where

open import Agda.Primitive
open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_; _++_; length)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Nat as ℕ using (ℕ; zero; suc; z≤n; s≤s; _+_)
import Data.Nat.Properties as ℕ
import Data.Nat.Induction as ℕ
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃; -,_)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary using (Rel; Antisymmetric; IsPartialOrder; IsDecPartialOrder)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst)
open import Relation.Nullary using (Dec; yes; no)

open import Calculus.Elevator.Embedding.LambdaBox.ModeSpec
import Calculus.Elevator.Syntax as S
import Calculus.Elevator.Typing as T
import Calculus.Elevator.Typing.Properties as TP
import Calculus.Elevator.OpSem as O
open S ℳ²
open T ℳ²
open TP ℳ²
open O ℳ²
import Calculus.LambdaBox.Syntax as DP
import Calculus.LambdaBox.OpSem as DP
import Calculus.LambdaBox.Typing as DP
import Calculus.LambdaBox.Typing.Properties as DP

open ⟶* using (_◅◅_)

infix   4 _~ᵀ_
infix   4 _⍮_~ˣ_
infix   4 _⍮_~ˣ⁻
infix   4 _⊢_~ᴹ_
infixr  5 _++ˣ⁻_

pattern `↓ S = `↓[ cMode ⇒ pMode ] S
pattern `↑ S = `↑[ pMode ⇒ cMode ] S

pattern ⊢`⊤ = `⊤[ _ ]
pattern ⊢`↓ neq ⊢S = `↓[-⇒ p≤c , neq ][ _ ] ⊢S
pattern ⊢`↑ neq ⊢S = `↑[-⇒ p≤c , neq ][ _ ] ⊢S
pattern ⊢_`⊸_ ⊢S ⊢T = ⊢S `⊸[ _ ] ⊢T

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

data _⍮_~ˣ⁻ : ℕ → ℕ → Set where
  []   : -----------
         0 ⍮ 0 ~ˣ⁻

  !∷ᶜ_ : k ⍮ k′ ~ˣ⁻ →
         ----------------
         suc k ⍮ k′ ~ˣ⁻

  ?∷ᶜ_ : k ⍮ k′ ~ˣ⁻ →
         --------------
         k ⍮ k′ ~ˣ⁻

  !∷ᵖ_ : k ⍮ k′ ~ˣ⁻ →
         ----------------
         k ⍮ suc k′ ~ˣ⁻

  ?∷ᵖ_ : k ⍮ k′ ~ˣ⁻ →
         --------------
         k ⍮ k′ ~ˣ⁻

variable
  kk′~ : k ⍮ k′ ~ˣ⁻

eraseˣ : DP.Δ ⍮ DP.Γ ~ˣ Γ →
         length DP.Δ ⍮ length DP.Γ ~ˣ⁻
eraseˣ []          = []
eraseˣ (_ !∷ᶜ ΔΓ~) = !∷ᶜ eraseˣ ΔΓ~
eraseˣ   (?∷ᶜ ΔΓ~) = ?∷ᶜ eraseˣ ΔΓ~
eraseˣ (_ !∷ᵖ ΔΓ~) = !∷ᵖ eraseˣ ΔΓ~
eraseˣ   (?∷ᵖ ΔΓ~) = ?∷ᵖ eraseˣ ΔΓ~

_++ˣ⁻_ : k ⍮ k′ ~ˣ⁻ →
         k″ ⍮ k‴ ~ˣ⁻ →
         k + k″ ⍮ k′ + k‴ ~ˣ⁻
[]         ++ˣ⁻ k″k‴~ = k″k‴~
(!∷ᶜ kk′~) ++ˣ⁻ k″k‴~ = !∷ᶜ (kk′~ ++ˣ⁻ k″k‴~)
(?∷ᶜ kk′~) ++ˣ⁻ k″k‴~ = ?∷ᶜ (kk′~ ++ˣ⁻ k″k‴~)
(!∷ᵖ kk′~) ++ˣ⁻ k″k‴~ = !∷ᵖ (kk′~ ++ˣ⁻ k″k‴~)
(?∷ᵖ kk′~) ++ˣ⁻ k″k‴~ = ?∷ᵖ (kk′~ ++ˣ⁻ k″k‴~)

extractˣ⁻ᶜ : k ⍮ k′ ~ˣ⁻ →
             k ⍮ 0 ~ˣ⁻
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

idxˣ⁻ᶜ : {u : ℕ} → k ⍮ k′ ~ˣ⁻ → u ℕ.< k → ℕ
idxˣ⁻ᶜ             (?∷ᵖ kk′~) u<         = suc (idxˣ⁻ᶜ kk′~ u<)
idxˣ⁻ᶜ             (!∷ᵖ kk′~) u<         = suc (idxˣ⁻ᶜ kk′~ u<)
idxˣ⁻ᶜ             (?∷ᶜ kk′~) u<         = suc (idxˣ⁻ᶜ kk′~ u<)
idxˣ⁻ᶜ {u = 0}     (!∷ᶜ kk′~) (ℕ.s≤s u<) = 0
idxˣ⁻ᶜ {u = suc u} (!∷ᶜ kk′~) (ℕ.s≤s u<) = suc (idxˣ⁻ᶜ kk′~ u<)

idxˣ⁻ᵖ : {x : ℕ} → k ⍮ k′ ~ˣ⁻ → x ℕ.< k′ → ℕ
idxˣ⁻ᵖ             (?∷ᶜ kk′~) x<         = suc (idxˣ⁻ᵖ kk′~ x<)
idxˣ⁻ᵖ             (!∷ᶜ kk′~) x<         = suc (idxˣ⁻ᵖ kk′~ x<)
idxˣ⁻ᵖ             (?∷ᵖ kk′~) x<         = suc (idxˣ⁻ᵖ kk′~ x<)
idxˣ⁻ᵖ {x = 0}     (!∷ᵖ kk′~) (ℕ.s≤s x<) = 0
idxˣ⁻ᵖ {x = suc x} (!∷ᵖ kk′~) (ℕ.s≤s x<) = suc (idxˣ⁻ᵖ kk′~ x<)

data _⊢_~ᴹ_ : k ⍮ k′ ~ˣ⁻ → DP.Term → Term → Set where
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

~ᵀ-det : DP.S ~ᵀ S →
         DP.S ~ᵀ S′ →
         S ≡ S′
~ᵀ-det `⊤         `⊤           = refl
~ᵀ-det (`□ ~S)    (`□ ~S′)
  rewrite ~ᵀ-det ~S ~S′        = refl
~ᵀ-det (~S `→ ~T) (~S′ `→ ~T′)
  rewrite ~ᵀ-det ~S ~S′
        | ~ᵀ-det ~T ~T′        = refl

~ᵀ-inj : DP.S ~ᵀ S →
         DP.S′ ~ᵀ S →
         DP.S ≡ DP.S′
~ᵀ-inj `⊤         `⊤           = refl
~ᵀ-inj (`□ ~S)    (`□ ~S′)
  rewrite ~ᵀ-inj ~S ~S′        = refl
~ᵀ-inj (~S `→ ~T) (~S′ `→ ~T′)
  rewrite ~ᵀ-inj ~S ~S′
        | ~ᵀ-inj ~T ~T′        = refl

~ᵀ-total : ∀ DPS →
           ∃ (λ S → DPS ~ᵀ S)
~ᵀ-total DP.`⊤           = -, `⊤
~ᵀ-total (DPS DP.`→ DPT) = -, proj₂ (~ᵀ-total DPS) `→ proj₂ (~ᵀ-total DPT)
~ᵀ-total (DP.`□ DPS)     = -, `□ (proj₂ (~ᵀ-total DPS))

~ᵀ⇒⊢ : DP.S ~ᵀ S →
       ⊢[ pMode ] S ⦂⋆
~ᵀ⇒⊢ `⊤         = ⊢`⊤
~ᵀ⇒⊢ (`□ ~S)    = ⊢`↓ (λ ()) (⊢`↑ (λ ()) (~ᵀ⇒⊢ ~S))
~ᵀ⇒⊢ (~S `→ ~T) = ⊢ ~ᵀ⇒⊢ ~S `⊸ ~ᵀ⇒⊢ ~T

is-del² : ∀ m d →
            d [ m ]is-del
is-del² _ false = unusable
is-del² _ true  = weakening _

is-all-del² : ∀ Γ →
                Γ is-all-del
is-all-del² []      = []
is-all-del² (_ ∷ Γ) = is-del² _ _ ∷ is-all-del² _

~d⊞² : ∀ m d →
       d [ m ]~d d ⊞ d
~d⊞² _ false = unusable
~d⊞² _ true  = contraction _

~⊞² : ∀ Γ →
      Γ ~ Γ ⊞ Γ
~⊞² []      = []
~⊞² (_ ∷ Γ) = ~d⊞² _ _ ∷ ~⊞² _

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
idxˣ⁻ᶜ-extractˣᶜ-eraseˣ                       (?∷ᶜ ~Γ) u<       = cong suc (idxˣ⁻ᶜ-extractˣᶜ-eraseˣ ~Γ u<)
idxˣ⁻ᶜ-extractˣᶜ-eraseˣ                     (_ !∷ᵖ ~Γ) u<       = cong suc (idxˣ⁻ᶜ-extractˣᶜ-eraseˣ ~Γ u<)
idxˣ⁻ᶜ-extractˣᶜ-eraseˣ                       (?∷ᵖ ~Γ) u<       = cong suc (idxˣ⁻ᶜ-extractˣᶜ-eraseˣ ~Γ u<)
idxˣ⁻ᶜ-extractˣᶜ-eraseˣ {_ ∷ Δ} {u = 0}     (_ !∷ᶜ ~Γ) (s≤s u<) = refl
idxˣ⁻ᶜ-extractˣᶜ-eraseˣ {_ ∷ Δ} {u = suc u} (_ !∷ᶜ ~Γ) (s≤s u<) = cong suc (idxˣ⁻ᶜ-extractˣᶜ-eraseˣ ~Γ u<)

idxˣ⁻ᶜ-extractˣ⁻ᶜ : ∀ {u : ℕ} →
                    (kk′~ : k ⍮ k′ ~ˣ⁻) →
                    (u< : u ℕ.< k) →
                    idxˣ⁻ᶜ kk′~ u< ≡ idxˣ⁻ᶜ (extractˣ⁻ᶜ kk′~) u<
idxˣ⁻ᶜ-extractˣ⁻ᶜ                         (?∷ᶜ kk′~) u<       = cong suc (idxˣ⁻ᶜ-extractˣ⁻ᶜ kk′~ u<)
idxˣ⁻ᶜ-extractˣ⁻ᶜ                         (!∷ᵖ kk′~) u<       = cong suc (idxˣ⁻ᶜ-extractˣ⁻ᶜ kk′~ u<)
idxˣ⁻ᶜ-extractˣ⁻ᶜ                         (?∷ᵖ kk′~) u<       = cong suc (idxˣ⁻ᶜ-extractˣ⁻ᶜ kk′~ u<)
idxˣ⁻ᶜ-extractˣ⁻ᶜ {k = suc _} {u = 0}     (!∷ᶜ kk′~) (s≤s u<) = refl
idxˣ⁻ᶜ-extractˣ⁻ᶜ {k = suc _} {u = suc u} (!∷ᶜ kk′~) (s≤s u<) = cong suc (idxˣ⁻ᶜ-extractˣ⁻ᶜ kk′~ u<)

extractˣ⁻ᶜ-++ˣ⁻ : (kk′~ : k ⍮ k′ ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
                  extractˣ⁻ᶜ (kk′~ ++ˣ⁻ k″k‴~) ≡ extractˣ⁻ᶜ kk′~ ++ˣ⁻ extractˣ⁻ᶜ k″k‴~
extractˣ⁻ᶜ-++ˣ⁻ []         = refl
extractˣ⁻ᶜ-++ˣ⁻ (!∷ᶜ kk′~) = cong !∷ᶜ_ (extractˣ⁻ᶜ-++ˣ⁻ kk′~)
extractˣ⁻ᶜ-++ˣ⁻ (?∷ᶜ kk′~) = cong ?∷ᶜ_ (extractˣ⁻ᶜ-++ˣ⁻ kk′~)
extractˣ⁻ᶜ-++ˣ⁻ (!∷ᵖ kk′~) = cong ?∷ᵖ_ (extractˣ⁻ᶜ-++ˣ⁻ kk′~)
extractˣ⁻ᶜ-++ˣ⁻ (?∷ᵖ kk′~) = cong ?∷ᵖ_ (extractˣ⁻ᶜ-++ˣ⁻ kk′~)

extractˣ⁻ᶜ-idempotent : (kk′~ : k ⍮ k′ ~ˣ⁻) →
                        extractˣ⁻ᶜ (extractˣ⁻ᶜ kk′~) ≡ extractˣ⁻ᶜ kk′~
extractˣ⁻ᶜ-idempotent []         = refl
extractˣ⁻ᶜ-idempotent (!∷ᶜ kk′~) = cong !∷ᶜ_ (extractˣ⁻ᶜ-idempotent kk′~)
extractˣ⁻ᶜ-idempotent (?∷ᶜ kk′~) = cong ?∷ᶜ_ (extractˣ⁻ᶜ-idempotent kk′~)
extractˣ⁻ᶜ-idempotent (!∷ᵖ kk′~) = cong ?∷ᵖ_ (extractˣ⁻ᶜ-idempotent kk′~)
extractˣ⁻ᶜ-idempotent (?∷ᵖ kk′~) = cong ?∷ᵖ_ (extractˣ⁻ᶜ-idempotent kk′~)

∈ᶜ⇒idxˣ⁻ᶜ-eraseˣ∈ : ∀ {u : ℕ} →
                    (~Γ : DP.Δ ⍮ DP.Γ ~ˣ Γ) →
                    DP.S ~ᵀ S →
                    (u< : u ℕ.< length DP.Δ) →
                    u DP.⦂ DP.S ∈ DP.Δ →
                    idxˣ⁻ᶜ (eraseˣ ~Γ) u< ⦂[ cMode ] `↑ S ∈ Γ
∈ᶜ⇒idxˣ⁻ᶜ-eraseˣ∈ {u = zero}  (~S′ !∷ᶜ ~Γ) ~S (s≤s u<) DP.here
  rewrite ~ᵀ-det ~S′ ~S                                              = here (is-all-del² _)
∈ᶜ⇒idxˣ⁻ᶜ-eraseˣ∈ {u = suc _} (_   !∷ᶜ ~Γ) ~S (s≤s u<) (DP.there u∈) = there (weakening _) (∈ᶜ⇒idxˣ⁻ᶜ-eraseˣ∈ ~Γ ~S u< u∈)
∈ᶜ⇒idxˣ⁻ᶜ-eraseˣ∈                 (?∷ᶜ ~Γ) ~S u<       u∈            = there unusable (∈ᶜ⇒idxˣ⁻ᶜ-eraseˣ∈ ~Γ ~S u< u∈)
∈ᶜ⇒idxˣ⁻ᶜ-eraseˣ∈             (_   !∷ᵖ ~Γ) ~S u<       u∈            = there (weakening _) (∈ᶜ⇒idxˣ⁻ᶜ-eraseˣ∈ ~Γ ~S u< u∈)
∈ᶜ⇒idxˣ⁻ᶜ-eraseˣ∈                 (?∷ᵖ ~Γ) ~S u<       u∈            = there unusable (∈ᶜ⇒idxˣ⁻ᶜ-eraseˣ∈ ~Γ ~S u< u∈)

idxˣ⁻ᶜ-eraseˣ∈⇒∈ᶜ : ∀ {u : ℕ} →
                    (~Γ : DP.Δ ⍮ DP.Γ ~ˣ Γ) →
                    DP.S ~ᵀ S →
                    (u< : u ℕ.< length DP.Δ) →
                    idxˣ⁻ᶜ (eraseˣ ~Γ) u< ⦂[ cMode ] `↑ S ∈ Γ →
                    u DP.⦂ DP.S ∈ DP.Δ
idxˣ⁻ᶜ-eraseˣ∈⇒∈ᶜ                 (?∷ᶜ ~Γ) ~S u<       (there _ u∈) = idxˣ⁻ᶜ-eraseˣ∈⇒∈ᶜ ~Γ ~S u< u∈
idxˣ⁻ᶜ-eraseˣ∈⇒∈ᶜ             (~S′ !∷ᵖ ~Γ) ~S u<       (there _ u∈) = idxˣ⁻ᶜ-eraseˣ∈⇒∈ᶜ ~Γ ~S u< u∈
idxˣ⁻ᶜ-eraseˣ∈⇒∈ᶜ                 (?∷ᵖ ~Γ) ~S u<       (there _ u∈) = idxˣ⁻ᶜ-eraseˣ∈⇒∈ᶜ ~Γ ~S u< u∈
idxˣ⁻ᶜ-eraseˣ∈⇒∈ᶜ {u = zero}  (~S′ !∷ᶜ ~Γ) ~S (s≤s u<) (here _)
  rewrite ~ᵀ-inj ~S′ ~S                                             = DP.here
idxˣ⁻ᶜ-eraseˣ∈⇒∈ᶜ {u = suc _} (~S′ !∷ᶜ ~Γ) ~S (s≤s u<) (there _ u∈) = DP.there (idxˣ⁻ᶜ-eraseˣ∈⇒∈ᶜ ~Γ ~S u< u∈)

∈ᵖ⇒idxˣ⁻ᵖ-eraseˣ∈ : ∀ {x : ℕ} →
                    (~Γ : DP.Δ ⍮ DP.Γ ~ˣ Γ) →
                    DP.S ~ᵀ S →
                    (x< : x ℕ.< length DP.Γ) →
                    x DP.⦂ DP.S ∈ DP.Γ →
                    idxˣ⁻ᵖ (eraseˣ ~Γ) x< ⦂[ pMode ] S ∈ Γ
∈ᵖ⇒idxˣ⁻ᵖ-eraseˣ∈ {x = zero}  (~S′ !∷ᵖ ~Γ) ~S (s≤s x<) DP.here
  rewrite ~ᵀ-det ~S′ ~S                                              = here (is-all-del² _)
∈ᵖ⇒idxˣ⁻ᵖ-eraseˣ∈ {x = suc _} (_   !∷ᵖ ~Γ) ~S (s≤s x<) (DP.there x∈) = there (weakening _) (∈ᵖ⇒idxˣ⁻ᵖ-eraseˣ∈ ~Γ ~S x< x∈)
∈ᵖ⇒idxˣ⁻ᵖ-eraseˣ∈                 (?∷ᵖ ~Γ) ~S x<       x∈            = there unusable (∈ᵖ⇒idxˣ⁻ᵖ-eraseˣ∈ ~Γ ~S x< x∈)
∈ᵖ⇒idxˣ⁻ᵖ-eraseˣ∈             (_   !∷ᶜ ~Γ) ~S x<       x∈            = there (weakening _) (∈ᵖ⇒idxˣ⁻ᵖ-eraseˣ∈ ~Γ ~S x< x∈)
∈ᵖ⇒idxˣ⁻ᵖ-eraseˣ∈                 (?∷ᶜ ~Γ) ~S x<       x∈            = there unusable (∈ᵖ⇒idxˣ⁻ᵖ-eraseˣ∈ ~Γ ~S x< x∈)

idxˣ⁻ᵖ-eraseˣ∈⇒∈ᵖ : ∀ {x : ℕ} →
                    (~Γ : DP.Δ ⍮ DP.Γ ~ˣ Γ) →
                    DP.S ~ᵀ S →
                    (x< : x ℕ.< length DP.Γ) →
                    idxˣ⁻ᵖ (eraseˣ ~Γ) x< ⦂[ pMode ] S ∈ Γ →
                    x DP.⦂ DP.S ∈ DP.Γ
idxˣ⁻ᵖ-eraseˣ∈⇒∈ᵖ {x = zero}  (~S′ !∷ᵖ ~Γ) ~S (s≤s x<) (here _)
  rewrite ~ᵀ-inj ~S′ ~S                                             = DP.here
idxˣ⁻ᵖ-eraseˣ∈⇒∈ᵖ {x = suc _} (_   !∷ᵖ ~Γ) ~S (s≤s x<) (there _ x∈) = DP.there (idxˣ⁻ᵖ-eraseˣ∈⇒∈ᵖ ~Γ ~S x< x∈)
idxˣ⁻ᵖ-eraseˣ∈⇒∈ᵖ                 (?∷ᵖ ~Γ) ~S x<       (there _ x∈) = idxˣ⁻ᵖ-eraseˣ∈⇒∈ᵖ ~Γ ~S x< x∈
idxˣ⁻ᵖ-eraseˣ∈⇒∈ᵖ             (_   !∷ᶜ ~Γ) ~S x<       (there _ x∈) = idxˣ⁻ᵖ-eraseˣ∈⇒∈ᵖ ~Γ ~S x< x∈
idxˣ⁻ᵖ-eraseˣ∈⇒∈ᵖ                 (?∷ᶜ ~Γ) ~S x<       (there _ x∈) = idxˣ⁻ᵖ-eraseˣ∈⇒∈ᵖ ~Γ ~S x< x∈

idxˣ⁻ᶜ⇒idxˣ⁻ᶜ-++ˣ⁻ : (kk′~ : k ⍮ k′ ~ˣ⁻) (k″k‴~ : k″ ⍮ k‴ ~ˣ⁻) (u< : DP.u ℕ.< k) (u<′ : DP.u ℕ.< k + k″) →
                     idxˣ⁻ᶜ kk′~ u< ≡ idxˣ⁻ᶜ (kk′~ ++ˣ⁻ k″k‴~) u<′
idxˣ⁻ᶜ⇒idxˣ⁻ᶜ-++ˣ⁻             (!∷ᵖ kk′~) k″k‴~ u<        u<′       = cong suc (idxˣ⁻ᶜ⇒idxˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~ u< u<′)
idxˣ⁻ᶜ⇒idxˣ⁻ᶜ-++ˣ⁻             (?∷ᵖ kk′~) k″k‴~ u<        u<′       = cong suc (idxˣ⁻ᶜ⇒idxˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~ u< u<′)
idxˣ⁻ᶜ⇒idxˣ⁻ᶜ-++ˣ⁻             (?∷ᶜ kk′~) k″k‴~ u<        u<′       = cong suc (idxˣ⁻ᶜ⇒idxˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~ u< u<′)
idxˣ⁻ᶜ⇒idxˣ⁻ᶜ-++ˣ⁻ {u = zero}  (!∷ᶜ kk′~) k″k‴~ (s≤s u<)  (s≤s u<′) = refl
idxˣ⁻ᶜ⇒idxˣ⁻ᶜ-++ˣ⁻ {u = suc _} (!∷ᶜ kk′~) k″k‴~ (s≤s u<)  (s≤s u<′) = cong suc (idxˣ⁻ᶜ⇒idxˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~ u< u<′)

idxˣ⁻ᵖ⇒idxˣ⁻ᵖ-++ˣ⁻ : (kk′~ : k ⍮ k′ ~ˣ⁻) (k″k‴~ : k″ ⍮ k‴ ~ˣ⁻) (x< : DP.x ℕ.< k′) (x<′ : DP.x ℕ.< k′ + k‴) →
                     idxˣ⁻ᵖ kk′~ x< ≡ idxˣ⁻ᵖ (kk′~ ++ˣ⁻ k″k‴~) x<′
idxˣ⁻ᵖ⇒idxˣ⁻ᵖ-++ˣ⁻             (!∷ᶜ kk′~) k″k‴~ x<        x<′       = cong suc (idxˣ⁻ᵖ⇒idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x< x<′)
idxˣ⁻ᵖ⇒idxˣ⁻ᵖ-++ˣ⁻             (?∷ᶜ kk′~) k″k‴~ x<        x<′       = cong suc (idxˣ⁻ᵖ⇒idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x< x<′)
idxˣ⁻ᵖ⇒idxˣ⁻ᵖ-++ˣ⁻             (?∷ᵖ kk′~) k″k‴~ x<        x<′       = cong suc (idxˣ⁻ᵖ⇒idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x< x<′)
idxˣ⁻ᵖ⇒idxˣ⁻ᵖ-++ˣ⁻ {x = zero}  (!∷ᵖ kk′~) k″k‴~ (s≤s x<)  (s≤s x<′) = refl
idxˣ⁻ᵖ⇒idxˣ⁻ᵖ-++ˣ⁻ {x = suc _} (!∷ᵖ kk′~) k″k‴~ (s≤s x<)  (s≤s x<′) = cong suc (idxˣ⁻ᵖ⇒idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x< x<′)

~ᴹ⇒++ˣ⁻~ᴹ : (kk′~ : k ⍮ k′ ~ˣ⁻) (k″k‴~ : k″ ⍮ k‴ ~ˣ⁻) →
            kk′~ ⊢ DP.L ~ᴹ L →
            kk′~ ++ˣ⁻ k″k‴~ ⊢ DP.L ~ᴹ L
~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ `unit = `unit
~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ (`box ~L)
  with ~L′ ← ~ᴹ⇒++ˣ⁻~ᴹ (extractˣ⁻ᶜ kk′~) (extractˣ⁻ᶜ k″k‴~) ~L
    rewrite sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~}) = `box ~L′
~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ (`let-box ~L `in ~M) = `let-box (~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ ~L) `in (~ᴹ⇒++ˣ⁻~ᴹ (!∷ᶜ kk′~) k″k‴~ ~M)
~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ (`#¹ u<)
  rewrite idxˣ⁻ᶜ⇒idxˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~ u< (ℕ.≤-trans u< (ℕ.m≤m+n _ _)) = `#¹ (ℕ.≤-trans u< (ℕ.m≤m+n _ _))
~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ (`λ⦂ S~ ∙ ~L) = `λ⦂ S~ ∙ ~ᴹ⇒++ˣ⁻~ᴹ (!∷ᵖ kk′~) k″k‴~ ~L
~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ (~L `$ ~M) = ~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ ~L `$ ~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ ~M
~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ (`#⁰ x<)
  rewrite idxˣ⁻ᵖ⇒idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x< (ℕ.≤-trans x< (ℕ.m≤m+n _ _)) = `#⁰ (ℕ.≤-trans x< (ℕ.m≤m+n _ _))
~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ (`unlift-`lift ~L)
  with ~L′ ← ~ᴹ⇒++ˣ⁻~ᴹ (extractˣ⁻ᶜ kk′~) (extractˣ⁻ᶜ k″k‴~) ~L
    rewrite sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~}) = `unlift-`lift ~L′

extractˣ⁻ᶜ⁻¹-~ᴹ : (kk′~ : k ⍮ k′ ~ˣ⁻) (k″k‴~ : k″ ⍮ k‴ ~ˣ⁻) →
                  kk′~ ++ˣ⁻ extractˣ⁻ᶜ k″k‴~ ⊢ DP.L ~ᴹ L →
                  kk′~ ++ˣ⁻ k″k‴~ ⊢ DP.L ~ᴹ L
extractˣ⁻ᶜ⁻¹-~ᴹ kk′~ k″k‴~ `unit = `unit
extractˣ⁻ᶜ⁻¹-~ᴹ kk′~ k″k‴~ (`box ~L)
  rewrite extractˣ⁻ᶜ-++ˣ⁻ kk′~ {extractˣ⁻ᶜ k″k‴~}
    with ~L′ ← extractˣ⁻ᶜ⁻¹-~ᴹ (extractˣ⁻ᶜ kk′~) (extractˣ⁻ᶜ k″k‴~) ~L
      rewrite sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~}) = `box ~L′
extractˣ⁻ᶜ⁻¹-~ᴹ kk′~ k″k‴~ (`let-box ~L `in ~M) = `let-box extractˣ⁻ᶜ⁻¹-~ᴹ kk′~ k″k‴~ ~L `in extractˣ⁻ᶜ⁻¹-~ᴹ (!∷ᶜ kk′~) k″k‴~ ~M
extractˣ⁻ᶜ⁻¹-~ᴹ kk′~ k″k‴~ (`#¹ u<)
  rewrite idxˣ⁻ᶜ-extractˣ⁻ᶜ (kk′~ ++ˣ⁻ extractˣ⁻ᶜ k″k‴~) u<
        | extractˣ⁻ᶜ-++ˣ⁻ kk′~ {extractˣ⁻ᶜ k″k‴~}
        | extractˣ⁻ᶜ-idempotent k″k‴~
        | sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~})
        | sym (idxˣ⁻ᶜ-extractˣ⁻ᶜ (kk′~ ++ˣ⁻ k″k‴~) u<) = `#¹ u<
extractˣ⁻ᶜ⁻¹-~ᴹ kk′~ k″k‴~ (`λ⦂ ~S ∙ ~L) = `λ⦂ ~S ∙ extractˣ⁻ᶜ⁻¹-~ᴹ (!∷ᵖ kk′~) k″k‴~ ~L
extractˣ⁻ᶜ⁻¹-~ᴹ kk′~ k″k‴~ (~L `$ ~M) = extractˣ⁻ᶜ⁻¹-~ᴹ kk′~ k″k‴~ ~L `$ extractˣ⁻ᶜ⁻¹-~ᴹ kk′~ k″k‴~ ~M
extractˣ⁻ᶜ⁻¹-~ᴹ {k′ = k′} kk′~ k″k‴~ (`#⁰_ {x = x} x<)
  rewrite sym (idxˣ⁻ᵖ⇒idxˣ⁻ᵖ-++ˣ⁻ kk′~ (extractˣ⁻ᶜ k″k‴~) (subst (x ℕ.<_) (ℕ.+-identityʳ k′) x<) x<)
        | idxˣ⁻ᵖ⇒idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ (subst (x ℕ.<_) (ℕ.+-identityʳ k′) x<) (ℕ.≤-trans (subst (x ℕ.<_) (ℕ.+-identityʳ k′) x<) (ℕ.m≤m+n _ _)) = `#⁰ (ℕ.≤-trans (subst (x ℕ.<_) (ℕ.+-identityʳ k′) x<) (ℕ.m≤m+n _ _))
extractˣ⁻ᶜ⁻¹-~ᴹ kk′~ k″k‴~ (`unlift-`lift ~L)
  rewrite extractˣ⁻ᶜ-++ˣ⁻ kk′~ {extractˣ⁻ᶜ k″k‴~}
    with ~L′ ← extractˣ⁻ᶜ⁻¹-~ᴹ (extractˣ⁻ᶜ kk′~) (extractˣ⁻ᶜ k″k‴~) ~L
      rewrite sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~}) = `unlift-`lift ~L′

extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ : (kk′~ : k ⍮ k′ ~ˣ⁻) (k″k‴~ : k″ ⍮ k‴ ~ˣ⁻) (~L : kk′~ ++ˣ⁻ extractˣ⁻ᶜ k″k‴~ ⊢ DP.L ~ᴹ L) →
                          depth~ᴹ (extractˣ⁻ᶜ⁻¹-~ᴹ kk′~ k″k‴~ ~L) ≡ depth~ᴹ ~L
extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ kk′~ k″k‴~ `unit = refl
extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ kk′~ k″k‴~ (`box ~L)
  rewrite extractˣ⁻ᶜ-++ˣ⁻ kk′~ {extractˣ⁻ᶜ k″k‴~}
    with ~L′ ← extractˣ⁻ᶜ⁻¹-~ᴹ (extractˣ⁻ᶜ kk′~) (extractˣ⁻ᶜ k″k‴~) ~L
       | eq ← extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ  (extractˣ⁻ᶜ kk′~) (extractˣ⁻ᶜ k″k‴~) ~L
      rewrite sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~}) = cong suc eq
extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ kk′~ k″k‴~ (`let-box ~L `in ~M) = cong suc (cong₂ ℕ._⊔_ (extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ kk′~ k″k‴~ ~L) (extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ (!∷ᶜ kk′~) k″k‴~ ~M))
extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ kk′~ k″k‴~ (`#¹ u<)
  rewrite idxˣ⁻ᶜ-extractˣ⁻ᶜ (kk′~ ++ˣ⁻ extractˣ⁻ᶜ k″k‴~) u<
        | extractˣ⁻ᶜ-++ˣ⁻ kk′~ {extractˣ⁻ᶜ k″k‴~}
        | extractˣ⁻ᶜ-idempotent k″k‴~
        | sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~})
        | sym (idxˣ⁻ᶜ-extractˣ⁻ᶜ (kk′~ ++ˣ⁻ k″k‴~) u<) = refl
extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ kk′~ k″k‴~ (`λ⦂ ~S ∙ ~L) = cong suc (extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ (!∷ᵖ kk′~) k″k‴~ ~L)
extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ kk′~ k″k‴~ (~L `$ ~M) = cong suc (cong₂ ℕ._⊔_ (extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ kk′~ k″k‴~ ~L) (extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ kk′~ k″k‴~ ~M))
extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ {k′ = k′} kk′~ k″k‴~ (`#⁰_ {x = x} x<)
  rewrite sym (idxˣ⁻ᵖ⇒idxˣ⁻ᵖ-++ˣ⁻ kk′~ (extractˣ⁻ᶜ k″k‴~) (subst (x ℕ.<_) (ℕ.+-identityʳ k′) x<) x<)
        | idxˣ⁻ᵖ⇒idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ (subst (x ℕ.<_) (ℕ.+-identityʳ k′) x<) (ℕ.≤-trans (subst (x ℕ.<_) (ℕ.+-identityʳ k′) x<) (ℕ.m≤m+n _ _)) = refl
extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ kk′~ k″k‴~ (`unlift-`lift ~L)
  rewrite extractˣ⁻ᶜ-++ˣ⁻ kk′~ {extractˣ⁻ᶜ k″k‴~}
    with ~L′ ← extractˣ⁻ᶜ⁻¹-~ᴹ (extractˣ⁻ᶜ kk′~) (extractˣ⁻ᶜ k″k‴~) ~L
       | eq ← extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ (extractˣ⁻ᶜ kk′~) (extractˣ⁻ᶜ k″k‴~) ~L
      rewrite sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~}) = cong suc eq

~ᴹ∧++⊢⇒⊢-helper : {kk′~ : (length DP.Δ) ⍮ (length DP.Γ₀) ~ˣ⁻} →
                  (~L : kk′~ ⊢ DP.L ~ᴹ L) →
                  DP.Δ DP.⍮ DP.Γ₀ ++ DP.Γ₁ ⊢ DP.L ⦂ DP.T →
                  Acc ℕ._<_ (depth~ᴹ ~L) →
                  DP.Δ DP.⍮ DP.Γ₀ ⊢ DP.L ⦂ DP.T
~ᴹ∧++⊢⇒⊢-helper `unit DP.`unit (acc r) = DP.`unit
~ᴹ∧++⊢⇒⊢-helper (`box ~L) (DP.`box ⊢DPL) (acc r) = DP.`box ⊢DPL
~ᴹ∧++⊢⇒⊢-helper (`let-box ~L `in ~M) (DP.`let-box ⊢DPL `in ⊢DPM) (acc r) = DP.`let-box ~ᴹ∧++⊢⇒⊢-helper ~L ⊢DPL (r _ (s≤s (ℕ.m≤m⊔n _ _))) `in ~ᴹ∧++⊢⇒⊢-helper ~M ⊢DPM (r _ (s≤s (ℕ.m≤n⊔m _ _)))
~ᴹ∧++⊢⇒⊢-helper (`#¹ u<) (DP.`#¹ u∈) (acc r) = DP.`#¹ u∈
~ᴹ∧++⊢⇒⊢-helper (`λ⦂ ~S ∙ ~L) (DP.`λ⦂-∙ ⊢DPL) (acc r) = DP.`λ⦂-∙ (~ᴹ∧++⊢⇒⊢-helper ~L ⊢DPL (r _ (ℕ.n<1+n _)))
~ᴹ∧++⊢⇒⊢-helper (~L `$ ~M) (⊢DPL DP.`$ ⊢DPM) (acc r) = ~ᴹ∧++⊢⇒⊢-helper ~L ⊢DPL (r _ (s≤s (ℕ.m≤m⊔n _ _))) DP.`$ ~ᴹ∧++⊢⇒⊢-helper ~M ⊢DPM (r _ (s≤s (ℕ.m≤n⊔m _ _)))
~ᴹ∧++⊢⇒⊢-helper (`#⁰ x<) (DP.`#⁰ x∈) (acc r) = DP.`#⁰ DP.>∈-++⇒∈ _ x< x∈
~ᴹ∧++⊢⇒⊢-helper (`unlift-`lift ~L) ⊢DPL (acc r) = ~ᴹ∧++⊢⇒⊢-helper (extractˣ⁻ᶜ⁻¹-~ᴹ [] _ ~L) ⊢DPL (r _ (subst (ℕ._< suc (depth~ᴹ ~L)) (sym (extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ [] _ ~L)) (ℕ.n<1+n (depth~ᴹ ~L))))

~ᴹ∧++⊢⇒⊢ : {kk′~ : (length DP.Δ) ⍮ (length DP.Γ₀) ~ˣ⁻} →
           kk′~ ⊢ DP.L ~ᴹ L →
           DP.Δ DP.⍮ DP.Γ₀ ++ DP.Γ₁ ⊢ DP.L ⦂ DP.T →
           DP.Δ DP.⍮ DP.Γ₀ ⊢ DP.L ⦂ DP.T
~ᴹ∧++⊢⇒⊢ ~L ⊢DPL = ~ᴹ∧++⊢⇒⊢-helper ~L ⊢DPL (ℕ.<-wellFounded _)

~ᴹ-soundness : (ΔΓ~ : DP.Δ ⍮ DP.Γ ~ˣ Γ) →
               DP.S ~ᵀ S →
               eraseˣ ΔΓ~ ⊢ DP.L ~ᴹ L →
               DP.Δ DP.⍮ DP.Γ ⊢ DP.L ⦂ DP.S →
               Γ ⊢[ pMode ] L ⦂ S
~ᴹ-soundness ~Γ ~S (`let-box ~L `in ~M) (DP.`let-box_`in_ {T = DPT} ⊢DPL ⊢DPM)
  with _ , ~T ← ~ᵀ-total DPT = ~⊞² _ ⊢`let-return ~ᴹ-soundness ~Γ (`□ ~T) ~L ⊢DPL  ⦂ ⊢`↓ (λ ()) (⊢`↑ (λ ()) (~ᵀ⇒⊢ ~T)) `in ~ᴹ-soundness (~T !∷ᶜ ~Γ) ~S ~M ⊢DPM
~ᴹ-soundness ~Γ ~S (`#¹ u<) (DP.`#¹ u∈)
  with _ , ~Γ′ ← extractˣᶜ ~Γ
     | ∤Γ′ ← extractˣᶜ-∤ ~Γ
     | eq ← idxˣ⁻ᶜ-extractˣᶜ-eraseˣ ~Γ u<  = ∤Γ′ ⊢`unlift (`# subst (_⦂[ _ ] _ ∈ _) (sym eq) (∈ᶜ⇒idxˣ⁻ᶜ-eraseˣ∈ ~Γ′ ~S u< u∈)) ⦂ (⊢`↑ (λ ()) (~ᵀ⇒⊢ ~S))
~ᴹ-soundness ~Γ (~S′ `→ ~T) (`λ⦂ ~S ∙ ~L) (DP.`λ⦂-∙ ⊢DPL)
  with refl ← ~ᵀ-det ~S′ ~S                                = `λ⦂-∘ ~ᴹ-soundness (~S !∷ᵖ ~Γ) ~T ~L ⊢DPL
~ᴹ-soundness ~Γ ~S (~L `$ ~M) (DP._`$_ {T = DPT} ⊢DPL ⊢DPM)
  with _ , ~T ← ~ᵀ-total DPT = ~⊞² _ ⊢ ~ᴹ-soundness ~Γ (~T `→ ~S) ~L ⊢DPL ⦂ ⊢ ~ᵀ⇒⊢ ~T `⊸ ~ᵀ⇒⊢ ~S `$ ~ᴹ-soundness ~Γ ~T ~M ⊢DPM
~ᴹ-soundness ~Γ ~S (`#⁰ x<) (DP.`#⁰ x∈) = `# ∈ᵖ⇒idxˣ⁻ᵖ-eraseˣ∈ ~Γ ~S x< x∈
~ᴹ-soundness ~Γ ~S (`unlift-`lift ~L) ⊢DPL
  with _ , ~Γ′ ← extractˣᶜ ~Γ
     | ∤Γ′ ← extractˣᶜ-∤ ~Γ
     | eq ← extractˣᶜ-eraseˣ-extractˣ⁻ᶜ ~Γ = ∤Γ′ ⊢`unlift ⊢`lift (~ᴹ-soundness ~Γ′ ~S (subst (_⊢ _ ~ᴹ _) eq ~L) (~ᴹ∧++⊢⇒⊢ ~L ⊢DPL)) ⦂ (⊢`↑ (λ ()) (~ᵀ⇒⊢ ~S))
~ᴹ-soundness ~Γ `⊤ `unit DP.`unit = `unit (is-all-del² _)
~ᴹ-soundness ~Γ (`□ ~S) (`box ~L) (DP.`box ⊢DPL)
  with _ , ~Γ′ ← extractˣᶜ ~Γ
     | ∤Γ′ ← extractˣᶜ-∤ ~Γ
     | eq ← extractˣᶜ-eraseˣ-extractˣ⁻ᶜ ~Γ = ∤Γ′ ⊢`return ⊢`lift (~ᴹ-soundness ~Γ′ ~S (subst (_⊢ _ ~ᴹ _) eq ~L) ⊢DPL)

∤-extractˣᶜ : (~Γ : DP.Δ ⍮ DP.Γ ~ˣ Γ) →
              Γ ∤[ cMode ] Γ′ →
              Γ′ ≡ proj₁ (extractˣᶜ ~Γ)
∤-extractˣᶜ []         [] = refl
∤-extractˣᶜ (_ !∷ᶜ ~Γ) (delete ≰cMode _ ∷ Γ∤) with () ← ≰cMode refl
∤-extractˣᶜ (_ !∷ᶜ ~Γ) (keep   _        ∷ Γ∤) = cong (_ ∷_) (∤-extractˣᶜ ~Γ Γ∤)
∤-extractˣᶜ   (?∷ᶜ ~Γ) (delete ≰cMode _ ∷ Γ∤) with () ← ≰cMode refl
∤-extractˣᶜ   (?∷ᶜ ~Γ) (keep _          ∷ Γ∤) = cong (_ ∷_) (∤-extractˣᶜ ~Γ Γ∤)
∤-extractˣᶜ (_ !∷ᵖ ~Γ) (delete ≰cMode _ ∷ Γ∤) = cong (_ ∷_) (∤-extractˣᶜ ~Γ Γ∤)
∤-extractˣᶜ   (?∷ᵖ ~Γ) (delete ≰cMode _ ∷ Γ∤) = cong (_ ∷_) (∤-extractˣᶜ ~Γ Γ∤)

∈ᵖ⇒~ᵀ : DP.Δ ⍮ DP.Γ ~ˣ Γ →
         x ⦂[ pMode ] S ∈ Γ →
         ∃ (λ DPS → DPS ~ᵀ S)
∈ᵖ⇒~ᵀ (_  !∷ᶜ ~Γ) (there _ x∈) = ∈ᵖ⇒~ᵀ ~Γ x∈
∈ᵖ⇒~ᵀ    (?∷ᶜ ~Γ) (there _ x∈) = ∈ᵖ⇒~ᵀ ~Γ x∈
∈ᵖ⇒~ᵀ (~S !∷ᵖ ~Γ) (here _)     = -, ~S
∈ᵖ⇒~ᵀ (_  !∷ᵖ ~Γ) (there _ x∈) = ∈ᵖ⇒~ᵀ ~Γ x∈
∈ᵖ⇒~ᵀ    (?∷ᵖ ~Γ) (there _ x∈) = ∈ᵖ⇒~ᵀ ~Γ x∈

∈ᶜ⇒~ᵀ : DP.Δ ⍮ DP.Γ ~ˣ Γ →
         x ⦂[ cMode ] `↑ S ∈ Γ →
         ∃ (λ DPS → DPS ~ᵀ S)
∈ᶜ⇒~ᵀ (~S !∷ᶜ ~Γ) (here _)     = -, ~S
∈ᶜ⇒~ᵀ (_  !∷ᶜ ~Γ) (there _ x∈) = ∈ᶜ⇒~ᵀ ~Γ x∈
∈ᶜ⇒~ᵀ    (?∷ᶜ ~Γ) (there _ x∈) = ∈ᶜ⇒~ᵀ ~Γ x∈
∈ᶜ⇒~ᵀ (_  !∷ᵖ ~Γ) (there _ x∈) = ∈ᶜ⇒~ᵀ ~Γ x∈
∈ᶜ⇒~ᵀ    (?∷ᵖ ~Γ) (there _ x∈) = ∈ᶜ⇒~ᵀ ~Γ x∈

~ᴹ∧⊢⇒~ᵀ : (~Γ : DP.Δ ⍮ DP.Γ ~ˣ Γ) →
          eraseˣ ~Γ ⊢ DP.L′ ~ᴹ L →
          Γ ⊢[ pMode ] L ⦂ S →
          ∃ (λ DPS → DPS ~ᵀ S)
~ᴹ∧⊢⇒~ᵀ ~Γ `unit (`unit _) = -, `⊤
~ᴹ∧⊢⇒~ᵀ ~Γ (`box ~L) (Γ∤ ⊢`return (⊢`lift ⊢L))
  rewrite extractˣᶜ-eraseˣ-extractˣ⁻ᶜ ~Γ
        | ∤-extractˣᶜ ~Γ Γ∤                 = -, `□ (proj₂ (~ᴹ∧⊢⇒~ᵀ (proj₂ (extractˣᶜ ~Γ)) ~L ⊢L))
~ᴹ∧⊢⇒~ᵀ ~Γ (`let-box ~L `in ~M) (Γ~ ⊢`let-return ⊢L ⦂ ⊢↓ `in ⊢M)
  with _ , `□ ~T ← ~ᴹ∧⊢⇒~ᵀ ~Γ ~L (~⊞-is-all-del∧⊢⇒⊢ (~⊞-swap Γ~) (is-all-del² _) ⊢L) = ~ᴹ∧⊢⇒~ᵀ (~T !∷ᶜ ~Γ) ~M (~⊞-is-all-del∧⊢⇒⊢ (contraction _ ∷ Γ~) (is-all-del² _) ⊢M)
~ᴹ∧⊢⇒~ᵀ ~Γ (`#¹ u<) (Γ∤ ⊢`unlift `# u∈ ⦂ x₁)
  rewrite ∤-extractˣᶜ ~Γ Γ∤ = ∈ᶜ⇒~ᵀ (proj₂ (extractˣᶜ ~Γ)) u∈ 
~ᴹ∧⊢⇒~ᵀ ~Γ (`λ⦂ ~S ∙ ~L) (`λ⦂-∘ ⊢L) = -, ~S `→ (proj₂ (~ᴹ∧⊢⇒~ᵀ (~S !∷ᵖ ~Γ) ~L ⊢L))
~ᴹ∧⊢⇒~ᵀ ~Γ (~L `$ ~M) (Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)
  with _ , _ `→ ~S ← ~ᴹ∧⊢⇒~ᵀ ~Γ ~L (~⊞-is-all-del∧⊢⇒⊢ (~⊞-swap Γ~) (is-all-del² _) ⊢L) = -, ~S
~ᴹ∧⊢⇒~ᵀ ~Γ (`#⁰ x<) (`# x∈) = ∈ᵖ⇒~ᵀ ~Γ x∈
~ᴹ∧⊢⇒~ᵀ ~Γ (`unlift-`lift ~L) (Γ∤ ⊢`unlift ⊢`lift ⊢L ⦂ ⊢↑)
  rewrite extractˣᶜ-eraseˣ-extractˣ⁻ᶜ ~Γ
        | ∤-extractˣᶜ ~Γ Γ∤ = ~ᴹ∧⊢⇒~ᵀ (proj₂ (extractˣᶜ ~Γ)) ~L ⊢L

⊢⇒++⊢ : ∀ DPΓ₁ →
        DP.Δ DP.⍮ DP.Γ₀ ⊢ DP.L ⦂ DP.S →
        DP.Δ DP.⍮ DP.Γ₀ ++ DPΓ₁ ⊢ DP.L ⦂ DP.S
⊢⇒++⊢ DPΓ₁ DP.`unit = DP.`unit
⊢⇒++⊢ DPΓ₁ (DP.`box ⊢DPL) = DP.`box ⊢DPL
⊢⇒++⊢ DPΓ₁ (DP.`let-box ⊢DPL `in ⊢DPM) = DP.`let-box ⊢⇒++⊢ DPΓ₁ ⊢DPL `in ⊢⇒++⊢ DPΓ₁ ⊢DPM
⊢⇒++⊢ DPΓ₁ (DP.`λ⦂-∙ ⊢DPL) = DP.`λ⦂-∙ ⊢⇒++⊢ DPΓ₁ ⊢DPL
⊢⇒++⊢ DPΓ₁ (⊢DPL DP.`$ ⊢DPM) = ⊢⇒++⊢ DPΓ₁ ⊢DPL DP.`$ ⊢⇒++⊢ DPΓ₁ ⊢DPM
⊢⇒++⊢ DPΓ₁ (DP.`#¹ u∈) = DP.`#¹ u∈
⊢⇒++⊢ DPΓ₁ (DP.`#⁰ x∈) = DP.`#⁰ DP.∈-++ʳ DPΓ₁ x∈

~ᴹ-completeness : (ΔΓ~ : DP.Δ ⍮ DP.Γ ~ˣ Γ) →
                  DP.S ~ᵀ S →
                  eraseˣ ΔΓ~ ⊢ DP.L ~ᴹ L →
                  Γ ⊢[ pMode ] L ⦂ S →
                  DP.Δ DP.⍮ DP.Γ ⊢ DP.L ⦂ DP.S
~ᴹ-completeness ~Γ ~S (`let-box ~L `in ~M) (Γ~ ⊢`let-return ⊢L ⦂ ⊢↓ `in ⊢M)
  with _ , `□ ~T ← ~ᴹ∧⊢⇒~ᵀ ~Γ ~L (~⊞-is-all-del∧⊢⇒⊢ (~⊞-swap Γ~) (is-all-del² _) ⊢L) = DP.`let-box ~ᴹ-completeness ~Γ (`□ ~T) ~L (~⊞-is-all-del∧⊢⇒⊢ (~⊞-swap Γ~) (is-all-del² _) ⊢L) `in ~ᴹ-completeness (~T !∷ᶜ ~Γ) ~S ~M (~⊞-is-all-del∧⊢⇒⊢ (contraction _ ∷ Γ~) (is-all-del² _) ⊢M)
~ᴹ-completeness ~Γ ~S (`#¹ u<) (Γ∤ ⊢`unlift `# u∈ ⦂ ⊢↑)
  rewrite idxˣ⁻ᶜ-extractˣᶜ-eraseˣ ~Γ u<
        | ∤-extractˣᶜ ~Γ Γ∤ = DP.`#¹ idxˣ⁻ᶜ-eraseˣ∈⇒∈ᶜ (proj₂ (extractˣᶜ ~Γ)) ~S u< u∈ 
~ᴹ-completeness ~Γ (~S′ `→ ~T) (`λ⦂ ~S ∙ ~L) (`λ⦂-∘ ⊢L)
  with refl ← ~ᵀ-inj ~S ~S′ = DP.`λ⦂-∙ ~ᴹ-completeness (~S !∷ᵖ ~Γ) ~T ~L ⊢L
~ᴹ-completeness ~Γ ~S (~L `$ ~M) (Γ~ ⊢ ⊢L ⦂ ⊢⊸ `$ ⊢M)
  with _ , ~⊸@(~T `→ ~S′) ← ~ᴹ∧⊢⇒~ᵀ ~Γ ~L (~⊞-is-all-del∧⊢⇒⊢ (~⊞-swap Γ~) (is-all-del² _) ⊢L)
    with refl ← ~ᵀ-inj ~S ~S′ = ~ᴹ-completeness ~Γ ~⊸ ~L (~⊞-is-all-del∧⊢⇒⊢ (~⊞-swap Γ~) (is-all-del² _) ⊢L) DP.`$ ~ᴹ-completeness ~Γ ~T ~M (~⊞-is-all-del∧⊢⇒⊢ Γ~ (is-all-del² _) ⊢M)
~ᴹ-completeness ~Γ ~S (`#⁰ x<) (`# x∈) = DP.`#⁰ idxˣ⁻ᵖ-eraseˣ∈⇒∈ᵖ ~Γ ~S x< x∈
~ᴹ-completeness ~Γ ~S (`unlift-`lift ~L) (Γ∤ ⊢`unlift ⊢`lift ⊢L ⦂ ⊢↑)
  rewrite extractˣᶜ-eraseˣ-extractˣ⁻ᶜ ~Γ
        | ∤-extractˣᶜ ~Γ Γ∤ = ⊢⇒++⊢ _ (~ᴹ-completeness (proj₂ (extractˣᶜ ~Γ)) ~S ~L ⊢L)
~ᴹ-completeness ~Γ `⊤ `unit (`unit _) = DP.`unit
~ᴹ-completeness ~Γ (`□ ~S) (`box ~L) (Γ∤ ⊢`return (⊢`lift ⊢L))
  rewrite extractˣᶜ-eraseˣ-extractˣ⁻ᶜ ~Γ
        | ∤-extractˣᶜ ~Γ Γ∤ = DP.`box (~ᴹ-completeness (proj₂ (extractˣᶜ ~Γ)) ~S ~L ⊢L)

~ᴹ-normalize[≤] : (~L : kk′~ ⊢ DP.L ~ᴹ L) →
                  ∃ λ L′ → L ⟶[ cMode ≤]* L′ × DeferredTerm[ cMode ≤] L′ × Σ (kk′~ ⊢ DP.L ~ᴹ L′) λ ~L′ → depth~ᴹ ~L′ ℕ.≤ depth~ᴹ ~L
~ᴹ-normalize[≤] `unit                                     = -, ε
                                                          , `unit
                                                          , `unit
                                                          , z≤n
~ᴹ-normalize[≤] (`box ~L)
  with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L = -, ξ-of-↝*-⟶[ cMode ≤]* _⟶_ `return ξ-`return≤ (ξ-of-↝*-⟶* _⟶[ cMode ≤]_ `lift ξ-`lift[-⇒-] ⟶*L′[≤])
                                                          , `return≤ (`lift WL′)
                                                          , `box ~L′
                                                          , s≤s L′≤
~ᴹ-normalize[≤] (`let-box ~L `in ~M)
  with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L
     | _ , ⟶*M′[≤] , WM′ , ~M′ , M′≤ ← ~ᴹ-normalize[≤] ~M = -, ξ-of-⟶[ cMode ≤]* (`let-return_`in _) ξ-`let-return_`in? ⟶*L′[≤]
                                                              ◅◅ ξ-of-⟶[ cMode ≤]* (`let-return _ `in_) (ξ-`let-return! WL′ `in_) ⟶*M′[≤]
                                                          , `let-return WL′ `in WM′
                                                          , `let-box ~L′ `in ~M′
                                                          , s≤s (ℕ.⊔-mono-≤ L′≤ M′≤)
~ᴹ-normalize[≤] (`#¹ u<)                                  = -, ε
                                                          , `unlift≤ (`neut (`# _))
                                                          , `#¹ u<
                                                          , z≤n
~ᴹ-normalize[≤] (`λ⦂ ~S ∙ ~L)
  with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L = -, ξ-of-⟶[ cMode ≤]* (`λ⦂ᵖ _ ∘_) ξ-`λ⦂[-]-∘_ ⟶*L′[≤]
                                                          , `λ⦂ᵖ _ ∘ WL′
                                                          , `λ⦂ ~S ∙ ~L′
                                                          , s≤s L′≤
~ᴹ-normalize[≤] (~L `$ ~M)
  with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L
     | _ , ⟶*M′[≤] , WM′ , ~M′ , M′≤ ← ~ᴹ-normalize[≤] ~M = -, ξ-of-⟶[ cMode ≤]* (_`$ _) ξ-_`$? ⟶*L′[≤]
                                                              ◅◅ ξ-of-⟶[ cMode ≤]* (_ `$_) (ξ-! WL′ `$_) ⟶*M′[≤]
                                                          , WL′ `$ WM′
                                                          , ~L′ `$ ~M′
                                                          , s≤s (ℕ.⊔-mono-≤ L′≤ M′≤)
~ᴹ-normalize[≤] (`#⁰ x<)                                  = -, ε
                                                          , `# _
                                                          , `#⁰ x<
                                                          , z≤n
~ᴹ-normalize[≤] (`unlift-`lift ~L)
  with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L = -, ξ-of-↝*-⟶[ cMode ≤]* _⟶_ `unlift ξ-`unlift≤ (ξ-of-↝*-⟶* (_⟶[ cMode ≤]_) `lift ξ-`lift ⟶*L′[≤])
                                                              ◅◅ β-`↑ refl WL′ ◅ ε
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

~ᴹ-simulation-helper : DP.L DP.⟶ DP.L′ →
                       (DPL~ : [] ⊢ DP.L ~ᴹ L) →
                       Acc ℕ._<_ (depth~ᴹ DPL~) →
                       ∃ λ L′ → L ⟶* L′ × [] ⊢ DP.L′ ~ᴹ L′
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
  with _ , ⟶*L′ , VL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L
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
 
