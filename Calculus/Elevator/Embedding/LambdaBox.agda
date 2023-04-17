module Calculus.Elevator.Embedding.LambdaBox where

open import Agda.Primitive
open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_; _++_; length)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.Nat as ℕ using (ℕ; zero; suc; z≤n; s≤s; _+_; _∸_)
import Data.Nat.Properties as ℕ
import Data.Nat.Induction as ℕ
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ; ∃; ∃₂; -,_)
open import Induction.WellFounded using (Acc; acc)
open import Relation.Binary using (Rel; Antisymmetric; IsPartialOrder; IsDecPartialOrder)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; cong₂; subst; ≢-sym)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Decidable using (dec-yes; dec-no)

open import Calculus.GeneralOpSem using (wkidx[_↑_]_; idx[_/_]_along_)
open import Calculus.GeneralOpSem.Properties
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

lengthˣ⁻ : k ⍮ k′ ~ˣ⁻ → ℕ
lengthˣ⁻ []         = 0
lengthˣ⁻ (!∷ᶜ kk′~) = suc (lengthˣ⁻ kk′~)
lengthˣ⁻ (?∷ᶜ kk′~) = suc (lengthˣ⁻ kk′~)
lengthˣ⁻ (!∷ᵖ kk′~) = suc (lengthˣ⁻ kk′~)
lengthˣ⁻ (?∷ᵖ kk′~) = suc (lengthˣ⁻ kk′~)

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

extractˣ⁻ᶜ-lengthˣ⁻ : (kk′~ : k ⍮ k′ ~ˣ⁻) →
                      lengthˣ⁻ (extractˣ⁻ᶜ kk′~) ≡ lengthˣ⁻ kk′~
extractˣ⁻ᶜ-lengthˣ⁻ [] = refl
extractˣ⁻ᶜ-lengthˣ⁻ (!∷ᶜ kk′~) = cong suc (extractˣ⁻ᶜ-lengthˣ⁻ kk′~)
extractˣ⁻ᶜ-lengthˣ⁻ (?∷ᶜ kk′~) = cong suc (extractˣ⁻ᶜ-lengthˣ⁻ kk′~)
extractˣ⁻ᶜ-lengthˣ⁻ (!∷ᵖ kk′~) = cong suc (extractˣ⁻ᶜ-lengthˣ⁻ kk′~)
extractˣ⁻ᶜ-lengthˣ⁻ (?∷ᵖ kk′~) = cong suc (extractˣ⁻ᶜ-lengthˣ⁻ kk′~)

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
∈ᶜ⇒idxˣ⁻ᶜ-eraseˣ∈                 (?∷ᵖ ~Γ) ~S u<       u∈            = there unusable (∈ᶜ⇒idxˣ⁻ᶜ-eraseˣ∈ ~Γ ~S u< u∈)
∈ᶜ⇒idxˣ⁻ᶜ-eraseˣ∈             (_   !∷ᵖ ~Γ) ~S u<       u∈            = there (weakening _) (∈ᶜ⇒idxˣ⁻ᶜ-eraseˣ∈ ~Γ ~S u< u∈)
∈ᶜ⇒idxˣ⁻ᶜ-eraseˣ∈                 (?∷ᶜ ~Γ) ~S u<       u∈            = there unusable (∈ᶜ⇒idxˣ⁻ᶜ-eraseˣ∈ ~Γ ~S u< u∈)
∈ᶜ⇒idxˣ⁻ᶜ-eraseˣ∈ {u = zero}  (~S′ !∷ᶜ ~Γ) ~S (s≤s u<) DP.here
  rewrite ~ᵀ-det ~S′ ~S                                              = here (is-all-del² _)
∈ᶜ⇒idxˣ⁻ᶜ-eraseˣ∈ {u = suc _} (_   !∷ᶜ ~Γ) ~S (s≤s u<) (DP.there u∈) = there (weakening _) (∈ᶜ⇒idxˣ⁻ᶜ-eraseˣ∈ ~Γ ~S u< u∈)

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
∈ᵖ⇒idxˣ⁻ᵖ-eraseˣ∈                 (?∷ᶜ ~Γ) ~S x<       x∈            = there unusable (∈ᵖ⇒idxˣ⁻ᵖ-eraseˣ∈ ~Γ ~S x< x∈)
∈ᵖ⇒idxˣ⁻ᵖ-eraseˣ∈             (_   !∷ᶜ ~Γ) ~S x<       x∈            = there (weakening _) (∈ᵖ⇒idxˣ⁻ᵖ-eraseˣ∈ ~Γ ~S x< x∈)
∈ᵖ⇒idxˣ⁻ᵖ-eraseˣ∈                 (?∷ᵖ ~Γ) ~S x<       x∈            = there unusable (∈ᵖ⇒idxˣ⁻ᵖ-eraseˣ∈ ~Γ ~S x< x∈)
∈ᵖ⇒idxˣ⁻ᵖ-eraseˣ∈ {x = zero}  (~S′ !∷ᵖ ~Γ) ~S (s≤s x<) DP.here
  rewrite ~ᵀ-det ~S′ ~S                                              = here (is-all-del² _)
∈ᵖ⇒idxˣ⁻ᵖ-eraseˣ∈ {x = suc _} (_   !∷ᵖ ~Γ) ~S (s≤s x<) (DP.there x∈) = there (weakening _) (∈ᵖ⇒idxˣ⁻ᵖ-eraseˣ∈ ~Γ ~S x< x∈)

idxˣ⁻ᵖ-eraseˣ∈⇒∈ᵖ : ∀ {x : ℕ} →
                    (~Γ : DP.Δ ⍮ DP.Γ ~ˣ Γ) →
                    DP.S ~ᵀ S →
                    (x< : x ℕ.< length DP.Γ) →
                    idxˣ⁻ᵖ (eraseˣ ~Γ) x< ⦂[ pMode ] S ∈ Γ →
                    x DP.⦂ DP.S ∈ DP.Γ
idxˣ⁻ᵖ-eraseˣ∈⇒∈ᵖ                 (?∷ᶜ ~Γ) ~S x<       (there _ x∈) = idxˣ⁻ᵖ-eraseˣ∈⇒∈ᵖ ~Γ ~S x< x∈
idxˣ⁻ᵖ-eraseˣ∈⇒∈ᵖ             (_   !∷ᶜ ~Γ) ~S x<       (there _ x∈) = idxˣ⁻ᵖ-eraseˣ∈⇒∈ᵖ ~Γ ~S x< x∈
idxˣ⁻ᵖ-eraseˣ∈⇒∈ᵖ                 (?∷ᵖ ~Γ) ~S x<       (there _ x∈) = idxˣ⁻ᵖ-eraseˣ∈⇒∈ᵖ ~Γ ~S x< x∈
idxˣ⁻ᵖ-eraseˣ∈⇒∈ᵖ {x = zero}  (~S′ !∷ᵖ ~Γ) ~S (s≤s x<) (here _)
  rewrite ~ᵀ-inj ~S′ ~S                                             = DP.here
idxˣ⁻ᵖ-eraseˣ∈⇒∈ᵖ {x = suc _} (_   !∷ᵖ ~Γ) ~S (s≤s x<) (there _ x∈) = DP.there (idxˣ⁻ᵖ-eraseˣ∈⇒∈ᵖ ~Γ ~S x< x∈)

<⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ : (kk′~ : k ⍮ k′ ~ˣ⁻) (k″k‴~ : k″ ⍮ k‴ ~ˣ⁻) (u< : DP.u ℕ.< k) (u<′ : DP.u ℕ.< k + k″) →
                       idxˣ⁻ᶜ kk′~ u< ≡ idxˣ⁻ᶜ (kk′~ ++ˣ⁻ k″k‴~) u<′
<⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻             (!∷ᵖ kk′~) k″k‴~ u<        u<′       = cong suc (<⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~ u< u<′)
<⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻             (?∷ᵖ kk′~) k″k‴~ u<        u<′       = cong suc (<⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~ u< u<′)
<⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻             (?∷ᶜ kk′~) k″k‴~ u<        u<′       = cong suc (<⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~ u< u<′)
<⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ {u = zero}  (!∷ᶜ kk′~) k″k‴~ (s≤s u<)  (s≤s u<′) = refl
<⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ {u = suc _} (!∷ᶜ kk′~) k″k‴~ (s≤s u<)  (s≤s u<′) = cong suc (<⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~ u< u<′)

idxˣ⁻ᶜ-<-irrelevant : (kk′~ : k ⍮ k′ ~ˣ⁻) (u< : DP.u ℕ.< k) (u<′ : DP.u ℕ.< k) →
                      idxˣ⁻ᶜ kk′~ u< ≡ idxˣ⁻ᶜ kk′~ u<′
idxˣ⁻ᶜ-<-irrelevant             (?∷ᵖ kk′~) u<        u<′      = cong suc (idxˣ⁻ᶜ-<-irrelevant kk′~ u< u<′)
idxˣ⁻ᶜ-<-irrelevant             (!∷ᵖ kk′~) u<        u<′      = cong suc (idxˣ⁻ᶜ-<-irrelevant kk′~ u< u<′)
idxˣ⁻ᶜ-<-irrelevant             (?∷ᶜ kk′~) u<        u<′      = cong suc (idxˣ⁻ᶜ-<-irrelevant kk′~ u< u<′)
idxˣ⁻ᶜ-<-irrelevant {u = zero}  (!∷ᶜ kk′~) (s≤s u<) (s≤s u<′) = refl
idxˣ⁻ᶜ-<-irrelevant {u = suc u} (!∷ᶜ kk′~) (s≤s u<) (s≤s u<′) = cong suc (idxˣ⁻ᶜ-<-irrelevant kk′~ u< u<′)

idxˣ⁻ᶜ<lengthˣ⁻ : ∀ {u} →
                  (kk′~ : k ⍮ k′ ~ˣ⁻) →
                  (u< : u ℕ.< k) →
                  idxˣ⁻ᶜ kk′~ u< ℕ.< lengthˣ⁻ kk′~
idxˣ⁻ᶜ<lengthˣ⁻             (?∷ᵖ kk′~) u<       = s≤s (idxˣ⁻ᶜ<lengthˣ⁻ kk′~ u<)
idxˣ⁻ᶜ<lengthˣ⁻             (!∷ᵖ kk′~) u<       = s≤s (idxˣ⁻ᶜ<lengthˣ⁻ kk′~ u<)
idxˣ⁻ᶜ<lengthˣ⁻             (?∷ᶜ kk′~) u<       = s≤s (idxˣ⁻ᶜ<lengthˣ⁻ kk′~ u<)
idxˣ⁻ᶜ<lengthˣ⁻ {u = zero}  (!∷ᶜ kk′~) (s≤s u<) = s≤s z≤n
idxˣ⁻ᶜ<lengthˣ⁻ {u = suc u} (!∷ᶜ kk′~) (s≤s u<) = s≤s (idxˣ⁻ᶜ<lengthˣ⁻ kk′~ u<)

≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ : (kk′~ : k ⍮ k′ ~ˣ⁻) (k″k‴~ : k″ ⍮ k‴ ~ˣ⁻) →
                                DP.u ℕ.≥ k →
                                (u<′ : DP.u ℕ.< k + k″) (u<″ : DP.u ∸ k ℕ.< k″) →
                                lengthˣ⁻ kk′~ + idxˣ⁻ᶜ k″k‴~ u<″ ≡ idxˣ⁻ᶜ (kk′~ ++ˣ⁻ k″k‴~) u<′
≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻             []         k″k‴~ u≥       u<′       u<″ = idxˣ⁻ᶜ-<-irrelevant k″k‴~ u<″ u<′
≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻             (?∷ᵖ kk′~) k″k‴~ u≥       u<′       u<″ = cong suc (≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~ u≥ u<′ u<″)
≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻             (!∷ᵖ kk′~) k″k‴~ u≥       u<′       u<″ = cong suc (≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~ u≥ u<′ u<″)
≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻             (?∷ᶜ kk′~) k″k‴~ u≥       u<′       u<″ = cong suc (≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~ u≥ u<′ u<″)
≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ {u = suc u} (!∷ᶜ kk′~) k″k‴~ (s≤s u≥) (s≤s u<′) u<″ = cong suc (≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~ u≥ u<′ u<″)

idxˣ⁻ᵖ<lengthˣ⁻ : (kk′~ : k ⍮ k′ ~ˣ⁻) →
                  (x< : x ℕ.< k′) →
                  idxˣ⁻ᵖ kk′~ x< ℕ.< lengthˣ⁻ kk′~
idxˣ⁻ᵖ<lengthˣ⁻             (?∷ᶜ kk′~) x<       = s≤s (idxˣ⁻ᵖ<lengthˣ⁻ kk′~ x<)
idxˣ⁻ᵖ<lengthˣ⁻             (!∷ᶜ kk′~) x<       = s≤s (idxˣ⁻ᵖ<lengthˣ⁻ kk′~ x<)
idxˣ⁻ᵖ<lengthˣ⁻             (?∷ᵖ kk′~) x<       = s≤s (idxˣ⁻ᵖ<lengthˣ⁻ kk′~ x<)
idxˣ⁻ᵖ<lengthˣ⁻ {x = zero}  (!∷ᵖ kk′~) (s≤s x<) = s≤s z≤n
idxˣ⁻ᵖ<lengthˣ⁻ {x = suc u} (!∷ᵖ kk′~) (s≤s x<) = s≤s (idxˣ⁻ᵖ<lengthˣ⁻ kk′~ x<)

<⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ : (kk′~ : k ⍮ k′ ~ˣ⁻) (k″k‴~ : k″ ⍮ k‴ ~ˣ⁻) (x< : DP.x ℕ.< k′) (x<′ : DP.x ℕ.< k′ + k‴) →
                       idxˣ⁻ᵖ kk′~ x< ≡ idxˣ⁻ᵖ (kk′~ ++ˣ⁻ k″k‴~) x<′
<⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻             (!∷ᶜ kk′~) k″k‴~ x<        x<′       = cong suc (<⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x< x<′)
<⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻             (?∷ᶜ kk′~) k″k‴~ x<        x<′       = cong suc (<⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x< x<′)
<⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻             (?∷ᵖ kk′~) k″k‴~ x<        x<′       = cong suc (<⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x< x<′)
<⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ {x = zero}  (!∷ᵖ kk′~) k″k‴~ (s≤s x<)  (s≤s x<′) = refl
<⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ {x = suc _} (!∷ᵖ kk′~) k″k‴~ (s≤s x<)  (s≤s x<′) = cong suc (<⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x< x<′)

idxˣ⁻ᵖ-<-irrelevant : (kk′~ : k ⍮ k′ ~ˣ⁻) (x< : x ℕ.< k′) (x<′ : x ℕ.< k′) →
                      idxˣ⁻ᵖ kk′~ x< ≡ idxˣ⁻ᵖ kk′~ x<′
idxˣ⁻ᵖ-<-irrelevant             (?∷ᶜ kk′~) x<        x<′      = cong suc (idxˣ⁻ᵖ-<-irrelevant kk′~ x< x<′)
idxˣ⁻ᵖ-<-irrelevant             (!∷ᶜ kk′~) x<        x<′      = cong suc (idxˣ⁻ᵖ-<-irrelevant kk′~ x< x<′)
idxˣ⁻ᵖ-<-irrelevant             (?∷ᵖ kk′~) x<        x<′      = cong suc (idxˣ⁻ᵖ-<-irrelevant kk′~ x< x<′)
idxˣ⁻ᵖ-<-irrelevant {x = zero}  (!∷ᵖ kk′~) (s≤s x<) (s≤s x<′) = refl
idxˣ⁻ᵖ-<-irrelevant {x = suc u} (!∷ᵖ kk′~) (s≤s x<) (s≤s x<′) = cong suc (idxˣ⁻ᵖ-<-irrelevant kk′~ x< x<′)

≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ : (kk′~ : k ⍮ k′ ~ˣ⁻) (k″k‴~ : k″ ⍮ k‴ ~ˣ⁻) →
                                x ℕ.≥ k′ →
                                (x<′ : x ℕ.< k′ + k‴) (x<″ : x ∸ k′ ℕ.< k‴) →
                                lengthˣ⁻ kk′~ + idxˣ⁻ᵖ k″k‴~ x<″ ≡ idxˣ⁻ᵖ (kk′~ ++ˣ⁻ k″k‴~) x<′
≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻             []         k″k‴~ x≥       x<′       x<″ = idxˣ⁻ᵖ-<-irrelevant k″k‴~ x<″ x<′
≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻             (?∷ᶜ kk′~) k″k‴~ x≥       x<′       x<″ = cong suc (≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x≥ x<′ x<″)
≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻             (!∷ᶜ kk′~) k″k‴~ x≥       x<′       x<″ = cong suc (≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x≥ x<′ x<″)
≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻             (?∷ᵖ kk′~) k″k‴~ x≥       x<′       x<″ = cong suc (≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x≥ x<′ x<″)
≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ {x = suc u} (!∷ᵖ kk′~) k″k‴~ (s≤s x≥) (s≤s x<′) x<″ = cong suc (≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x≥ x<′ x<″)

~ᴹ⇒++ˣ⁻~ᴹ : (kk′~ : k ⍮ k′ ~ˣ⁻) (k″k‴~ : k″ ⍮ k‴ ~ˣ⁻) →
            kk′~ ⊢ DP.L ~ᴹ L →
            kk′~ ++ˣ⁻ k″k‴~ ⊢ DP.L ~ᴹ L
~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ `unit = `unit
~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ (`box ~L)
  with ~L′ ← ~ᴹ⇒++ˣ⁻~ᴹ (extractˣ⁻ᶜ kk′~) (extractˣ⁻ᶜ k″k‴~) ~L
    rewrite sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~}) = `box ~L′
~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ (`let-box ~L `in ~M) = `let-box (~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ ~L) `in (~ᴹ⇒++ˣ⁻~ᴹ (!∷ᶜ kk′~) k″k‴~ ~M)
~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ (`#¹ u<)
  rewrite <⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~ u< (ℕ.≤-trans u< (ℕ.m≤m+n _ _)) = `#¹ (ℕ.≤-trans u< (ℕ.m≤m+n _ _))
~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ (`λ⦂ S~ ∙ ~L) = `λ⦂ S~ ∙ ~ᴹ⇒++ˣ⁻~ᴹ (!∷ᵖ kk′~) k″k‴~ ~L
~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ (~L `$ ~M) = ~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ ~L `$ ~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ ~M
~ᴹ⇒++ˣ⁻~ᴹ kk′~ k″k‴~ (`#⁰ x<)
  rewrite <⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x< (ℕ.≤-trans x< (ℕ.m≤m+n _ _)) = `#⁰ (ℕ.≤-trans x< (ℕ.m≤m+n _ _))
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
  rewrite sym (<⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ (extractˣ⁻ᶜ k″k‴~) (subst (x ℕ.<_) (ℕ.+-identityʳ k′) x<) x<)
        | <⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ (subst (x ℕ.<_) (ℕ.+-identityʳ k′) x<) (ℕ.≤-trans (subst (x ℕ.<_) (ℕ.+-identityʳ k′) x<) (ℕ.m≤m+n _ _)) = `#⁰ (ℕ.≤-trans (subst (x ℕ.<_) (ℕ.+-identityʳ k′) x<) (ℕ.m≤m+n _ _))
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
  rewrite sym (<⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ (extractˣ⁻ᶜ k″k‴~) (subst (x ℕ.<_) (ℕ.+-identityʳ k′) x<) x<)
        | <⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ (subst (x ℕ.<_) (ℕ.+-identityʳ k′) x<) (ℕ.≤-trans (subst (x ℕ.<_) (ℕ.+-identityʳ k′) x<) (ℕ.m≤m+n _ _)) = refl
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


⟶[≤]-preserves-~ᴹ : kk′~ ⊢ DP.L ~ᴹ L →
                    L ⟶[ cMode ≤] L′ →
                    kk′~ ⊢ DP.L ~ᴹ L′
⟶[≤]-preserves-~ᴹ (`box ~L)            (ξ-`return[≰ ≰cMode ⇒-] L⟶[≤]) with () ← ≰cMode refl
⟶[≤]-preserves-~ᴹ (`box ~L)            (ξ-`return≤ (ξ-`lift L⟶[≤]))   = `box (⟶[≤]-preserves-~ᴹ ~L L⟶[≤])
⟶[≤]-preserves-~ᴹ (`let-box ~L `in ~M) ξ-`let-return L⟶[≤] `in?       = `let-box (⟶[≤]-preserves-~ᴹ ~L L⟶[≤]) `in ~M
⟶[≤]-preserves-~ᴹ (`let-box ~L `in ~M) (ξ-`let-return! WL `in M⟶[≤])  = `let-box ~L `in ⟶[≤]-preserves-~ᴹ ~M M⟶[≤]
⟶[≤]-preserves-~ᴹ (`λ⦂ ~S ∙ ~L)        (ξ-`λ⦂[-]-∘ L⟶[≤])             = `λ⦂ ~S ∙ ⟶[≤]-preserves-~ᴹ ~L L⟶[≤]
⟶[≤]-preserves-~ᴹ (~L `$ ~M)           ξ- L⟶[≤] `$?                   = ⟶[≤]-preserves-~ᴹ ~L L⟶[≤] `$ ~M
⟶[≤]-preserves-~ᴹ (~L `$ ~M)           (ξ-! WL `$ M⟶[≤])              = ~L `$ ⟶[≤]-preserves-~ᴹ ~M M⟶[≤]
⟶[≤]-preserves-~ᴹ (`#¹ u<)             (ξ-`unlift[≰ ≰cMode ⇒-] L⟶[≤]) with () ← ≰cMode refl
⟶[≤]-preserves-~ᴹ (`#¹ u<)             (ξ-`unlift≤ ())
⟶[≤]-preserves-~ᴹ (`unlift-`lift ~L)   (ξ-`unlift[≰ ≰cMode ⇒-] L⟶[≤]) with () ← ≰cMode refl
⟶[≤]-preserves-~ᴹ (`unlift-`lift ~L)   (ξ-`unlift≤ (ξ-`lift L⟶[≤]))   = `unlift-`lift (⟶[≤]-preserves-~ᴹ ~L L⟶[≤])
⟶[≤]-preserves-~ᴹ (`unlift-`lift ~L)   (β-`↑ _ WL)                    = extractˣ⁻ᶜ⁻¹-~ᴹ [] _ ~L


[]⊢~ᴹ⁻¹⇒¬Neut⁰ : [] ⊢ DP.L ~ᴹ L →
                 ¬ (WeakNeut L)
[]⊢~ᴹ⁻¹⇒¬Neut⁰ (`unlift-`lift ~L)   (`unlift ())
[]⊢~ᴹ⁻¹⇒¬Neut⁰ (`let-box ~L `in ~M) (`let-return NL `in _) = []⊢~ᴹ⁻¹⇒¬Neut⁰ ~L NL
[]⊢~ᴹ⁻¹⇒¬Neut⁰ (~L `$ ~M)           (NL `$ VM)             = []⊢~ᴹ⁻¹⇒¬Neut⁰ ~L NL

[]⊢~ᴹ⁻¹-respects-Value : [] ⊢ DP.L ~ᴹ L →
                         WeakNorm L →
                         DP.Value DP.L
[]⊢~ᴹ⁻¹-respects-Value `unit         `unit = DP.`unit
[]⊢~ᴹ⁻¹-respects-Value (`box ~L)     (`return (`lift WL)) = DP.`box _
[]⊢~ᴹ⁻¹-respects-Value (`λ⦂ ~S ∙ ~L) (`λ⦂ᵖ S ∘ L) = DP.`λ⦂ _ ∙ _
[]⊢~ᴹ⁻¹-respects-Value ~L            (`neut NL) with () ← []⊢~ᴹ⁻¹⇒¬Neut⁰ ~L NL


~ᴹ-normalize[≤] : (~L : kk′~ ⊢ DP.L ~ᴹ L) →
                  ∃ (λ L′ → L ⟶[ cMode ≤]* L′ × DeferredTerm[ cMode ≤] L′ × Σ (kk′~ ⊢ DP.L ~ᴹ L′) λ ~L′ → depth~ᴹ ~L′ ℕ.≤ depth~ᴹ ~L)
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
                                                          , extractˣ⁻ᶜ⁻¹-~ᴹ [] _ ~L′
                                                          , ℕ.m≤n⇒m≤1+n (subst (ℕ._≤ _) (sym (extractˣ⁻ᶜ⁻¹-~ᴹ-depth~ᴹ [] _ ~L′)) L′≤)


Value~ᴹ-normalize-helper : (~L : kk′~ ⊢ DP.L ~ᴹ L) →
                           DP.Value DP.L →
                           Acc ℕ._<_ (depth~ᴹ ~L) →
                           ∃ (λ L′ → L ⟶* L′ × WeakNorm L′ × kk′~ ⊢ DP.L ~ᴹ L′)
Value~ᴹ-normalize-helper `unit              VDPL (acc r) = -, ε , `unit , `unit
Value~ᴹ-normalize-helper (`box ~L)          VDPL (acc r)
  with _ , ⟶*L′[≤] , WL′ , ~L′ , _ ← ~ᴹ-normalize[≤] ~L = -, ξ-of-⟶* `return ξ-`return (ξ-of-↝*-⟶* _⟶[ _ ≤]_ `lift ξ-`lift ⟶*L′[≤]) , `return (`lift WL′) , `box ~L′
Value~ᴹ-normalize-helper (`λ⦂ ~S ∙ ~L)      VDPL (acc r) = -, ε , `λ⦂ᵖ _ ∘ _ , `λ⦂ ~S ∙ ~L
Value~ᴹ-normalize-helper (`unlift-`lift ~L) VDPL (acc r)
  with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L
    with _ , ⟶*L″ , VL″ , ~L″ ← Value~ᴹ-normalize-helper ~L′ VDPL (r _ (s≤s L′≤)) = -, ξ-of-⟶* `unlift ξ-`unlift (ξ-of-↝*-⟶* _⟶[ cMode ≤]_ `lift ξ-`lift ⟶*L′[≤]) ◅◅ β-`↑ WL′ ◅ ⟶*L″ , VL″ , extractˣ⁻ᶜ⁻¹-~ᴹ [] _ ~L″

Value~ᴹ-normalize : kk′~ ⊢ DP.L ~ᴹ L →
                    DP.Value DP.L →
                    ∃ (λ L′ → L ⟶* L′ × WeakNorm L′ × kk′~ ⊢ DP.L ~ᴹ L′)
Value~ᴹ-normalize ~L VDPL = Value~ᴹ-normalize-helper ~L VDPL (ℕ.<-wellFounded _)


`box-~ᴹ-inv-helper : (~L : kk′~ ⊢ DP.`box DP.L ~ᴹ L) →
                     Acc ℕ._<_ (depth~ᴹ ~L) →
                     ∃ (λ L′ → L ⟶* `return (`lift L′) × DeferredTerm[ cMode ≤] L′ × kk′~ ⊢ DP.L ~ᴹ L′)
`box-~ᴹ-inv-helper (`box ~L) (acc r)
  with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L = -, ξ-of-⟶* `return ξ-`return (ξ-of-↝*-⟶* _⟶[ _ ≤]_ `lift ξ-`lift ⟶*L′[≤]) , WL′ , extractˣ⁻ᶜ⁻¹-~ᴹ [] _ ~L′
`box-~ᴹ-inv-helper (`unlift-`lift ~L) (acc r)
  with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L
    with _ , ⟶*`boxL″ , WL″ , ~L″ ← `box-~ᴹ-inv-helper ~L′ (r _ (s≤s L′≤)) = -, ξ-of-⟶* `unlift ξ-`unlift (ξ-of-↝*-⟶* _⟶[ cMode ≤]_ `lift ξ-`lift ⟶*L′[≤]) ◅◅ β-`↑ WL′ ◅ ⟶*`boxL″ , WL″ , extractˣ⁻ᶜ⁻¹-~ᴹ [] _ ~L″

`box-~ᴹ-inv : kk′~ ⊢ DP.`box DP.M ~ᴹ M →
              ∃ (λ M′ → M ⟶* `return (`lift M′) × DeferredTerm[ cMode ≤] M′ × kk′~ ⊢ DP.M ~ᴹ M′)
`box-~ᴹ-inv ~L = `box-~ᴹ-inv-helper ~L (ℕ.<-wellFounded _)


`λ⦂-∙-~ᴹ-inv-helper : (~L : kk′~ ⊢ DP.`λ⦂ DP.S ∙ DP.L ~ᴹ L) →
                      Acc ℕ._<_ (depth~ᴹ ~L) →
                      ∃₂ (λ S′ L′ → L ⟶* `λ⦂ᵖ S′ ∘ L′ × !∷ᵖ kk′~ ⊢ DP.L ~ᴹ L′ × DP.S ~ᵀ S′)
`λ⦂-∙-~ᴹ-inv-helper (`λ⦂ ~S ∙ ~L) (acc r) = -, -, ε , ~L , ~S
`λ⦂-∙-~ᴹ-inv-helper (`unlift-`lift ~L) (acc r)
  with _ , ⟶*L′[≤] , WL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L
    with _ , _ , ⟶*`λ⦂ᵖS″∘L″ , ~L″ , ~S″ ← `λ⦂-∙-~ᴹ-inv-helper ~L′ (r _ (s≤s L′≤)) = -, -, ξ-of-⟶* `unlift ξ-`unlift (ξ-of-↝*-⟶* _⟶[ cMode ≤]_ `lift ξ-`lift ⟶*L′[≤]) ◅◅ β-`↑ WL′ ◅ ⟶*`λ⦂ᵖS″∘L″ , extractˣ⁻ᶜ⁻¹-~ᴹ (!∷ᵖ []) _ ~L″ , ~S″

`λ⦂-∙-~ᴹ-inv : kk′~ ⊢ DP.`λ⦂ DP.S ∙ DP.L ~ᴹ L →
               ∃₂ (λ S′ L′ → L ⟶* `λ⦂ᵖ S′ ∘ L′ × !∷ᵖ kk′~ ⊢ DP.L ~ᴹ L′ × DP.S ~ᵀ S′)
`λ⦂-∙-~ᴹ-inv ~L = `λ⦂-∙-~ᴹ-inv-helper ~L (ℕ.<-wellFounded _)

wkidx[↑]-idxˣ⁻ᶜ : ∀ {u} →
                  (kk′~ : k ⍮ k′ ~ˣ⁻) (0k₀~ : 0 ⍮ k₀ ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
                  (u< : u ℕ.< k + k″) →
                  wkidx[ lengthˣ⁻ 0k₀~ ↑ lengthˣ⁻ kk′~ ] (idxˣ⁻ᶜ (kk′~ ++ˣ⁻ k″k‴~) u<) ≡ idxˣ⁻ᶜ (kk′~ ++ˣ⁻ 0k₀~ ++ˣ⁻ k″k‴~) u<
wkidx[↑]-idxˣ⁻ᶜ             []         0k₀~ {k″k‴~} u<                                             = ≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ 0k₀~ k″k‴~ z≤n u< u<
wkidx[↑]-idxˣ⁻ᶜ             (?∷ᵖ kk′~) 0k₀~ {k″k‴~} u<
  rewrite wkidx[↑suc]suc≡sucwkidx[↑] (lengthˣ⁻ 0k₀~) (lengthˣ⁻ kk′~) (idxˣ⁻ᶜ (kk′~ ++ˣ⁻ k″k‴~) u<) = cong suc (wkidx[↑]-idxˣ⁻ᶜ kk′~ 0k₀~ u<)
wkidx[↑]-idxˣ⁻ᶜ             (!∷ᵖ kk′~) 0k₀~ {k″k‴~} u<
  rewrite wkidx[↑suc]suc≡sucwkidx[↑] (lengthˣ⁻ 0k₀~) (lengthˣ⁻ kk′~) (idxˣ⁻ᶜ (kk′~ ++ˣ⁻ k″k‴~) u<) = cong suc (wkidx[↑]-idxˣ⁻ᶜ kk′~ 0k₀~ u<)
wkidx[↑]-idxˣ⁻ᶜ             (?∷ᶜ kk′~) 0k₀~ {k″k‴~} u<
  rewrite wkidx[↑suc]suc≡sucwkidx[↑] (lengthˣ⁻ 0k₀~) (lengthˣ⁻ kk′~) (idxˣ⁻ᶜ (kk′~ ++ˣ⁻ k″k‴~) u<) = cong suc (wkidx[↑]-idxˣ⁻ᶜ kk′~ 0k₀~ u<)
wkidx[↑]-idxˣ⁻ᶜ {u = zero}  (!∷ᶜ kk′~) 0k₀~         (s≤s u<)                                       = refl
wkidx[↑]-idxˣ⁻ᶜ {u = suc u} (!∷ᶜ kk′~) 0k₀~ {k″k‴~} (s≤s u<)
  rewrite wkidx[↑suc]suc≡sucwkidx[↑] (lengthˣ⁻ 0k₀~) (lengthˣ⁻ kk′~) (idxˣ⁻ᶜ (kk′~ ++ˣ⁻ k″k‴~) u<) = cong suc (wkidx[↑]-idxˣ⁻ᶜ kk′~ 0k₀~ u<)

wkidx[↑]-idxˣ⁻ᵖ : (kk′~ : k ⍮ k′ ~ˣ⁻) (k₀0~ : k₀ ⍮ 0 ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
                  (x< : x ℕ.< k′ + k‴) →
                  wkidx[ lengthˣ⁻ k₀0~ ↑ lengthˣ⁻ kk′~ ] (idxˣ⁻ᵖ (kk′~ ++ˣ⁻ k″k‴~) x<) ≡ idxˣ⁻ᵖ (kk′~ ++ˣ⁻ k₀0~ ++ˣ⁻ k″k‴~) x<
wkidx[↑]-idxˣ⁻ᵖ             []         k₀0~ {k″k‴~} x<                                             = ≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ k₀0~ k″k‴~ z≤n x< x<
wkidx[↑]-idxˣ⁻ᵖ             (?∷ᶜ kk′~) k₀0~ {k″k‴~} x<
  rewrite wkidx[↑suc]suc≡sucwkidx[↑] (lengthˣ⁻ k₀0~) (lengthˣ⁻ kk′~) (idxˣ⁻ᵖ (kk′~ ++ˣ⁻ k″k‴~) x<) = cong suc (wkidx[↑]-idxˣ⁻ᵖ kk′~ k₀0~ x<)
wkidx[↑]-idxˣ⁻ᵖ             (!∷ᶜ kk′~) k₀0~ {k″k‴~} x<
  rewrite wkidx[↑suc]suc≡sucwkidx[↑] (lengthˣ⁻ k₀0~) (lengthˣ⁻ kk′~) (idxˣ⁻ᵖ (kk′~ ++ˣ⁻ k″k‴~) x<) = cong suc (wkidx[↑]-idxˣ⁻ᵖ kk′~ k₀0~ x<)
wkidx[↑]-idxˣ⁻ᵖ             (?∷ᵖ kk′~) k₀0~ {k″k‴~} x<
  rewrite wkidx[↑suc]suc≡sucwkidx[↑] (lengthˣ⁻ k₀0~) (lengthˣ⁻ kk′~) (idxˣ⁻ᵖ (kk′~ ++ˣ⁻ k″k‴~) x<) = cong suc (wkidx[↑]-idxˣ⁻ᵖ kk′~ k₀0~ x<)
wkidx[↑]-idxˣ⁻ᵖ {x = zero}  (!∷ᵖ kk′~) k₀0~         (s≤s x<)                                       = refl
wkidx[↑]-idxˣ⁻ᵖ {x = suc x} (!∷ᵖ kk′~) k₀0~ {k″k‴~} (s≤s x<)
  rewrite wkidx[↑suc]suc≡sucwkidx[↑] (lengthˣ⁻ k₀0~) (lengthˣ⁻ kk′~) (idxˣ⁻ᵖ (kk′~ ++ˣ⁻ k″k‴~) x<) = cong suc (wkidx[↑]-idxˣ⁻ᵖ kk′~ k₀0~ x<)

wk[↑¹]~ᴹwk[↑]ᶜ : (kk′~ : k ⍮ k′ ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
                 kk′~ ++ˣ⁻ k″k‴~ ⊢ DP.L ~ᴹ L →
                 kk′~ ++ˣ⁻ !∷ᶜ k″k‴~ ⊢ DP.wk[ 1 ↑¹ k ] DP.L ~ᴹ wk[ 1 ↑ lengthˣ⁻ kk′~ ] L
wk[↑¹]~ᴹwk[↑]ᶜ kk′~ `unit = `unit
wk[↑¹]~ᴹwk[↑]ᶜ kk′~ {k″k‴~} (`box ~L)
  rewrite extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~ = k″k‴~}
    with ~L′ ← wk[↑¹]~ᴹwk[↑]ᶜ (extractˣ⁻ᶜ kk′~) {k″k‴~ = extractˣ⁻ᶜ k″k‴~} ~L
      rewrite sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~ = !∷ᶜ k″k‴~})
            | extractˣ⁻ᶜ-lengthˣ⁻ kk′~ = `box ~L′
wk[↑¹]~ᴹwk[↑]ᶜ kk′~ (`let-box ~L `in ~M) = `let-box wk[↑¹]~ᴹwk[↑]ᶜ kk′~ ~L `in wk[↑¹]~ᴹwk[↑]ᶜ (!∷ᶜ kk′~) ~M
wk[↑¹]~ᴹwk[↑]ᶜ {k} kk′~ {k″k‴~} (`#¹_ {u = u} u<)
  with u ℕ.≥? k
...  | no  u≱k
    with u<k ← ℕ.≰⇒> u≱k
      rewrite sym (<⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~ u<k u<)
            | dec-no (_ ℕ.≤? _) (ℕ.<⇒≱ (idxˣ⁻ᶜ<lengthˣ⁻ kk′~ u<k))
            | <⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ (!∷ᶜ k″k‴~) u<k (ℕ.<-transˡ u<k (ℕ.m≤m+n _ _)) = `#¹ ℕ.<-transˡ u<k (ℕ.m≤m+n _ _)
...  | yes u≥k
    with u∸k< ← subst (u ∸ k ℕ.<_) (ℕ.m+n∸m≡n k _) (ℕ.∸-monoˡ-< u< u≥k)
      rewrite sym (≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~ u≥k u< u∸k<)
            | proj₂ (dec-yes (_ ℕ.≤? _) (ℕ.m≤m+n (lengthˣ⁻ kk′~) (idxˣ⁻ᶜ k″k‴~ u∸k<)))
            | dec-no (_ ℕ.≟ _) (ℕ.m+1+n≢m (lengthˣ⁻ kk′~) {idxˣ⁻ᶜ k″k‴~ u∸k<})
            | sym (ℕ.+-suc (lengthˣ⁻ kk′~) (idxˣ⁻ᶜ k″k‴~ u∸k<)) = {!!}
wk[↑¹]~ᴹwk[↑]ᶜ {k} {k′} kk′~ (`λ⦂ ~S ∙ ~L)
  with ~L′ ← wk[↑¹]~ᴹwk[↑]ᶜ (!∷ᵖ kk′~) ~L
    rewrite ℕ.+-suc k k′ = `λ⦂ ~S ∙ ~L′
wk[↑¹]~ᴹwk[↑]ᶜ kk′~ (~L `$ ~M) = wk[↑¹]~ᴹwk[↑]ᶜ kk′~ ~L `$ wk[↑¹]~ᴹwk[↑]ᶜ kk′~ ~M
wk[↑¹]~ᴹwk[↑]ᶜ kk′~ {k″k‴~} (`#⁰ x<)
  rewrite wkidx[↑]-idxˣ⁻ᵖ kk′~ (!∷ᶜ []) {k″k‴~} x< = `#⁰ x<
wk[↑¹]~ᴹwk[↑]ᶜ kk′~ {k″k‴~} (`unlift-`lift ~L)
  rewrite extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~ = k″k‴~}
    with ~L′ ← wk[↑¹]~ᴹwk[↑]ᶜ (extractˣ⁻ᶜ kk′~) {k″k‴~ = extractˣ⁻ᶜ k″k‴~} ~L
      rewrite sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~ = !∷ᶜ k″k‴~})
            | extractˣ⁻ᶜ-lengthˣ⁻ kk′~ = `unlift-`lift ~L′

~ᴹ∧≥⇒wk[↑⁰]≡ : {kk′~ : k ⍮ k′ ~ˣ⁻} →
               kk′~ ⊢ DP.L ~ᴹ L →
               x ℕ.≥ k′ →
               DP.wk[ 1 ↑⁰ x ] DP.L ≡ DP.L
~ᴹ∧≥⇒wk[↑⁰]≡ `unit x≥ = refl
~ᴹ∧≥⇒wk[↑⁰]≡ (`box ~M) x≥ = refl
~ᴹ∧≥⇒wk[↑⁰]≡ (`let-box ~M `in ~N) x≥ = cong₂ DP.`let-box_`in_ (~ᴹ∧≥⇒wk[↑⁰]≡ ~M x≥) (~ᴹ∧≥⇒wk[↑⁰]≡ ~N x≥)
~ᴹ∧≥⇒wk[↑⁰]≡ (`#¹ u<) x≥ = refl
~ᴹ∧≥⇒wk[↑⁰]≡ (`λ⦂ ~S ∙ ~M) x≥ = cong (DP.`λ⦂ _ ∙_) (~ᴹ∧≥⇒wk[↑⁰]≡ ~M (s≤s x≥))
~ᴹ∧≥⇒wk[↑⁰]≡ (~M `$ ~N) x≥ = cong₂ DP._`$_ (~ᴹ∧≥⇒wk[↑⁰]≡ ~M x≥) (~ᴹ∧≥⇒wk[↑⁰]≡ ~N x≥)
~ᴹ∧≥⇒wk[↑⁰]≡ (`#⁰ y<) x≥
  rewrite dec-no (_ ℕ.≤? _) (ℕ.<⇒≱ (ℕ.<-transˡ y< x≥)) = refl
~ᴹ∧≥⇒wk[↑⁰]≡ (`unlift-`lift ~M) x≥ = ~ᴹ∧≥⇒wk[↑⁰]≡ ~M z≤n 

~ᴹwk[↑]ᵖ : (kk′~ : k ⍮ k′ ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
           kk′~ ++ˣ⁻ k″k‴~ ⊢ DP.L ~ᴹ L →
           kk′~ ++ˣ⁻ ?∷ᵖ k″k‴~ ⊢ DP.L ~ᴹ wk[ 1 ↑ lengthˣ⁻ kk′~ ] L
~ᴹwk[↑]ᵖ kk′~ `unit = `unit
~ᴹwk[↑]ᵖ kk′~ {k″k‴~} (`box ~L)
  rewrite extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~ = k″k‴~}
    with ~L′ ← ~ᴹwk[↑]ᵖ (extractˣ⁻ᶜ kk′~) {k″k‴~ = extractˣ⁻ᶜ k″k‴~} ~L
      rewrite sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~ = ?∷ᵖ k″k‴~})
            | extractˣ⁻ᶜ-lengthˣ⁻ kk′~ = `box ~L′
~ᴹwk[↑]ᵖ kk′~ (`let-box ~L `in ~M) = `let-box ~ᴹwk[↑]ᵖ kk′~ ~L `in ~ᴹwk[↑]ᵖ (!∷ᶜ kk′~) ~M
~ᴹwk[↑]ᵖ kk′~ {k″k‴~} (`#¹ u<)
  rewrite wkidx[↑]-idxˣ⁻ᶜ kk′~ (?∷ᵖ []) {k″k‴~} u< = `#¹ u<
~ᴹwk[↑]ᵖ {k = k} {k′ = k′} kk′~ (`λ⦂ ~S ∙ ~L)
  with ~L′ ← ~ᴹwk[↑]ᵖ (!∷ᵖ kk′~) ~L
    rewrite ℕ.+-suc k k′ = `λ⦂ ~S ∙ ~L′
~ᴹwk[↑]ᵖ kk′~ (~L `$ ~M) = ~ᴹwk[↑]ᵖ kk′~ ~L `$ ~ᴹwk[↑]ᵖ kk′~ ~M
~ᴹwk[↑]ᵖ kk′~ {k″k‴~} (`#⁰ x<)
  rewrite wkidx[↑]-idxˣ⁻ᵖ kk′~ (?∷ᵖ []) {k″k‴~} x< = `#⁰ x<
~ᴹwk[↑]ᵖ kk′~ {k″k‴~} (`unlift-`lift ~L)
  rewrite extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~ = k″k‴~}
    with ~L′ ← ~ᴹwk[↑]ᵖ (extractˣ⁻ᶜ kk′~) {k″k‴~ = extractˣ⁻ᶜ k″k‴~} ~L
      rewrite sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~ = ?∷ᵖ k″k‴~})
            | extractˣ⁻ᶜ-lengthˣ⁻ kk′~ = `unlift-`lift ~L′

wk[↑⁰]~ᴹwk[↑]ᵖ : (kk′~ : k ⍮ k′ ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
                 kk′~ ++ˣ⁻ k″k‴~ ⊢ DP.L ~ᴹ L →
                 kk′~ ++ˣ⁻ !∷ᵖ k″k‴~ ⊢ DP.wk[ 1 ↑⁰ k′ ] DP.L ~ᴹ wk[ 1 ↑ lengthˣ⁻ kk′~ ] L
wk[↑⁰]~ᴹwk[↑]ᵖ kk′~ `unit = `unit
wk[↑⁰]~ᴹwk[↑]ᵖ kk′~ {k″k‴~} (`box ~L)
  rewrite extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~ = k″k‴~}
    with ~L′ ← ~ᴹwk[↑]ᵖ (extractˣ⁻ᶜ kk′~) {k″k‴~ = extractˣ⁻ᶜ k″k‴~} ~L
      rewrite sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~ = !∷ᵖ k″k‴~})
            | extractˣ⁻ᶜ-lengthˣ⁻ kk′~ = `box ~L′
wk[↑⁰]~ᴹwk[↑]ᵖ kk′~ (`let-box ~L `in ~M) = `let-box wk[↑⁰]~ᴹwk[↑]ᵖ kk′~ ~L `in wk[↑⁰]~ᴹwk[↑]ᵖ (!∷ᶜ kk′~) ~M
wk[↑⁰]~ᴹwk[↑]ᵖ kk′~ {k″k‴~} (`#¹ u<)
  rewrite wkidx[↑]-idxˣ⁻ᶜ kk′~ (!∷ᵖ []) {k″k‴~} u< = `#¹ u<
wk[↑⁰]~ᴹwk[↑]ᵖ {k = k} {k′ = k′} kk′~ (`λ⦂ ~S ∙ ~L)
  with ~L′ ← wk[↑⁰]~ᴹwk[↑]ᵖ (!∷ᵖ kk′~) ~L
    rewrite ℕ.+-suc k k′ = `λ⦂ ~S ∙ ~L′
wk[↑⁰]~ᴹwk[↑]ᵖ kk′~ (~L `$ ~M) = wk[↑⁰]~ᴹwk[↑]ᵖ kk′~ ~L `$ wk[↑⁰]~ᴹwk[↑]ᵖ kk′~ ~M
wk[↑⁰]~ᴹwk[↑]ᵖ kk′~ {k″k‴~} (`#⁰ x<) = {!!}
wk[↑⁰]~ᴹwk[↑]ᵖ {k′ = k′} kk′~ {k″k‴~} (`unlift-`lift ~L)
  rewrite extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~ = k″k‴~}
    with ~L′ ← ~ᴹwk[↑]ᵖ (extractˣ⁻ᶜ kk′~) {k″k‴~ = extractˣ⁻ᶜ k″k‴~} ~L
      rewrite sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~ = !∷ᵖ k″k‴~})
            | extractˣ⁻ᶜ-lengthˣ⁻ kk′~
            | ~ᴹ∧≥⇒wk[↑⁰]≡ ~L (z≤n {k′}) = `unlift-`lift ~L′

[/¹]~ᴹ[/]ᶜ : (kk′~ : k ⍮ k′ ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
             extractˣ⁻ᶜ (kk′~ ++ˣ⁻ k″k‴~) ⊢ DP.L ~ᴹ L →
             kk′~ ++ˣ⁻ !∷ᶜ k″k‴~ ⊢ DP.M ~ᴹ M →
             kk′~ ++ˣ⁻ k″k‴~ ⊢ DP.[ DP.L /¹ k ] DP.M ~ᴹ [ `lift L /[ cMode ] lengthˣ⁻ kk′~ ] M
[/¹]~ᴹ[/]ᶜ kk′~ ~L `unit = `unit
[/¹]~ᴹ[/]ᶜ kk′~ {k″k‴~} ~L (`box ~M)
  rewrite sym (extractˣ⁻ᶜ-idempotent (kk′~ ++ˣ⁻ k″k‴~))
        | extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~ = k″k‴~}
        | extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~ = !∷ᶜ k″k‴~}
    with ~M′ ← [/¹]~ᴹ[/]ᶜ (extractˣ⁻ᶜ kk′~) ~L ~M
      rewrite sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~ = k″k‴~})
            | extractˣ⁻ᶜ-lengthˣ⁻ kk′~ = `box ~M′
[/¹]~ᴹ[/]ᶜ kk′~ ~L (`let-box ~M `in ~N) = `let-box [/¹]~ᴹ[/]ᶜ kk′~ ~L ~M `in [/¹]~ᴹ[/]ᶜ (!∷ᶜ kk′~) (wk[↑¹]~ᴹwk[↑]ᶜ [] ~L) ~N
[/¹]~ᴹ[/]ᶜ {k} {_} {k″} kk′~ {k″k‴~} ~L (`#¹_ {u = u} u<)
  with u ℕ.≥? k
...  | no  u≱k
    with u<k ← ℕ.≰⇒> u≱k
      rewrite sym (<⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ (!∷ᶜ k″k‴~) u<k u<)
            | dec-no (_ ℕ.≤? _) (ℕ.<⇒≱ (idxˣ⁻ᶜ<lengthˣ⁻ kk′~ u<k))
            | <⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~ u<k (ℕ.<-transˡ u<k (ℕ.m≤m+n _ _)) = `#¹ (ℕ.<-transˡ u<k (ℕ.m≤m+n _ _))
...  | yes u≥k
    with u∸k< ← subst (u ∸ k ℕ.<_) (ℕ.m+n∸m≡n k _) (ℕ.∸-monoˡ-< u< u≥k)
      rewrite sym (≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ (!∷ᶜ k″k‴~) u≥k u< u∸k<)
            | proj₂ (dec-yes (_ ℕ.≤? _) (ℕ.m≤m+n (lengthˣ⁻ kk′~) (idxˣ⁻ᶜ (!∷ᶜ k″k‴~) u∸k<)))
        with u ℕ.≟ k
...        | no  u≢k
          with u>k ← ℕ.≤∧≢⇒< u≥k (≢-sym u≢k)
             | s≤s u∸k≤ ← u∸k<
            with suc u′ ← u
              rewrite ℕ.+-∸-assoc 1 (ℕ.≤-pred u>k)
                    | dec-no (_ ℕ.≟ _) (ℕ.m+1+n≢m (lengthˣ⁻ kk′~) {idxˣ⁻ᶜ k″k‴~ u∸k≤})
                    | ℕ.+-suc (lengthˣ⁻ kk′~) (idxˣ⁻ᶜ k″k‴~ u∸k≤)
                    | ℕ.+-suc k k″
                    | ≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~ (ℕ.≤-pred u>k) (ℕ.≤-pred u<) u∸k≤ = `#¹ (ℕ.≤-pred u<)
...        | yes u≡k
          with s≤s _ ← u∸k<
            rewrite u≡k
                  | ℕ.n∸n≡0 k
                  | proj₂ (dec-yes (_ ℕ.≟ _) (ℕ.+-identityʳ (lengthˣ⁻ kk′~))) = `unlift-`lift ~L
[/¹]~ᴹ[/]ᶜ {k} {k′} kk′~ ~L (`λ⦂ ~S ∙ ~M)
  with ~M′ ← [/¹]~ᴹ[/]ᶜ (!∷ᵖ kk′~) (~ᴹwk[↑]ᵖ [] ~L) ~M
    rewrite ℕ.+-suc k k′ = `λ⦂ ~S ∙ ~M′
[/¹]~ᴹ[/]ᶜ kk′~ ~L (~M `$ ~N) = [/¹]~ᴹ[/]ᶜ kk′~ ~L ~M `$ [/¹]~ᴹ[/]ᶜ kk′~ ~L ~N
[/¹]~ᴹ[/]ᶜ {_} {k′} {_} {k‴} kk′~ {k″k‴~} ~L (`#⁰_ {x = x} x<)
  with x ℕ.≥? k′
...  | no  x≱k′
    with x<k′ ← ℕ.≰⇒> x≱k′
      rewrite sym (<⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ (!∷ᶜ k″k‴~) x<k′ x<)
            | dec-no (_ ℕ.≥? _) (ℕ.<⇒≱ (idxˣ⁻ᵖ<lengthˣ⁻ kk′~ x<k′))
            | <⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x<k′ x< = `#⁰ x<
...  | yes x≥k′
    with x∸k′< ← subst (x ∸ k′ ℕ.<_) (ℕ.m+n∸m≡n k′ _) (ℕ.∸-monoˡ-< x< x≥k′)
      rewrite sym (≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ (!∷ᶜ k″k‴~) x≥k′ x< x∸k′<)
            | proj₂ (dec-yes (_ ℕ.≤? _) (ℕ.m≤m+n (lengthˣ⁻ kk′~) (idxˣ⁻ᵖ (!∷ᶜ k″k‴~) x∸k′<)))
            | dec-no (_ ℕ.≟ _) (ℕ.m+1+n≢m (lengthˣ⁻ kk′~) {idxˣ⁻ᵖ k″k‴~ x∸k′<})
            | ℕ.+-suc (lengthˣ⁻ kk′~) (idxˣ⁻ᵖ k″k‴~ x∸k′<)
            | ≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x≥k′ x< x∸k′< = `#⁰ x<
[/¹]~ᴹ[/]ᶜ kk′~ {k″k‴~} ~L (`unlift-`lift ~M)
  rewrite sym (extractˣ⁻ᶜ-idempotent (kk′~ ++ˣ⁻ k″k‴~))
        | extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~ = k″k‴~}
        | extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~ = !∷ᶜ k″k‴~}
    with ~M′ ← [/¹]~ᴹ[/]ᶜ (extractˣ⁻ᶜ kk′~) ~L ~M
      rewrite sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~ = k″k‴~})
            | extractˣ⁻ᶜ-lengthˣ⁻ kk′~ = `unlift-`lift ~M′

~ᴹ∧≥⇒[/⁰]≡ : ∀ DPL →
             {kk′~ : k ⍮ k′ ~ˣ⁻} →
             kk′~ ⊢ DP.M ~ᴹ M →
             x ℕ.≥ k′ →
             DP.[ DPL /⁰ x ] DP.M ≡ DP.M
~ᴹ∧≥⇒[/⁰]≡ _ `unit x≥ = refl
~ᴹ∧≥⇒[/⁰]≡ _ (`box ~M) x≥ = refl
~ᴹ∧≥⇒[/⁰]≡ _ (`let-box ~M `in ~N) x≥ = cong₂ DP.`let-box_`in_ (~ᴹ∧≥⇒[/⁰]≡ _ ~M x≥) (~ᴹ∧≥⇒[/⁰]≡ _ ~N x≥)
~ᴹ∧≥⇒[/⁰]≡ _ (`#¹ u<) x≥ = refl
~ᴹ∧≥⇒[/⁰]≡ _ (`λ⦂ ~S ∙ ~M) x≥ = cong (DP.`λ⦂ _ ∙_) (~ᴹ∧≥⇒[/⁰]≡ _ ~M (s≤s x≥))
~ᴹ∧≥⇒[/⁰]≡ _ (~M `$ ~N) x≥ = cong₂ DP._`$_ (~ᴹ∧≥⇒[/⁰]≡ _ ~M x≥) (~ᴹ∧≥⇒[/⁰]≡ _ ~N x≥)
~ᴹ∧≥⇒[/⁰]≡ _ (`#⁰ y<) x≥
  rewrite dec-no (_ ℕ.≤? _) (ℕ.<⇒≱ (ℕ.<-transˡ y< x≥)) = refl
~ᴹ∧≥⇒[/⁰]≡ _ (`unlift-`lift ~M) x≥ = ~ᴹ∧≥⇒[/⁰]≡ _ ~M z≤n 

~ᴹ[/]ᵖ : (kk′~ : k ⍮ k′ ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
         ∀ L →
         kk′~ ++ˣ⁻ ?∷ᵖ k″k‴~ ⊢ DP.M ~ᴹ M →
         kk′~ ++ˣ⁻ k″k‴~ ⊢ DP.M ~ᴹ [ L /[ pMode ] lengthˣ⁻ kk′~ ] M
~ᴹ[/]ᵖ kk′~         _ `unit = `unit
~ᴹ[/]ᵖ kk′~ {k″k‴~} _ (`box ~M)
  rewrite extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~ = ?∷ᵖ k″k‴~}
    with ~M′ ← ~ᴹ[/]ᵖ (extractˣ⁻ᶜ kk′~) (`unlift `unit) ~M
      rewrite sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~ = k″k‴~})
            | extractˣ⁻ᶜ-lengthˣ⁻ kk′~ = `box ~M′
~ᴹ[/]ᵖ kk′~         _ (`let-box ~M `in ~N) = `let-box ~ᴹ[/]ᵖ kk′~ _ ~M `in ~ᴹ[/]ᵖ (!∷ᶜ kk′~) _ ~N
~ᴹ[/]ᵖ {k} kk′~ {k″k‴~} _ (`#¹_ {u = u} u<)
  with u ℕ.≥? k
...  | no  u≱k
    rewrite sym (<⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ (?∷ᵖ k″k‴~) (ℕ.≰⇒> u≱k) u<)
          | dec-no (_ ℕ.≥? _) (ℕ.<⇒≱ (idxˣ⁻ᶜ<lengthˣ⁻ kk′~ (ℕ.≰⇒> u≱k)))
          | <⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~ (ℕ.≰⇒> u≱k) u< = `#¹ u<
...  | yes u≥k
    with u∸k< ← subst (u ∸ k ℕ.<_) (ℕ.m+n∸m≡n k _) (ℕ.∸-monoˡ-< u< u≥k)
      rewrite sym (≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ (?∷ᵖ k″k‴~) u≥k u< u∸k<)
            | proj₂ (dec-yes (_ ℕ.≤? _) (ℕ.m≤m+n (lengthˣ⁻ kk′~) (idxˣ⁻ᶜ (?∷ᵖ k″k‴~) u∸k<)))
            | dec-no (_ ℕ.≟ _) (ℕ.m+1+n≢m (lengthˣ⁻ kk′~) {idxˣ⁻ᶜ k″k‴~ u∸k<})
            | ℕ.+-suc (lengthˣ⁻ kk′~) (idxˣ⁻ᶜ k″k‴~ u∸k<)
            | ≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ k″k‴~ u≥k u< u∸k< = `#¹ u<
~ᴹ[/]ᵖ kk′~         _ (`λ⦂ ~S ∙ ~M) = `λ⦂ ~S ∙ (~ᴹ[/]ᵖ (!∷ᵖ kk′~) _ ~M)
~ᴹ[/]ᵖ kk′~         _ (~M `$ ~N) = ~ᴹ[/]ᵖ kk′~ _ ~M `$ ~ᴹ[/]ᵖ kk′~ _ ~N
~ᴹ[/]ᵖ {_} {k′} kk′~ {k″k‴~} _ (`#⁰_ {x = x} x<)
  with x ℕ.≥? k′
...  | no  x≱k′
    with x<k′ ← ℕ.≰⇒> x≱k′
      rewrite sym (<⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ (?∷ᵖ k″k‴~) x<k′ x<)
            | dec-no (_ ℕ.≥? _) (ℕ.<⇒≱ (idxˣ⁻ᵖ<lengthˣ⁻ kk′~ x<k′))
            | <⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x<k′ x< = `#⁰ x<
...  | yes x≥k′
    with x∸k′< ← subst (x ∸ k′ ℕ.<_) (ℕ.m+n∸m≡n k′ _) (ℕ.∸-monoˡ-< x< x≥k′)
      rewrite sym (≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ (?∷ᵖ k″k‴~) x≥k′ x< x∸k′<)
            | proj₂ (dec-yes (_ ℕ.≤? _) (ℕ.m≤m+n (lengthˣ⁻ kk′~) (idxˣ⁻ᵖ (?∷ᵖ k″k‴~) x∸k′<)))
            | dec-no (_ ℕ.≟ _) (ℕ.m+1+n≢m (lengthˣ⁻ kk′~) {idxˣ⁻ᵖ k″k‴~ x∸k′<})
            | ℕ.+-suc (lengthˣ⁻ kk′~) (idxˣ⁻ᵖ k″k‴~ x∸k′<)
            | ≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x≥k′ x< x∸k′< = `#⁰ x<
~ᴹ[/]ᵖ kk′~ {k″k‴~} _ (`unlift-`lift ~M)
  rewrite extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~ = ?∷ᵖ k″k‴~}
    with ~M′ ← ~ᴹ[/]ᵖ (extractˣ⁻ᶜ kk′~) (`unlift `unit) ~M
      rewrite sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~ = k″k‴~})
            | extractˣ⁻ᶜ-lengthˣ⁻ kk′~ = `unlift-`lift ~M′

[/⁰]~ᴹ[/]ᵖ : (kk′~ : k ⍮ k′ ~ˣ⁻) {k″k‴~ : k″ ⍮ k‴ ~ˣ⁻} →
             kk′~ ++ˣ⁻ k″k‴~ ⊢ DP.L ~ᴹ L →
             kk′~ ++ˣ⁻ !∷ᵖ k″k‴~ ⊢ DP.M ~ᴹ M →
             kk′~ ++ˣ⁻ k″k‴~ ⊢ DP.[ DP.L /⁰ k′ ] DP.M ~ᴹ [ L /[ pMode ] lengthˣ⁻ kk′~ ] M
[/⁰]~ᴹ[/]ᵖ kk′~ ~L `unit = `unit
[/⁰]~ᴹ[/]ᵖ kk′~ {k″k‴~} ~L (`box ~M)
  rewrite extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~ = !∷ᵖ k″k‴~}
    with ~M′ ← ~ᴹ[/]ᵖ (extractˣ⁻ᶜ kk′~) (`unlift `unit) ~M
      rewrite sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~ = k″k‴~})
            | extractˣ⁻ᶜ-lengthˣ⁻ kk′~ = `box ~M′
[/⁰]~ᴹ[/]ᵖ kk′~ ~L (`let-box ~M `in ~N) = `let-box [/⁰]~ᴹ[/]ᵖ kk′~ ~L ~M `in [/⁰]~ᴹ[/]ᵖ (!∷ᶜ kk′~) (wk[↑¹]~ᴹwk[↑]ᶜ [] ~L) ~N
[/⁰]~ᴹ[/]ᵖ {k} {_} {_} {_} {_} {L} kk′~ {k″k‴~} ~L (`#¹_ {u = u} u<)
  with u ℕ.≥? k
...  | no  u≱k
    rewrite sym (<⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ (!∷ᵖ k″k‴~) (ℕ.≰⇒> u≱k) u<)
          | <⇒idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ (?∷ᵖ k″k‴~) (ℕ.≰⇒> u≱k) u< = ~ᴹ[/]ᵖ kk′~ L (`#¹ u<)
...  | yes u≥k
    with u∸k< ← subst (u ∸ k ℕ.<_) (ℕ.m+n∸m≡n k _) (ℕ.∸-monoˡ-< u< u≥k)
      rewrite sym (≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ (!∷ᵖ k″k‴~) u≥k u< u∸k<)
            | ≥⇒lengthˣ⁻+idxˣ⁻ᶜ≡idxˣ⁻ᶜ-++ˣ⁻ kk′~ (?∷ᵖ k″k‴~) u≥k u< u∸k< = ~ᴹ[/]ᵖ kk′~ L (`#¹ u<) 
[/⁰]~ᴹ[/]ᵖ {k} {k′} kk′~ ~L (`λ⦂ ~S ∙ ~M)
  with ~M′ ← [/⁰]~ᴹ[/]ᵖ (!∷ᵖ kk′~) (wk[↑⁰]~ᴹwk[↑]ᵖ [] ~L) ~M
    rewrite ℕ.+-suc k k′ = `λ⦂ ~S ∙ ~M′
[/⁰]~ᴹ[/]ᵖ kk′~ ~L (~M `$ ~N) = [/⁰]~ᴹ[/]ᵖ kk′~ ~L ~M `$ [/⁰]~ᴹ[/]ᵖ kk′~ ~L ~N
[/⁰]~ᴹ[/]ᵖ {_} {k′} {_} {k‴} kk′~ {k″k‴~} ~L (`#⁰_ {x = x} x<)
  with x ℕ.≥? k′
...  | no  x≱k′
    with x<k′ ← ℕ.≰⇒> x≱k′
      rewrite sym (<⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ (!∷ᵖ k″k‴~) x<k′ x<)
            | dec-no (_ ℕ.≥? _) (ℕ.<⇒≱ (idxˣ⁻ᵖ<lengthˣ⁻ kk′~ x<k′))
            | <⇒idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ x<k′ (ℕ.<-transˡ x<k′ (ℕ.m≤m+n _ _)) = `#⁰ ℕ.<-transˡ x<k′ (ℕ.m≤m+n _ _)
...  | yes x≥k′
    with x∸k′< ← subst (x ∸ k′ ℕ.<_) (ℕ.m+n∸m≡n k′ _) (ℕ.∸-monoˡ-< x< x≥k′)
      rewrite sym (≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ (!∷ᵖ k″k‴~) x≥k′ x< x∸k′<)
            | proj₂ (dec-yes (_ ℕ.≤? _) (ℕ.m≤m+n (lengthˣ⁻ kk′~) (idxˣ⁻ᵖ (!∷ᵖ k″k‴~) x∸k′<)))
        with x ℕ.≟ k′
...        | no  x≢k′
          with x>k′ ← ℕ.≤∧≢⇒< x≥k′ (≢-sym x≢k′)
             | s≤s x∸k′≤ ← x∸k′<
            with suc x′ ← x
              rewrite ℕ.+-∸-assoc 1 (ℕ.≤-pred x>k′)
                    | dec-no (_ ℕ.≟ _) (ℕ.m+1+n≢m (lengthˣ⁻ kk′~) {idxˣ⁻ᵖ k″k‴~ x∸k′≤})
                    | ℕ.+-suc (lengthˣ⁻ kk′~) (idxˣ⁻ᵖ k″k‴~ x∸k′≤)
                    | ℕ.+-suc k′ k‴
                    | ≥⇒lengthˣ⁻+idxˣ⁻ᵖ≡idxˣ⁻ᵖ-++ˣ⁻ kk′~ k″k‴~ (ℕ.≤-pred x>k′) (ℕ.≤-pred x<) x∸k′≤ = `#⁰ (ℕ.≤-pred x<)
...        | yes x≡k′
          with s≤s _ ← x∸k′<
            rewrite x≡k′
                  | ℕ.n∸n≡0 k′
                  | proj₂ (dec-yes (_ ℕ.≟ _) (ℕ.+-identityʳ (lengthˣ⁻ kk′~))) = ~L
[/⁰]~ᴹ[/]ᵖ {_} {k′} {_} {_} {DPL} kk′~ {k″k‴~} ~L (`unlift-`lift ~M)
  rewrite ~ᴹ∧≥⇒[/⁰]≡ DPL ~M (z≤n {k′})
        | extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~ = !∷ᵖ k″k‴~}
    with ~M′ ← ~ᴹ[/]ᵖ (extractˣ⁻ᶜ kk′~) (`unlift `unit) ~M
      rewrite sym (extractˣ⁻ᶜ-++ˣ⁻ kk′~ {k″k‴~ = k″k‴~})
            | extractˣ⁻ᶜ-lengthˣ⁻ kk′~ = `unlift-`lift ~M′


~ᴹ-simulation-helper : DP.L DP.⟶ DP.L′ →
                       (~L : [] ⊢ DP.L ~ᴹ L) →
                       Acc ℕ._<_ (depth~ᴹ ~L) →
                       ∃ (λ L′ → L ⟶* L′ × [] ⊢ DP.L′ ~ᴹ L′)
~ᴹ-simulation-helper DP.ξ-`let-box DPL⟶ `in- (`let-box ~L `in ~M) (acc r)
  with _ , ⟶*L′ , ~L′ ← ~ᴹ-simulation-helper DPL⟶ ~L (r _ (s≤s (ℕ.m≤m⊔n _ _))) = -, ξ-of-⟶* (`let-return_`in _) ξ-`let-return_`in- ⟶*L′
                                                                               , `let-box ~L′ `in ~M
~ᴹ-simulation-helper DP.β-`□                 (`let-box ~L `in ~M) (acc r)
  with _ , ⟶*`boxL′ , WL′ , ~L ← `box-~ᴹ-inv ~L = -, ξ-of-⟶* (`let-return_`in _) ξ-`let-return_`in- ⟶*`boxL′
                                                                                    ◅◅ β-`↓ (`lift WL′) ◅ ε
                                                                               , [/¹]~ᴹ[/]ᶜ [] ~L ~M
~ᴹ-simulation-helper DP.ξ- DPL⟶ `$?          (~L `$ ~M)           (acc r)
  with _ , ⟶*L′ , ~L′ ← ~ᴹ-simulation-helper DPL⟶ ~L (r _ (s≤s (ℕ.m≤m⊔n _ _))) = -, ξ-of-⟶* (_`$ _) ξ-_`$? ⟶*L′
                                                                               , ~L′ `$ ~M
~ᴹ-simulation-helper (DP.ξ-! VDPL `$ DPM⟶)   (~L `$ ~M)           (acc r)
  with _ , ⟶*L′ , VL′ , ~L′ ← Value~ᴹ-normalize ~L VDPL
     | _ , ⟶*M′ , ~M′ ← ~ᴹ-simulation-helper DPM⟶ ~M (r _ (s≤s (ℕ.m≤n⊔m _ _))) = -, ξ-of-⟶* (_`$ _) ξ-_`$? ⟶*L′
                                                                                   ◅◅ ξ-of-⟶* (_ `$_) (ξ-! VL′ `$_) ⟶*M′
                                                                               , ~L′ `$ ~M′
~ᴹ-simulation-helper (DP.β-`→ VDPM)          (~L `$ ~M)           (acc r)
  with _ , _ , ⟶*`λ⦂ᵖS′∘L′ , ~L′ , ~S′ ← `λ⦂-∙-~ᴹ-inv ~L
     | _ , ⟶*M′ , VM′ , ~M′ ← Value~ᴹ-normalize ~M VDPM                        = -, ξ-of-⟶* (_`$ _) ξ-_`$? ⟶*`λ⦂ᵖS′∘L′
                                                                                   ◅◅ ξ-of-⟶* (_ `$_) ξ-! `λ⦂ᵖ _ ∘ _ `$_ ⟶*M′
                                                                                   ◅◅ β-`⊸ VM′ ◅ ε
                                                                               , [/⁰]~ᴹ[/]ᵖ [] ~M′ ~L′
~ᴹ-simulation-helper DPL⟶                    (`unlift-`lift ~L)   (acc r)
  with _ , ⟶*L′[≤] , VL′ , ~L′ , L′≤ ← ~ᴹ-normalize[≤] ~L
    with _ , ⟶*L″ , ~L″ ← ~ᴹ-simulation-helper DPL⟶ ~L′ (r _ (s≤s L′≤))        = -, ξ-of-⟶* `unlift ξ-`unlift (ξ-of-↝*-⟶* _⟶[ cMode ≤]_ `lift ξ-`lift ⟶*L′[≤])
                                                                                    ◅◅ β-`↑ VL′ ◅ ⟶*L″
                                                                               , ~L″

~ᴹ-simulation : DP.L DP.⟶ DP.L′ →
                [] ⊢ DP.L ~ᴹ L →
                ∃ (λ L′ → L ⟶* L′ × [] ⊢ DP.L′ ~ᴹ L′)
~ᴹ-simulation DPL⟶ ~L = ~ᴹ-simulation-helper DPL⟶ ~L (ℕ.<-wellFounded _)

~ᴹ⁻¹-simulation : L ⟶ L′ →
                  [] ⊢ DP.L ~ᴹ L →
                  ∃ (λ DPL′ → DP.L DP.⟶* DPL′ × [] ⊢ DPL′ ~ᴹ L′)
~ᴹ⁻¹-simulation (ξ-`unlift (ξ-`lift L⟶[≤])) (`unlift-`lift ~L)        = -, ε , `unlift-`lift (⟶[≤]-preserves-~ᴹ ~L L⟶[≤])
~ᴹ⁻¹-simulation (β-`↑ WL′)                  (`unlift-`lift ~L)        = -, ε , ~L
~ᴹ⁻¹-simulation (ξ-`return (ξ-`lift L⟶[≤])) (`box ~L)                 = -, ε , `box (⟶[≤]-preserves-~ᴹ ~L L⟶[≤])
~ᴹ⁻¹-simulation ξ-`let-return L⟶ `in-       (`let-box ~L `in ~M)
  with _ , DPL⟶* , ~L′ ← ~ᴹ⁻¹-simulation L⟶ ~L                        = -, DP.ξ-of-⟶* (DP.`let-box_`in _) DP.ξ-`let-box_`in- DPL⟶* , `let-box ~L′ `in ~M
~ᴹ⁻¹-simulation (β-`↓ (`lift WL))           (`let-box `box ~L `in ~M) = -, DP.β-`□ ◅ ε , [/¹]~ᴹ[/]ᶜ [] ~L ~M
~ᴹ⁻¹-simulation ξ- L⟶ `$?                   (~L `$ ~M)
  with _ , DPL⟶* , ~L′ ← ~ᴹ⁻¹-simulation L⟶ ~L                        = -, DP.ξ-of-⟶* (DP._`$ _) DP.ξ-_`$? DPL⟶* , ~L′ `$ ~M
~ᴹ⁻¹-simulation (ξ-! VL′ `$ M⟶)             (~L `$ ~M)
  with _ , DPM⟶* , ~M′ ← ~ᴹ⁻¹-simulation M⟶ ~M                        = -, DP.ξ-of-⟶* (_ DP.`$_) (DP.ξ-! []⊢~ᴹ⁻¹-respects-Value ~L VL′ `$_) DPM⟶* , ~L `$ ~M′
~ᴹ⁻¹-simulation (β-`⊸ VM)                   ((`λ⦂ ~S ∙ ~L) `$ ~M)     = -, DP.β-`→ ([]⊢~ᴹ⁻¹-respects-Value ~M VM) ◅ ε , [/⁰]~ᴹ[/]ᵖ [] ~M ~L

