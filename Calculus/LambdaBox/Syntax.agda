{-# OPTIONS --safe #-}
module Calculus.LambdaBox.Syntax where

open import Data.Nat using (ℕ)
open import Data.List using (List)

data Type : Set where
  `⊤   : Type
  _`→_ : Type → Type → Type
  `□_  : Type → Type

data Term : Set where
  `unit         : Term

  `box          : Term → Term
  `let-box_`in_ : Term → Term → Term

  `λ⦂_∙_        : Type → Term → Term
  _`$_          : Term → Term → Term

  `#¹_          : ℕ → Term
  `#⁰_          : ℕ → Term

Context : Set
Context = List Type

variable
  x x′ x″ x‴ x₀ x₁ x₂ x₃ y y′ y″ y‴ y₀ y₁ y₂ y₃ u u′ u″ u‴ u₀ u₁ u₂ u₃ v v′ v″ v‴ v₀ v₁ v₂ v₃ : ℕ
  S S′ S″ S‴ S₀ S₁ S₂ S₃ T T′ T″ T‴ T₀ T₁ T₂ T₃ : Type
  L L′ L″ L‴ L₀ L₁ L₂ L₃ M M′ M″ M‴ M₀ M₁ M₂ M₃ N N′ N″ N‴ N₀ N₁ N₂ N₃ : Term
  Γ Γ′ Γ″ Γ‴ Γ₀ Γ₁ Γ₂ Γ₃ Δ Δ′ Δ″ Δ‴ Δ₀ Δ₁ Δ₂ Δ₃ Ψ Ψ′ Ψ″ Ψ‴ Ψ₀ Ψ₁ Ψ₂ Ψ₃ : Context

-- _⟶*_ : Term → Term → Set
-- _⟶*_ = Star _⟶_

-- *lift-⟶-cong : (f : Term → Term) →
--                (∀ {M M′} → M ⟶ M′ → f M ⟶ f M′) →
--                ∀ {M M′} → M ⟶* M′ → f M ⟶* f M′
-- *lift-⟶-cong f cong ε           = ε
-- *lift-⟶-cong f cong (e⟶ ◅ e′⟶*) = cong e⟶ ◅ *lift-⟶-cong f cong e′⟶*

-- ------------------------------------------------------------
-- -- Properties of Substitutions and Weakenings
-- ------------------------------------------------------------
-- wkwkby¹from¹≡wkby¹from¹ : ∀ n m l M₀ →
--                           ------------------------------------------------------------------
--                           wk wk M₀ by¹ n from¹ l by¹ m from¹ l ≡ wk M₀ by¹ (n + m) from¹ l
-- wkwkby¹from¹≡wkby¹from¹ n m l (box M₀)        = cong box (wkwkby¹from¹≡wkby¹from¹ n m l M₀)
-- wkwkby¹from¹≡wkby¹from¹ n m l (let-box M₀ N₀) = cong₂ let-box (wkwkby¹from¹≡wkby¹from¹ n m l M₀) (wkwkby¹from¹≡wkby¹from¹ n m (suc l) N₀)
-- wkwkby¹from¹≡wkby¹from¹ n m l (#¹ u)          = cong #¹_ (wkvarwkvar≡wkvar n m l u)
-- wkwkby¹from¹≡wkby¹from¹ n m l (#⁰ x)          = refl
-- wkwkby¹from¹≡wkby¹from¹ n m l (Λ S₀ ∙ M₀)     = cong (Λ S₀ ∙_) (wkwkby¹from¹≡wkby¹from¹ n m l M₀)
-- wkwkby¹from¹≡wkby¹from¹ n m l (M₀ $ N₀)       = cong₂ _$_ (wkwkby¹from¹≡wkby¹from¹ n m l M₀) (wkwkby¹from¹≡wkby¹from¹ n m l N₀)

-- wkwkby⁰from⁰≡wkby⁰from⁰ : ∀ n m l M₀ →
--                           ------------------------------------------------------------------
--                           wk wk M₀ by⁰ n from⁰ l by⁰ m from⁰ l ≡ wk M₀ by⁰ (n + m) from⁰ l
-- wkwkby⁰from⁰≡wkby⁰from⁰ n m l (box M₀)        = refl
-- wkwkby⁰from⁰≡wkby⁰from⁰ n m l (let-box M₀ N₀) = cong₂ let-box (wkwkby⁰from⁰≡wkby⁰from⁰ n m l M₀) (wkwkby⁰from⁰≡wkby⁰from⁰ n m l N₀)
-- wkwkby⁰from⁰≡wkby⁰from⁰ n m l (#¹ u)          = refl
-- wkwkby⁰from⁰≡wkby⁰from⁰ n m l (#⁰ x)          = cong #⁰_ (wkvarwkvar≡wkvar n m l x)
-- wkwkby⁰from⁰≡wkby⁰from⁰ n m l (Λ S₀ ∙ M₀)     = cong (Λ S₀ ∙_) (wkwkby⁰from⁰≡wkby⁰from⁰ n m (suc l) M₀)
-- wkwkby⁰from⁰≡wkby⁰from⁰ n m l (M₀ $ N₀)       = cong₂ _$_ (wkwkby⁰from⁰≡wkby⁰from⁰ n m l M₀) (wkwkby⁰from⁰≡wkby⁰from⁰ n m l N₀)

-- wkby⁰from⁰wkby¹from¹-commute : ∀ n m l o M₀ →
--                                ------------------------------------------------------------------------------
--                                wk wk M₀ by¹ l from¹ o by⁰ n from⁰ m ≡ wk wk M₀ by⁰ n from⁰ m by¹ l from¹ o
-- wkby⁰from⁰wkby¹from¹-commute n m l o (box M₀)        = refl
-- wkby⁰from⁰wkby¹from¹-commute n m l o (let-box M₀ N₀) = cong₂ let-box (wkby⁰from⁰wkby¹from¹-commute n m l o M₀) (wkby⁰from⁰wkby¹from¹-commute n m l (suc o) N₀)
-- wkby⁰from⁰wkby¹from¹-commute n m l o (#¹ u)          = refl
-- wkby⁰from⁰wkby¹from¹-commute n m l o (#⁰ x)          = refl
-- wkby⁰from⁰wkby¹from¹-commute n m l o (Λ S₀ ∙ M₀)     = cong (Λ S₀ ∙_) (wkby⁰from⁰wkby¹from¹-commute n (suc m) l o M₀)
-- wkby⁰from⁰wkby¹from¹-commute n m l o (M₀ $ N₀)       = cong₂ _$_ (wkby⁰from⁰wkby¹from¹-commute n m l o M₀) (wkby⁰from⁰wkby¹from¹-commute n m l o N₀)


-- wkby¹0from¹ : ∀ n M₀ →
--               ------------------------
--               wk M₀ by¹ 0 from¹ n ≡ M₀
-- wkby¹0from¹ n (box M₀)        = cong box (wkby¹0from¹ n M₀)
-- wkby¹0from¹ n (let-box M₀ N₀) = cong₂ let-box (wkby¹0from¹ n M₀) (wkby¹0from¹ (suc n) N₀)
-- wkby¹0from¹ n (#¹ u)          = cong #¹_ (wkvarby0 n u)
-- wkby¹0from¹ n (#⁰ x)          = refl
-- wkby¹0from¹ n (Λ S₀ ∙ M₀)     = cong (Λ S₀ ∙_) (wkby¹0from¹ n M₀)
-- wkby¹0from¹ n (M₀ $ N₀)       = cong₂ _$_ (wkby¹0from¹ n M₀) (wkby¹0from¹ n N₀)

-- wkby⁰0from⁰ : ∀ n M₀ →
--               ------------------------
--               wk M₀ by⁰ 0 from⁰ n ≡ M₀
-- wkby⁰0from⁰ n (box M₀)        = refl
-- wkby⁰0from⁰ n (let-box M₀ N₀) = cong₂ let-box (wkby⁰0from⁰ n M₀) (wkby⁰0from⁰ n N₀)
-- wkby⁰0from⁰ n (#¹ u)          = refl
-- wkby⁰0from⁰ n (#⁰ x)          = cong #⁰_ (wkvarby0 n x)
-- wkby⁰0from⁰ n (Λ S₀ ∙ M₀)     = cong (Λ S₀ ∙_) (wkby⁰0from⁰ (suc n) M₀)
-- wkby⁰0from⁰ n (M₀ $ N₀)       = cong₂ _$_ (wkby⁰0from⁰ n M₀) (wkby⁰0from⁰ n N₀)


-- ⊢wkby¹from¹ : ∀ Φ₁″ Φ₁′ →
--               Φ₁″ ++ Φ₁ ⍮ Φ₀ ⊢ M₀ ⦂ S₀ →
--               -----------------------------------------------------------------
--               Φ₁″ ++ Φ₁′ ++ Φ₁ ⍮ Φ₀ ⊢ wk M₀ by¹ length Φ₁′ from¹ length Φ₁″ ⦂ S₀
-- ⊢wkby¹from¹ Φ₁″ Φ₁′ (box ⊢M₀)         = box (⊢wkby¹from¹ Φ₁″ Φ₁′ ⊢M₀)
-- ⊢wkby¹from¹ Φ₁″ Φ₁′ (let-box ⊢M₀ ⊢N₀) = let-box (⊢wkby¹from¹ Φ₁″ Φ₁′ ⊢M₀) (⊢wkby¹from¹ (_ ∷ Φ₁″) Φ₁′ ⊢N₀)
-- ⊢wkby¹from¹ Φ₁″ Φ₁′ (#¹ u∈)           = #¹ wkvar∈ Φ₁″ Φ₁′ u∈
-- ⊢wkby¹from¹ Φ₁″ Φ₁′ (#⁰ x∈)           = #⁰ x∈
-- ⊢wkby¹from¹ Φ₁″ Φ₁′ (Λ?∙ ⊢M₀)         = Λ?∙ ⊢wkby¹from¹ Φ₁″ Φ₁′ ⊢M₀
-- ⊢wkby¹from¹ Φ₁″ Φ₁′ (⊢M₀ $ ⊢N₀)       = ⊢wkby¹from¹ Φ₁″ Φ₁′ ⊢M₀ $ ⊢wkby¹from¹ Φ₁″ Φ₁′ ⊢N₀

-- ⊢wkby⁰from⁰ : ∀ Φ₀″ Φ₀′ →
--               Φ₁ ⍮ Φ₀″ ++ Φ₀ ⊢ M₀ ⦂ S₀ →
--               -----------------------------------------------------------------
--               Φ₁ ⍮ Φ₀″ ++ Φ₀′ ++ Φ₀ ⊢ wk M₀ by⁰ length Φ₀′ from⁰ length Φ₀″ ⦂ S₀
-- ⊢wkby⁰from⁰ Φ₀″ Φ₀′ (box ⊢M₀)         = box ⊢M₀
-- ⊢wkby⁰from⁰ Φ₀″ Φ₀′ (let-box ⊢M₀ ⊢N₀) = let-box (⊢wkby⁰from⁰ Φ₀″ Φ₀′ ⊢M₀) (⊢wkby⁰from⁰ Φ₀″ Φ₀′ ⊢N₀)
-- ⊢wkby⁰from⁰ Φ₀″ Φ₀′ (#¹ u∈)           = #¹ u∈
-- ⊢wkby⁰from⁰ Φ₀″ Φ₀′ (#⁰ x∈)           = #⁰ wkvar∈ Φ₀″ Φ₀′ x∈
-- ⊢wkby⁰from⁰ Φ₀″ Φ₀′ (Λ?∙ ⊢M₀)         = Λ?∙ ⊢wkby⁰from⁰ (_ ∷ Φ₀″) Φ₀′ ⊢M₀
-- ⊢wkby⁰from⁰ Φ₀″ Φ₀′ (⊢M₀ $ ⊢N₀)       = ⊢wkby⁰from⁰ Φ₀″ Φ₀′ ⊢M₀ $ ⊢wkby⁰from⁰ Φ₀″ Φ₀′ ⊢N₀

-- ≤⇒⊢⇒wk≡ : ∀ n {m} →
--           length Φ₀ ≤ m →
--           Φ₁ ⍮ Φ₀ ⊢ M₀ ⦂ S₀ →
--           wk M₀ by⁰ n from⁰ m ≡ M₀
-- ≤⇒⊢⇒wk≡ n Φ₀≤ (box ⊢M₀)         = refl
-- ≤⇒⊢⇒wk≡ n Φ₀≤ (let-box ⊢M₀ ⊢N₀) = cong₂ let-box (≤⇒⊢⇒wk≡ n Φ₀≤ ⊢M₀) (≤⇒⊢⇒wk≡ n Φ₀≤ ⊢N₀)
-- ≤⇒⊢⇒wk≡ n Φ₀≤ (#¹ u∈)           = refl
-- ≤⇒⊢⇒wk≡ n Φ₀≤ (#⁰ x∈)           = cong #⁰_ (<⇒wkvar≡ _ (<-transˡ (∈⇒< x∈) Φ₀≤))
-- ≤⇒⊢⇒wk≡ n Φ₀≤ (Λ?∙ ⊢M₀)         = cong (Λ _ ∙_) (≤⇒⊢⇒wk≡ n (s≤s Φ₀≤) ⊢M₀)
-- ≤⇒⊢⇒wk≡ n Φ₀≤ (⊢M₀ $ ⊢N₀)       = cong₂ _$_ (≤⇒⊢⇒wk≡ n Φ₀≤ ⊢M₀) (≤⇒⊢⇒wk≡ n Φ₀≤ ⊢N₀)

-- ⊢[/¹] : ∀ Φ₁′ →
--         Φ₁ ⍮ [] ⊢ M₀ ⦂ S₀ →
--         Φ₁′ ++ (S₀ ∷ Φ₁) ⍮ Φ₀ ⊢ N₀ ⦂ T₀ →
--         -------------------------------------------------------------------------
--         Φ₁′ ++ Φ₁ ⍮ Φ₀ ⊢ [ wk M₀ by¹ (length Φ₁′) from¹ 0 /¹ length Φ₁′ ] N₀ ⦂ T₀
-- ⊢[/¹]           Φ₁′ ⊢M₀ (box ⊢N₀)                               = box (⊢[/¹] Φ₁′ ⊢M₀ ⊢N₀)
-- ⊢[/¹] {M₀ = M₀} Φ₁′ ⊢M₀ (let-box ⊢N₀ ⊢L₀)
--   with ⊢L₀′ ← ⊢[/¹] (_ ∷ Φ₁′) ⊢M₀ ⊢L₀
--     rewrite +-comm 1 (length Φ₁′)
--           | ≡.sym (wkwkby¹from¹≡wkby¹from¹ (length Φ₁′) 1 0 M₀) = let-box (⊢[/¹] Φ₁′ ⊢M₀ ⊢N₀) ⊢L₀′
-- ⊢[/¹] {S₀ = S₀} Φ₁′ ⊢M₀ (#¹_ {u = u} u∈)
--   with length Φ₁′ ≟ u
-- ...  | yes refl
--     rewrite length∈-++⇒≡ Φ₁′ u∈                                 = ⊢wkby¹from¹ [] Φ₁′ (subst₂ (_ ⍮_⊢_⦂ _) (++-identityʳ _) (≤⇒⊢⇒wk≡ _ z≤n ⊢M₀) (⊢wkby⁰from⁰ [] _ ⊢M₀))
-- ...  | no  ≢u
--     with length Φ₁′ <? u
-- ...    | no  ≮u                                                 = #¹ (>∈-++-++⇒∈-++ Φ₁′ L.[ _ ] (≤∧≢⇒< (≮⇒≥ ≮u) (≢-sym ≢u)) u∈)
-- ...    | yes <u
--       rewrite +-comm 1 (length Φ₁′)
--             | ≡.sym (length-++ Φ₁′ {L.[ S₀ ]})                  = #¹ ≤∈-++-++⇒∈-++ Φ₁′ L.[ _ ] <u u∈
-- ⊢[/¹]           Φ₁′ ⊢M₀ (#⁰ x∈)                                 = #⁰ x∈
-- ⊢[/¹]           Φ₁′ ⊢M₀ (Λ?∙ ⊢N₀)                               = Λ?∙ ⊢[/¹] Φ₁′ ⊢M₀ ⊢N₀
-- ⊢[/¹]           Φ₁′ ⊢M₀ (⊢N₀ $ ⊢L₀)                             = ⊢[/¹] Φ₁′ ⊢M₀ ⊢N₀ $ ⊢[/¹] Φ₁′ ⊢M₀ ⊢L₀

-- ⊢[/⁰] : ∀ Φ₀′ →
--         Φ₁ ⍮ Φ₀ ⊢ M₀ ⦂ S₀ →
--         Φ₁ ⍮ Φ₀′ ++ (S₀ ∷ Φ₀) ⊢ N₀ ⦂ T₀ →
--         -------------------------------------------------------------------------
--         Φ₁ ⍮ Φ₀′ ++ Φ₀ ⊢ [ wk M₀ by⁰ (length Φ₀′) from⁰ 0 /⁰ length Φ₀′ ] N₀ ⦂ T₀
-- ⊢[/⁰]           Φ₀′ ⊢M₀ (box ⊢N₀)                               = box ⊢N₀
-- ⊢[/⁰] {M₀ = M₀} Φ₀′ ⊢M₀ (let-box ⊢N₀ ⊢L₀)
--   with ⊢L₀′ ← ⊢[/⁰] Φ₀′ (⊢wkby¹from¹ [] L.[ _ ] ⊢M₀) ⊢L₀
--     rewrite wkby⁰from⁰wkby¹from¹-commute (length Φ₀′) 0 1 0 M₀  = let-box (⊢[/⁰] Φ₀′ ⊢M₀ ⊢N₀) ⊢L₀′
-- ⊢[/⁰]           Φ₀′ ⊢M₀ (#¹ u∈)                                 = #¹ u∈
-- ⊢[/⁰] {S₀ = S₀} Φ₀′ ⊢M₀ (#⁰_ {x = x} x∈)
--   with length Φ₀′ ≟ x
-- ...  | yes refl
--     rewrite length∈-++⇒≡ Φ₀′ x∈                                 = ⊢wkby⁰from⁰ [] Φ₀′ ⊢M₀
-- ...  | no  ≢x
--     with length Φ₀′ <? x
-- ...    | no  ≮x                                                 = #⁰ (>∈-++-++⇒∈-++ Φ₀′ L.[ _ ] (≤∧≢⇒< (≮⇒≥ ≮x) (≢-sym ≢x)) x∈)
-- ...    | yes <x
--       rewrite +-comm 1 (length Φ₀′)
--             | ≡.sym (length-++ Φ₀′ {L.[ S₀ ]})                  = #⁰ ≤∈-++-++⇒∈-++ Φ₀′ L.[ _ ] <x x∈
-- ⊢[/⁰] {M₀ = M₀} Φ₀′ ⊢M₀ (Λ?∙ ⊢N₀)
--   with ⊢N₀′ ← ⊢[/⁰] (_ ∷ Φ₀′) ⊢M₀ ⊢N₀
--     rewrite +-comm 1 (length Φ₀′)
--           | ≡.sym (wkwkby⁰from⁰≡wkby⁰from⁰ (length Φ₀′) 1 0 M₀) = Λ?∙ ⊢N₀′
-- ⊢[/⁰]           Φ₀′ ⊢M₀ (⊢N₀ $ ⊢L₀)                             = ⊢[/⁰] Φ₀′ ⊢M₀ ⊢N₀ $ ⊢[/⁰] Φ₀′ ⊢M₀ ⊢L₀

-- ------------------------------------------------------------
-- -- Type Safety
-- ------------------------------------------------------------
-- preservation : [] ⍮ [] ⊢ M₀ ⦂ S₀ →
--                M₀ ⟶ M₀′ →
--                -------------------------------
--                [] ⍮ [] ⊢ M₀′ ⦂ S₀
-- preservation (let-box ⊢M₀       ⊢N₀) (cong-let-box M₀⟶) = let-box (preservation ⊢M₀ M₀⟶) ⊢N₀
-- preservation (let-box (box ⊢M₀) ⊢N₀) (β-□ {M₀ = M₀})
--   with ⊢N₀′ ← ⊢[/¹] [] ⊢M₀ ⊢N₀
--     rewrite wkby¹0from¹ 0 M₀                            = ⊢N₀′
-- preservation (⊢M₀       $ ⊢N₀)       (congˡ-$ M₀⟶)      = preservation ⊢M₀ M₀⟶ $ ⊢N₀
-- preservation (⊢M₀       $ ⊢N₀)       (congʳ-$ _ N₀⟶)    = ⊢M₀ $ preservation ⊢N₀ N₀⟶
-- preservation ((Λ?∙ ⊢M₀) $ ⊢N₀)       (β-⇒ {N₀ = N₀} _)
--   with ⊢M₀′ ← ⊢[/⁰] [] ⊢N₀ ⊢M₀
--     rewrite wkby⁰0from⁰ 0 N₀                           = ⊢M₀′

-- progress : [] ⍮ [] ⊢ M₀ ⦂ S₀ →
--            -----------------
--            Value M₀ ⊎ (∃ λ M₀′ → M₀ ⟶ M₀′)
-- progress (box _)           = inj₁ (box _)
-- progress (let-box ⊢M₀ ⊢N₀)
--   with progress ⊢M₀
-- ...  | inj₂ (_ , M₀⟶)      = inj₂ (-, cong-let-box M₀⟶)
-- ...  | inj₁ (box _)        = inj₂ (-, β-□)
-- progress (Λ?∙ ⊢M₀)         = inj₁ (Λ _ ∙ _)
-- progress (⊢M₀ $ ⊢N₀)
--   with progress ⊢M₀
-- ...  | inj₂ (_ , M₀⟶)      = inj₂ (-, congˡ-$ M₀⟶)
-- ...  | inj₁ VM₀@(Λ _ ∙ _)
--     with progress ⊢N₀
-- ...    | inj₂ (_ , N₀⟶)    = inj₂ (-, congʳ-$ VM₀ N₀⟶)
-- ...    | inj₁ VN₀          = inj₂ (-, β-⇒ VN₀)
