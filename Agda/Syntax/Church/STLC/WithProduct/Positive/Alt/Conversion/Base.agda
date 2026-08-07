{-# OPTIONS --safe #-}
module Syntax.Church.STLC.WithProduct.Positive.Alt.Conversion.Base where

open import Agda.Primitive                     using (lzero)
open import Data.List                          using (_∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Nat                           using (ℕ; zero; suc)
open import Relation.Binary                    using (REL)

open import Syntax.Church.STLC.WithProduct.Positive.Base     hiding (module Variables)
open import Syntax.Church.STLC.WithProduct.Positive.Alt.Base

convEx : ∀ {Γ A} → Ex Γ A → Tm Γ A
convExE : ∀ {Γ A B} → ExE Γ A B → (Tm Γ A → Tm Γ B)

convEx (`# x)     = `# x
convEx (`λ e)     = `λ convEx e
convEx (e `, f)   = convEx e `, convEx f
convEx (e `∷ᵉ ee) = convExE ee (convEx e)

convExE (-`$ f)      M = M `$ convEx f
convExE (`let-`in f) M = `let M `in convEx f

convTm : ∀ {Γ A} → Tm Γ A → Ex Γ A
convTm (`# x)         = `# x
convTm (`λ M)         = `λ convTm M
convTm (M `$ N)       = convTm M `∷ᵉ -`$ convTm N
convTm (M `, N)       = convTm M `, convTm N
convTm (`let M `in N) = convTm M `∷ᵉ `let-`in convTm N
