{-# OPTIONS --safe #-}
module Syntax.Church.STLC.WithSum.Alt.Properties where

open import Data.Nat                              using (suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Syntax.Church.STLC.WithSum.Alt.Base
open Variables

----------------------------------------------------------
-- Useful Properties for _`∷_
----------------------------------------------------------
`∷ˢ-`++ˢ-commute : ∀ e (ee : ExE Γ A B) (es : ExEs _ _ C) →
                   e `∷ˢ ee `++ˢ es ≡ e `++ˢ (ee `∷ es)
`∷ˢ-`++ˢ-commute e ee `[] = refl
`∷ˢ-`++ˢ-commute e ee (es `∷ˢ ee′) = cong (_`∷ˢ ee′) (`∷ˢ-`++ˢ-commute e ee es)

`∷-lengthˢ : ∀ (ee : ExE Γ A B) (es : ExEs Γ B C) →
             lengthˢ (ee `∷ es) ≡ suc (lengthˢ es)
`∷-lengthˢ ee `[]        = refl
`∷-lengthˢ ee (es `∷ˢ _) = cong suc (`∷-lengthˢ ee es)
