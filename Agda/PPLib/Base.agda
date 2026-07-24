{-# OPTIONS --safe --without-K #-}
module PPLib.Base where

open import Agda.Primitive                        using (Level)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

variable
  ℓ ℓ′ ℓ″ ℓ‴ : Level

cong₃ : ∀ {A : Set ℓ} {B : Set ℓ′} {C : Set ℓ″} {D : Set ℓ‴}
          (f : A → B → C → D) {a a′ b b′ c c′} →
        a ≡ a′ → b ≡ b′ → c ≡ c′ → f a b c ≡ f a′ b′ c′
cong₃ f refl refl refl = refl
