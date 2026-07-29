{-# OPTIONS --safe --without-K #-}
module PPLib.Base where

open import Agda.Primitive                                        using (Level)
open import Relation.Binary.PropositionalEquality                 using (_≡_; refl; cong)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive using (Star; ε; _◅_; _◅◅_)

private
  variable
    ℓ ℓ′ ℓ″ ℓ‴ : Level

cong₃ : ∀ {A : Set ℓ} {B : Set ℓ′} {C : Set ℓ″} {D : Set ℓ‴}
          (f : A → B → C → D) {a a′ b b′ c c′} →
        a ≡ a′ → b ≡ b′ → c ≡ c′ → f a b c ≡ f a′ b′ c′
cong₃ f refl refl refl = refl

◅◅-identityʳ : ∀ {A : Set ℓ} {T : A → A → Set ℓ′} {i j}
                 (es : Star T i j) →
               ----------------------
               es ◅◅ ε ≡ es
◅◅-identityʳ ε         = refl
◅◅-identityʳ (ee ◅ es) = cong (_ ◅_) (◅◅-identityʳ es)
