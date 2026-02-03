open import Relation.Binary.Core

module Math.CompletePartialOrder.Monotone
  {a b aℓ aℓ′ bℓ bℓ′} {A : Set a} {B : Set b}
  (_≈a_ : Rel A aℓ)
  (_≤a_ : Rel A aℓ′)
  (_≈b_ : Rel B bℓ)
  (_≤b_ : Rel B bℓ′)
  where

open import Agda.Primitive
open import Data.Product
open import Data.Sum
open import Function.Definitions
open import Function.Structures
open import Relation.Binary.Structures
open import Relation.Unary
open import Math.CompletePartialOrder.Base

private
  variable
    aℓ″ bℓ″ : Level

_$$_ : (f : A → B) → (P : Pred A aℓ″) → Pred B (a ⊔ bℓ ⊔ aℓ″)
_$$_ f P = λ u → ∃ λ x → P x × u ≈b f x

record IsMonotone (f : A → B) : Set (lsuc (a ⊔ aℓ ⊔ aℓ′ ⊔ aℓ″ ⊔ b ⊔ bℓ ⊔ bℓ′)) where
  field
    cong : Congruent _≈a_ _≈b_ f
    isCPOˡ : IsCPO _≈a_ _≤a_
    isCPOʳ : IsCPO _≈b_ _≤b_
    monotone : ∀ {x y : A} → x ≤a y → f x ≤b f y

  module isCPOˡ = IsCPO isCPOˡ
  module isCPOʳ = IsCPO isCPOʳ

  isCongruent : IsCongruent _≈a_ _≈b_ f
  isCongruent = record
    { cong = cong
    ; isEquivalence₁ = isCPOˡ.isEquivalence
    ; isEquivalence₂ = isCPOʳ.isEquivalence
    }

  isDirectedˡ⇒isDirectedʳ : ∀ {P : Pred A aℓ″} →
                            IsDirected _≈a_ _≤a_ P →
                            IsDirected _≈b_ _≤b_ (f $$ P)
  isDirectedˡ⇒isDirectedʳ isDirectedˡ = record
    { isSubset = {!!}
    ; satisfiable = f (proj₁ isDirectedˡ.satisfiable)
                  , proj₁ isDirectedˡ.satisfiable
                  , proj₂ isDirectedˡ.satisfiable
                  , IsCPO.Eq.refl isCPOʳ
    ; isPartialOrder = isCPOʳ.isPartialOrder
    ; directed = λ{ {fx} {fy} (x , Px , fx≈) (y , Py , fy≈) →
        let z , x≤z , y≤z , Pz = isDirectedˡ.directed Px Py in
        f z
        , isCPOʳ.≤-respˡ-≈ (isCPOʳ.Eq.sym fx≈) (monotone x≤z)
        , isCPOʳ.≤-respˡ-≈ (isCPOʳ.Eq.sym fy≈) (monotone y≤z)
        , z
        , Pz
        , isCPOʳ.Eq.refl }
    }
    where
      module isDirectedˡ = IsDirected isDirectedˡ

  isDirectedˡ⇒f$$⊔P≤⊔[f$$P] : ∀ {P : Pred A aℓ″} →
                              (isDirectedˡ : IsDirected _≈a_ _≤a_ P) →
                              proj₁ (isCPOʳ.complete (isDirectedˡ⇒isDirectedʳ isDirectedˡ)) ≤b f (proj₁ (isCPOˡ.complete isDirectedˡ))
  isDirectedˡ⇒f$$⊔P≤⊔[f$$P] {P} isDirectedˡ = IsLUB.least isLUBʳ isUBʳ
    where
      isLUBˡ = proj₂ (isCPOˡ.complete isDirectedˡ)
      isLUBʳ = proj₂ (isCPOʳ.complete (isDirectedˡ⇒isDirectedʳ isDirectedˡ))

      isUBʳ : IsUB _≈b_ _≤b_ (f $$ P) (f (proj₁ (isCPOˡ.complete isDirectedˡ)))
      isUBʳ = record
        { isSubset = {!!}
        ; isPartialOrder = isCPOʳ.isPartialOrder
        ; upperbound = λ{ {fx} (x , Px , fx≈) → isCPOʳ.≤-respˡ-≈ (isCPOʳ.Eq.sym fx≈) (monotone (IsLUB.upperbound isLUBˡ Px)) }
        }

record IsContinuous (f : A → B) : Set (lsuc (a ⊔ aℓ ⊔ aℓ′ ⊔ b ⊔ bℓ ⊔ bℓ′)) where
  open IsCPO
  field
    cong : Congruent _≈a_ _≈b_ f
    isCPOˡ : IsCPO _≈a_ _≤a_
    isCPOʳ : IsCPO _≈b_ _≤b_

  module isCPOˡ = IsCPO isCPOˡ
  module isCPOʳ = IsCPO isCPOʳ

  field
    continuous : ∀ {P : Pred A aℓ} →
                 (isDirectedˡ : IsDirected _≈a_ _≤a_ P) →
                 Σ (IsDirected _≈b_ _≤b_ (f $$ P))
                   λ isDirectedʳ → f (proj₁ (isCPOˡ.complete isDirectedˡ)) ≈b proj₁ (isCPOʳ.complete isDirectedʳ)

  isMonotone : IsMonotone f
  isMonotone = record
    { cong = cong
    ; isCPOˡ = isCPOˡ
    ; isCPOʳ = isCPOʳ
    ; monotone = λ {x} x≤y →
        isCPOʳ.≤-respʳ-≈
          (isCPOʳ.Eq.sym
            (isCPOʳ.Eq.trans
              (cong (IsLUB.unique (isLUBˡ x≤y) (proj₂ (isCPOˡ.complete (isDirectedˡ x≤y)))))
              (f⊔P≈⊔fP x≤y)))
          (IsLUB.upperbound
            (proj₂ (isCPOʳ.complete (isDirectedʳ x≤y)))
            (x , inj₁ isCPOˡ.Eq.refl , isCPOʳ.Eq.refl))
    }
    where
      ⟦_,_⟧ : A → A → Pred A aℓ
      ⟦ x , y ⟧ = λ z → z ≈a x ⊎ z ≈a y

      isSubsetˡ : ∀ {x y} → IsSubset _≈a_ _≤a_ ⟦ x , y ⟧
      isSubsetˡ = record
        { P-resp-≈ = λ{ z≈w (inj₁ z≈x) → inj₁ (isCPOˡ.Eq.trans (isCPOˡ.Eq.sym z≈w) z≈x)
                      ; z≈w (inj₂ z≈y) → inj₂ (isCPOˡ.Eq.trans (isCPOˡ.Eq.sym z≈w) z≈y) }
        }

      isDirectedˡ : ∀ {x y} → x ≤a y → IsDirected _≈a_ _≤a_ ⟦ x , y ⟧
      isDirectedˡ {x} {y} x≤y = record
        { isSubset = isSubsetˡ
        ; satisfiable = x , inj₁ isCPOˡ.Eq.refl
        ; isPartialOrder = isCPOˡ.isPartialOrder
        ; directed = λ{ (inj₁ x′≈x) (inj₁ y′≈x) → x
                                                , isCPOˡ.reflexive x′≈x
                                                , isCPOˡ.reflexive y′≈x
                                                , inj₁ isCPOˡ.Eq.refl
                      ; (inj₁ x′≈x) (inj₂ y′≈y) → y
                                                , isCPOˡ.≤-respˡ-≈ (isCPOˡ.Eq.sym x′≈x) x≤y
                                                , isCPOˡ.reflexive y′≈y
                                                , inj₂ isCPOˡ.Eq.refl
                      ; (inj₂ x′≈y) (inj₁ y′≈x) → y
                                                , isCPOˡ.reflexive x′≈y
                                                , isCPOˡ.≤-respˡ-≈ (isCPOˡ.Eq.sym y′≈x) x≤y
                                                , inj₂ isCPOˡ.Eq.refl
                      ; (inj₂ x′≈y) (inj₂ y′≈y) → y
                                                , isCPOˡ.reflexive x′≈y
                                                , isCPOˡ.reflexive y′≈y
                                                , inj₂ isCPOˡ.Eq.refl }
        }

      isUBˡ : ∀ {x y} → x ≤a y → IsUB _≈a_ _≤a_ ⟦ x , y ⟧ y
      isUBˡ x≤y = record
        { isSubset = isSubsetˡ
        ; isPartialOrder = isCPOˡ.isPartialOrder
        ; upperbound = λ{ (inj₁ z≈x) → isCPOˡ.≤-respˡ-≈ (isCPOˡ.Eq.sym z≈x) x≤y
                        ; (inj₂ z≈y) → isCPOˡ.reflexive z≈y }
        }

      isLUBˡ : ∀ {x y} → x ≤a y → IsLUB _≈a_ _≤a_ ⟦ x , y ⟧ y
      isLUBˡ x≤y = record
        { isUB = isUBˡ x≤y
        ; least = λ{ prf → IsUB.upperbound prf (inj₂ isCPOˡ.Eq.refl) }
        }

      isDirectedʳ : ∀ {x y} → x ≤a y → IsDirected _≈b_ _≤b_ (f $$ ⟦ x , y ⟧)
      isDirectedʳ x≤y = proj₁ (continuous (isDirectedˡ x≤y))

      f⊔P≈⊔fP : ∀ {x y} → (x≤y : x ≤a y) → f (proj₁ (isCPOˡ.complete (isDirectedˡ x≤y))) ≈b proj₁ (isCPOʳ.complete (isDirectedʳ x≤y))
      f⊔P≈⊔fP x≤y = proj₂ (continuous (isDirectedˡ x≤y))

  open IsMonotone isMonotone hiding (cong; isCPOʳ; isCPOˡ) public
