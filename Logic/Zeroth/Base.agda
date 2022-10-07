module Logic.Zeroth.Base where

open import Data.Empty public
open import Data.List hiding ([_]; map; zip) public
open import Data.List.Properties public
open import Data.List.Relation.Unary.Any using (here; there) public
open import Data.List.Membership.Propositional hiding (_─_) public
open import Data.List.Membership.Propositional.Properties public
open import Data.Nat public
open import Data.Nat.Induction public
open import Data.Nat.Properties public
open import Data.Product hiding (assocʳ; assocˡ; map; map₁; map₂; swap; zip) public
open import Data.Product.Relation.Binary.Lex.Strict
open import Data.Sum hiding (assocʳ; assocˡ; map; map₁; map₂; swap) public
open import Function.Base public
open import Induction.WellFounded
open import Level renaming (_⊔_ to _l⊔_; suc to lsuc; zero to lzero) public
open import Relation.Binary.Construct.On
open import Relation.Binary.Core public
open import Relation.Binary.PropositionalEquality using (_≡_; cong; cong₂; refl; subst; trans) public

module WfLex = Data.Product.Relation.Binary.Lex.Strict
module Wf = Induction.WellFounded
module On = Relation.Binary.Construct.On

private
  variable
    a b c p q r ℓ : Level
    A : Set a
    B : Set b
    C : Set c
    x y z : A
    xs ys zs : List A

∈-++-++ : ∀ xs {ys} zs → x ∈ xs ++ ys → x ∈ xs ++ zs ++ ys
∈-++-++ xs zs x∈
  with ∈-++⁻ xs x∈
...  | inj₁ x∈xs = ∈-++⁺ˡ x∈xs
...  | inj₂ x∈ys = ∈-++⁺ʳ xs (∈-++⁺ʳ zs x∈ys)

∈-++-∷ : ∀ xs {ys} y → x ∈ xs ++ ys → x ∈ xs ++ y ∷ ys
∈-++-∷ xs _ = ∈-++-++ xs (_ ∷ [])

∈-++-dedupe₁ : ∀ xs {ys} {y} → x ∈ xs ++ y ∷ y ∷ ys → x ∈ xs ++ y ∷ ys
∈-++-dedupe₁ xs x∈
  with ∈-++⁻ xs x∈
...  | inj₁ x∈xs = ∈-++⁺ˡ x∈xs
...  | inj₂ (here refl) = ∈-++⁺ʳ xs (here refl)
...  | inj₂ (there (here refl)) = ∈-++⁺ʳ xs (here refl)
...  | inj₂ (there (there x∈ys)) = ∈-++⁺ʳ xs (there x∈ys)

∈-++-swap : ∀ xs {ys} {y} {z} → x ∈ xs ++ y ∷ z ∷ ys → x ∈ xs ++ z ∷ y ∷ ys
∈-++-swap xs x∈
  with ∈-++⁻ xs x∈
...  | inj₁ x∈xs = ∈-++⁺ˡ x∈xs
...  | inj₂ (here refl) = ∈-++⁺ʳ xs (there (here refl))
...  | inj₂ (there (here refl)) = ∈-++⁺ʳ xs (here refl)
...  | inj₂ (there (there x∈ys)) = ∈-++⁺ʳ xs (there (there x∈ys))

∈⇒∈-ext : (∀ {x} → x ∈ xs → x ∈ ys) → ∀ {x} → x ∈ y ∷ xs → x ∈ y ∷ ys
∈⇒∈-ext f (here refl) = here refl
∈⇒∈-ext f (there x∈)  = there (f x∈)
