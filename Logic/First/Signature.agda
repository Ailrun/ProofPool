module Logic.First.Signature where

open import Logic.Base public

record Signature₁ : Set₁ where
  infix 4 _returns₁ₜ_
  field
    TmConst₁ TmTy₁ TmPred₁ : Set
    _returns₁ₜ_ : TmConst₁ → TmTy₁ → Set
    cargs₁ₜ : TmConst₁ → List TmTy₁
    pargs₁ₜ : TmPred₁ → List TmTy₁
