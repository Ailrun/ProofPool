module Calculus.LinearSide.Parser where

open import Data.String
open import Calculus.LinearSide.Syntax

data Type : Set where
  LBaseT : Type
  LArrT : Type → Type → Type
  LBangT : Type → Type

data Term : Set where
  LVar : String → Term
  LAbs : String → Type → Term → Term
  LApp : Term → Term → Term
  LBang : Term → Term
  LLetB : String → Term → Term → Term

{-# FOREIGN GHC import Calculus.LinearSide.Haskell.Syntax #-}
{-# COMPILE GHC Type =
  data Type ( LBaseT | LArrT | LBangT) #-}
{-# COMPILE GHC Term =
  data Term ( LVar | LAbs | LApp | LBang | LLetB) #-}
