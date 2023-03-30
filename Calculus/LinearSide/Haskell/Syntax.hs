module Calculus.LinearSide.Haskell.Syntax where

import Data.Text (Text)

data Type
  = LBaseT
  | LArrT Type Type
  | LBangT Type

data Term
  = LVar Text
  | LAbs Text Type Term
  | LApp Term Term
  | LBang Term
  | LLetB Text Term Term
