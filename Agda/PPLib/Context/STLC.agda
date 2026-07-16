{-# OPTIONS --safe #-}
module PPLib.Context.STLC {ℓ₀} (Tp : Set ℓ₀) where

open import PPLib.Context.STLC.Base Tp       renaming (module Variables to BVariables) public
open import PPLib.Context.STLC.Properties Tp public
open import PPLib.Context.STLC.Extension Tp  renaming (module Variables to EVariables) public
