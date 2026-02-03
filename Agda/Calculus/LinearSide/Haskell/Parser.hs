{-# LANGUAGE OverloadedStrings #-}
module Calculus.LinearSide.Haskell.Parser where

import Calculus.LinearSide.Haskell.Syntax
import Control.Monad
import Data.Text (Text)
import Data.Text qualified as T
import Data.Void
import Text.Parsec

type Parser = Parsec Text ()

parseType :: Parser Type
parseType = _

parseTerm :: Parser Term
parseTerm = parseAbs <|> parseApp
  where
    parseAbs = do
      symbolLambda
      spaces
      symbolArrow
      spaces
      parseTerm

    parseApp = do
      _

parseIdent :: Parser Text
parseIdent = (T.pack .) . (:) <$> letter <*> many alphaNum

keywordLet :: Parser ()
keywordLet = string "let" >> notFollowedBy alphaNum

keywordBang :: Parser ()
keywordBang = string "bang" >> notFollowedBy alphaNum

keywordIn :: Parser ()
keywordIn = string "in" >> notFollowedBy alphaNum

symbolBase :: Parser ()
symbolBase = void $ char '#'

symbolLambda :: Parser ()
symbolLambda = void $ char '\\'

symbolArrow :: Parser ()
symbolArrow = void . try $ char '-' >> char '>'
