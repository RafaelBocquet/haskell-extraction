module Data.Sexp where

import Prelude

import Data.ByteString.Char8 as B
import Data.Attoparsec.ByteString.Char8 as A
import Control.Applicative

data Sexp = Atom String
          | Sexp [Sexp]
          deriving (Show)

sexpParser :: Parser Sexp
sexpParser = do
  skipSpace
  choice [ Sexp <$> (char '(' *> many sexpParser <* skipSpace <* char ')')
         , Atom . B.unpack <$> A.takeWhile1 (\c -> not (isSpace c || c == ')' || c == '('))
         ]

parseSexp :: ByteString -> Either String Sexp
parseSexp = A.parseOnly (sexpParser <* skipSpace <* endOfInput)
