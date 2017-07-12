module Main where

import Extraction
import Emit
import Rename
import Coq.Parse
import HS
import Data.Nat

import Language.Haskell.Exts.Pretty
import qualified Data.ByteString as B
import System.Environment
import Control.Monad

main :: IO ()
main = do
  [f] <- getArgs
  b <- B.readFile f
  case parseCoq b >>= extract of
    Left e -> print e
    Right a -> do
      let r = prettyPrintStyleMode
              (Style PageMode 160 1.5)
              (PPHsMode 2 2 2 2 2 2 2 False PPOffsideRule False)
              (uncurry emit (rename a))
      putStrLn r
      writeFile "OUT.hs" r
