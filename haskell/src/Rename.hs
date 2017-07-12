module Rename where

import qualified HS as H
import Telescope
import Data.Nat

import Data.Maybe

import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

import Data.Bitraversable

import Control.Lens
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Reader

import Debug.Trace

rename :: H.Definitions (H.AName String) -> ([(String, H.Name String String)], H.Definitions String)
rename ds =
  let (x, y) = runWriter $ forM ds (H.traverseDefinition renameAName)
      y'   = zipWith (\a b -> (b, "N" ++ show a)) [0..] $ S.toList y
      y''  = M.fromList y'
      y''' = fmap (\(H.AName a, s) -> (s, fmap (fromJust . flip M.lookup y'') a)) y'
      renameAName x@(H.AName a) = do
        forM_ a renameAName
        tell (S.singleton x)
        pure (fromJust (M.lookup x y''))
  in (y''', x)
