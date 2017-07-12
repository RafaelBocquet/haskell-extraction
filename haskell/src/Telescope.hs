module Telescope where

import Data.Nat

data Telescope f g a where
  TEmpty :: g a -> Telescope f g a
  TNext  :: f a -> Telescope f g ('S a) -> Telescope f g a

traverseTelescope :: Applicative m => (forall a. f a -> m (f' a)) -> (forall a. g a -> m (g' a)) -> Telescope f g a -> m (Telescope f' g' a)
traverseTelescope f g (TEmpty a) = TEmpty <$> g a
traverseTelescope f g (TNext a b) = TNext <$> f a <*> traverseTelescope f g b

telescopeLength :: Telescope f g a -> Int
telescopeLength (TEmpty _)  = 0
telescopeLength (TNext _ a) = 1 + telescopeLength a

data Application f a = Application (f a) [f a]
                     deriving (Show, Eq, Ord)

traverseApplication :: Applicative m => (f a -> m (f' b)) -> Application f a -> m (Application f' b)
traverseApplication f (Application a b) = Application <$> f a <*> traverse f b

type Signature f a = Telescope f f a
type Constructor f a = Telescope f (Application f) a
