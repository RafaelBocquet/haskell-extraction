module Data.Nat where

import Control.Lens
import Data.GADT.Compare
import Data.Type.Equality

data N = Z | S N

type family Plus (a :: N) (b :: N) :: N where
  Plus Z     b = b
  Plus (S a) b = S (Plus a b)

plus :: SN a -> SN b -> SN (Plus a b)
plus SZ     b = b
plus (SS a) b = SS (plus a b)

plusSRight :: SN a -> SN b -> (Plus a (S b) :~: Plus (S a) b)
plusSRight SZ     _ = Refl
plusSRight (SS a) b = case plusSRight a b of Refl -> Refl

plusComm :: SN a -> SN b -> (Plus a b :~: Plus b a)
plusComm SZ     SZ     = Refl
plusComm SZ     (SS a) = case plusComm SZ a of Refl -> Refl
plusComm (SS a) SZ     = case plusComm a SZ of Refl -> Refl
plusComm (SS a) (SS b) = case (plusComm a b, plusSRight a b, plusSRight b a) of
  (Refl, Refl, Refl) -> Refl

data SN :: N -> * where
  SZ :: SN 'Z
  SS :: SN n -> SN ('S n)

deriving instance Show (SN a)
deriving instance Eq (SN a)
deriving instance Ord (SN a)

instance GEq SN where
  geq SZ SZ = Just Refl
  geq (SS a) (SS b) = case geq a b of
    Just Refl -> Just Refl
    Nothing   -> Nothing
  geq _ _ = Nothing

instance GCompare SN where
  gcompare SZ     SZ     = GEQ
  gcompare (SS a) (SS b) = case gcompare a b of
    GLT -> GLT
    GEQ -> GEQ
    GGT -> GGT
  gcompare SZ    (SS _)  = GLT
  gcompare (SS _) SZ     = GGT

data ESN = forall n. ESN (SN n)

esnOfInt :: Int -> ESN
esnOfInt 0 = ESN SZ
esnOfInt n = case esnOfInt (n-1) of ESN m -> ESN (SS m)

data Fin :: N -> * where
  FZ :: Fin ('S n)
  FS :: Fin n -> Fin ('S n)

deriving instance Eq (Fin n)
deriving instance Ord (Fin n)

intOfFin :: Fin n -> Int
intOfFin FZ     = 0
intOfFin (FS n) = 1 + intOfFin n

allFins :: SN n -> Vec n (Fin n)
allFins SZ     = VNil
allFins (SS n) = VCons FZ (FS <$> allFins n)

liftFinBy :: SN m -> Fin n -> Fin (Plus m n)
liftFinBy SZ     a = a
liftFinBy (SS n) a = FS (liftFinBy n a)

instance Show (Fin n) where
  show = show . intOfFin

data Vec :: N -> * -> * where
  VNil :: Vec 'Z a
  VCons :: a -> Vec n a -> Vec ('S n) a

snocVec :: a -> Vec n a -> Vec ('S n) a
snocVec a VNil = VCons a VNil
snocVec a (VCons x xs) = VCons x (snocVec a xs)

reverseVec :: Vec n a -> Vec n a
reverseVec VNil = VNil
reverseVec (VCons x xs) = snocVec x (reverseVec xs)

snOfVec :: Vec n a -> SN n
snOfVec VNil         = SZ
snOfVec (VCons _ xs) = SS (snOfVec xs)

data EVec a where
  EVec :: Vec n a -> EVec a

vecOfList :: [a] -> EVec a
vecOfList []     = EVec VNil
vecOfList (x:xs) = case vecOfList xs of
  EVec ys -> EVec (VCons x ys)

deriving instance Show a => Show (Vec n a)
deriving instance Eq a => Eq (Vec n a)
deriving instance Ord a => Ord (Vec n a)

deriving instance Functor (Vec n)
deriving instance Foldable (Vec n)
deriving instance Traversable (Vec n)
instance Applicative (Vec n) where
  pure = error "no pure instance for Vec"
  VNil <*> VNil = VNil
  VCons f fs <*> VCons a as = VCons (f a) (fs <*> as)

instance {-# OVERLAPPING #-} Monoid a => Monoid (SN n -> Vec n a) where
  mempty SZ     = VNil
  mempty (SS n) = VCons mempty (mempty n)
  f `mappend` g = \x -> mappend' (f x) (g x)
    where mappend' :: Monoid a => Vec n a -> Vec n a -> Vec n a
          mappend' VNil          VNil        = VNil
          mappend' (VCons a as) (VCons b bs) = VCons (mappend a b) (mappend' as bs)

type instance Index (Vec n a) = Fin n
type instance IxValue (Vec n a) = a

instance Ixed (Vec n a) where
  ix FZ     f (VCons a as) = VCons <$> f a <*> pure as
  ix (FS x) f (VCons a as) = VCons a <$> ix x f as

instance FunctorWithIndex (Fin n) (Vec n) where
  imap f VNil = VNil
  imap f (VCons x xs) = VCons (f FZ x) (imap (f . FS) xs)

instance FoldableWithIndex (Fin n) (Vec n) where
  ifoldMap f VNil = mempty
  ifoldMap f (VCons x xs) = f FZ x `mappend` ifoldMap (f . FS) xs

instance TraversableWithIndex (Fin n) (Vec n) where
  itraverse f VNil         = pure VNil
  itraverse f (VCons x xs) = VCons <$> (f FZ x) <*> itraverse (f . FS) xs

lookupVec :: Vec n a -> Fin n -> a
lookupVec (VCons a as) FZ = a
lookupVec (VCons a as) (FS n) = lookupVec as n

takeVec :: SN n -> SN m -> Vec (Plus m n) a -> Vec m a
takeVec n SZ     v            = VNil
takeVec n (SS m) (VCons a as) = VCons a (takeVec n m as)
