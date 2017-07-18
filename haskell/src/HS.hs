module HS where

import Data.Nat
import Telescope

import Data.Foldable
import Data.Maybe
import Data.Monoid hiding (Product)
import Data.Traversable
import Data.Set (Set)

import Data.Bitraversable
import Data.GADT.Compare
import Data.Functor.Identity
import Control.Lens
import Control.Applicative

--------------------------------------------------------------------------------

-- TODO : find a better way to write this

data Sub a b where
  SLN :: Sub Z Z
  SLS :: Sub n m -> Sub n (S m)
  SLM :: Sub n m -> Sub (S n) (S m)

snList :: Sub a b -> [Fin b]
snList SLN     = []
snList (SLS s) = FS <$> snList s
snList (SLM s) = FZ : (FS <$> snList s)

snOfSub' :: Sub a b -> SN b
snOfSub' SLN = SZ
snOfSub' (SLS a) = SS (snOfSub' a)
snOfSub' (SLM a) = SS (snOfSub' a)

snOfSub :: Sub a b -> SN a
snOfSub SLN = SZ
snOfSub (SLS a) = snOfSub a
snOfSub (SLM a) = SS (snOfSub a)

subRefl :: SN a -> Sub a a
subRefl SZ     = SLN
subRefl (SS a) = SLM (subRefl a)

subTrans :: Sub a b -> Sub b c -> Sub a c
subTrans SLN     SLN     = SLN
subTrans p       (SLS q) = SLS (subTrans p q)
subTrans (SLS p) (SLM q) = SLS (subTrans p q)
subTrans (SLM p) (SLM q) = SLM (subTrans p q)

subFn :: Sub a b -> Fin a -> Fin b
subFn (SLM a) FZ     = FZ
subFn (SLM a) (FS x) = FS (subFn a x)
subFn (SLS a) x      = FS (subFn a x)

data SubMerge b1 b2 a where
  SubMerge :: Sub b1 c -> Sub b2 c -> Sub c a -> SubMerge b1 b2 a

subMerge :: Sub b1 a -> Sub b2 a -> SubMerge b1 b2 a
subMerge SLN     SLN     = SubMerge SLN SLN SLN
subMerge (SLM a) (SLM b) = case subMerge a b of
  SubMerge x y z -> SubMerge (SLM x) (SLM y) (SLM z)
subMerge (SLM a) (SLS b) = case subMerge a b of
  SubMerge x y z -> SubMerge (SLM x) (SLS y) (SLM z)
subMerge (SLS a) (SLM b) = case subMerge a b of
  SubMerge x y z -> SubMerge (SLS x) (SLM y) (SLM z)
subMerge (SLS a) (SLS b) = case subMerge a b of
  SubMerge x y z -> SubMerge x y (SLS z)

data C (f :: N -> *) (a :: N) where
  C :: Sub b a -> (forall c. Sub b c -> f c) -> C f a

data D f a where
  D :: Sub b a -> f b -> D f a

data E f b a where
  E :: Sub b c -> Sub c a -> f c -> E f b a

dOfC :: C f a -> D f a
dOfC (C a b) = D a (b (subRefl (snOfSub a)))

data L (f :: N -> *) (a :: N) = L (f (S a))
data LB (f :: N -> *) (b :: N) (a :: N) = LB (f (Plus b a))

liftC :: C f (S a) -> C (L f) a
liftC (C (SLS a) b) = C a (L . b . SLS)
liftC (C (SLM a) b) = C a (L . b . SLM)

liftBC :: SN a -> SN b -> C f (Plus b a) -> C (LB f b) a
liftBC a SZ     (C x y) = C x (LB . y)
liftBC a (SS n) c = case plusSRight n a of
  Refl -> case liftC (liftBC (SS a) n c) of
    C x y -> C x (\s -> case y s of L (LB a) -> case plusSRight n (snOfSub' s) of Refl -> LB a)

mapC :: (forall a. f a -> g a) -> C f a -> C g a
mapC f (C a b) = C a (f . b)

constC :: SN a -> (forall a. f a) -> C f a
constC n f = C (cFin' n) (const f)

data Product f g a where
  Pair :: f a -> g a -> Product f g a

data Compose f g a where
  Compose :: f (g a) -> Compose f g a

appC :: (forall a. f a -> g a -> h a) -> C f a -> C g a -> C h a
appC f (C a b) (C a' b') = case subMerge a a' of
  SubMerge x y z -> C z (\s -> f (b (subTrans x s)) (b' (subTrans y s)))

cFin' :: SN a -> Sub Z a
cFin' SZ     = SLN
cFin' (SS n) = SLS (cFin' n)

cFin :: SN a -> Fin a -> C Fin a
cFin (SS n) FZ     = C (SLM (cFin' n)) (\s -> subFn s FZ)
cFin (SS n) (FS x) = case cFin n x of
  C a b -> C (SLS a) b

dEnv :: Env n a -> C f a -> D (Product (Env n) f) a
dEnv e (C x y) = case dEnv' e x of
  E a b c -> D b (Pair c (y a))
  where dEnv' :: Env n a -> Sub b a -> E (Env n) b a
        dEnv' EnvNil         SLN     = E SLN SLN EnvNil
        dEnv' (EnvCons a as) (SLS x) = case dEnv' as x of
          E x y z -> E x (SLS y) z
        dEnv' (EnvCons a as) (SLM x) = case cType (snOfSub' x) a of
          C y z -> case subMerge y x of
            SubMerge i j k -> case dEnv' as k of
              E o n m -> E (SLM (subTrans j o)) (SLM n) (EnvCons (z (subTrans i o)) m)

cType :: SN a -> Type n a -> C (Type n) a
cType n (TVar a)    = mapC TVar (cFin n a)
cType n (TConst c)  = constC n (TConst c)
cType n TType       = constC n TType
cType n (TPi a b)   = appC TPi (cType n a) (cType n b)
cType n (TPApp a b) = appC TPApp (cType n a) (cType n b)
cType n (TCApp a b) = appC TCApp (cType n a) (cType n b)
cType n (TApp a b)  = appC TApp (cType n a) (cType n b)
cType n (TLift a)   = constC n (TLift a)
cType n TUNKNOWN    = constC n TUNKNOWN

cVec :: SN a -> Vec b (C f a) -> C (Compose (Vec b) f) a
cVec s VNil         = constC s (Compose VNil)
cVec s (VCons a as) = appC (\b (Compose bs) -> Compose (VCons b bs)) a (cVec s as)

cList :: SN a -> [C f a] -> C (Compose [] f) a
cList s []     = constC s (Compose [])
cList s (x:xs) = appC (\b (Compose bs) -> Compose (b:bs)) x (cList s xs)

cCase :: SN a -> Case n a -> C (Case n) a
cCase s (Case a b c) = let d = liftBC s b (cType (plus b s) c)
                       in mapC (\(LB x) -> Case a b x) d

--------------------------------------------------------------------------------

data Env n a where
  EnvNil  :: Env n Z
  EnvCons :: Type n a -> Env n a -> Env n (S a)

deriving instance Show n => Show (Env n a)
deriving instance Eq n => Eq (Env n a)
deriving instance Ord n => Ord (Env n a)

snOfEnv :: Env n a -> SN a
snOfEnv EnvNil         = SZ
snOfEnv (EnvCons _ xs) = SS (snOfEnv xs)

vecOfEnv :: Env n a -> Vec a (Type n a)
vecOfEnv EnvNil         = VNil
vecOfEnv (EnvCons a as) = fmap (mapType id FS) (VCons a (vecOfEnv as))

envLookup :: Fin a -> Env n a -> Type n a
envLookup FZ     (EnvCons x xs) = mapType id FS x
envLookup (FS n) (EnvCons x xs) = mapType id FS (envLookup n xs)

traverseEnv :: Applicative t => (forall a. Type n a -> t (Type m a)) -> Env n a -> t (Env m a)
traverseEnv f EnvNil         = pure EnvNil
traverseEnv f (EnvCons x xs) = EnvCons <$> f x <*> traverseEnv f xs

--------------------------------------------------------------------------------

data TTFix n a where
  TTFix :: Vec b (Type n a) -> Fin b -> TTFix n a
instance Show n => Show (TTFix n a) where
  showsPrec p (TTFix a b) = showParen (p >= 11) $ ("(TTFix " ++) . (showsPrec 11 a) . (" " ++) . (showsPrec 11 b) . (")" ++)
instance Eq n => Eq (TTFix n a) where
  TTFix a b == TTFix a' b' = undefined
instance Ord n => Ord (TTFix n a) where
  TTFix a b `compare` TTFix a' b' = case gcompare (snOfVec a) (snOfVec a') of
    GEQ -> (a, b) `compare` (a', b')
    x   -> weakenOrdering x

data Type n a where
  TVar     :: Fin a -> Type n a
  TConst   :: n -> Type n a
  TType    :: Type n a
  TPi      :: Type n a -> Type n a -> Type n a
  TFix     :: TTFix n a -> Type n a
  TPApp    :: Type n a -> Type n a -> Type n a -- f ('P :: P x)
  TCApp    :: Type n a -> Type n a -> Type n a -- f x
  TApp     :: Type n a -> Type n a -> Type n a -- f @@@ x
  TLift    :: Type n Z -> Type n a
  TUNKNOWN :: Type n a

deriving instance Show n => Show (Type n a)
deriving instance Eq n => Eq (Type n a)
deriving instance Ord n => Ord (Type n a)

deriving instance Show n => Show (Signature (Type n) a)
deriving instance Show n => Show (Constructor (Type n) a)
deriving instance Eq n => Eq (Signature (Type n) a)
deriving instance Eq n => Eq (Constructor (Type n) a)
deriving instance Ord n => Ord (Signature (Type n) a)
deriving instance Ord n => Ord (Constructor (Type n) a)

traverseType :: Applicative f => (n -> f m) -> (Fin a -> f (Fin b)) -> Type n a -> f (Type m b)
traverseType f g (TVar a)    = TVar <$> g a
traverseType f g (TConst a)  = TConst <$> f a
traverseType f g TType       = pure TType
traverseType f g (TPi a b)   = TPi <$> traverseType f g a <*> traverseType f g b
traverseType f g (TPApp a b) = TPApp <$> traverseType f g a <*> traverseType f g b
traverseType f g (TCApp a b) = TCApp <$> traverseType f g a <*> traverseType f g b
traverseType f g (TApp a b)  = TApp <$> traverseType f g a <*> traverseType f g b
traverseType f g (TLift a)   = TLift <$> traverseType f pure a
traverseType f g TUNKNOWN    = pure TUNKNOWN

mapType f g = runIdentity . traverseType (Identity . f) (Identity . g)
foldMapType f g = getConst . traverseType (Const . f) (Const . g)

--------------------------------------------------------------------------------

data Case n a where
  Case :: n -> SN m -> Type n (Plus m a) -> Case n a

deriving instance Show n => Show (Case n a)

data Name m n where
  NConst  :: m -> Name m n
  NPi     :: Env n a -> Type n a -> Type n (S a) -> Name m n
  NLam    :: Env n a -> Type n a -> Type n (S a) -> Type n (S a) -> Name m n
  NFix    :: Env n a -> Vec b (n, n, Type n a, Type n (Plus b a)) -> Fin b -> Name m n
  NFix1   :: Env n a -> Vec b (Type n a, Type n (Plus b a)) -> Fin b -> Name m n
  NFix2   :: Env n a -> Vec b (Type n a, Type n (Plus b a)) -> Fin b -> Name m n
  NCase   :: Env n a -> Type n a -> Type n (S a) -> [Case n a] -> Name m n
  NInd    :: m -> Int -> Name m n
  NICons  :: m -> Int -> Int -> Name m n
  NISCons :: m -> Int -> Int -> Name m n

instance Functor (Name m) where
  fmap = fmapDefault
instance Foldable (Name m) where
  foldMap = foldMapDefault
instance Traversable (Name m) where
  traverse f (NConst a)   = pure $ NConst a
  traverse f (NPi a b c) = NPi <$> traverseEnv (traverseType f pure) a <*> traverseType f pure b <*> traverseType f pure c
  traverse f (NLam a b c d) = NLam <$> traverseEnv (traverseType f pure) a <*> traverseType f pure b <*> traverseType f pure c <*> traverseType f pure d
  traverse f (NFix a b c) = NFix
                            <$> traverseEnv (traverseType f pure) a
                            <*> traverse (\(a, b, c, d) -> (,,,) <$> f a <*> f b <*> traverseType f pure c <*> traverseType f pure d) b
                            <*> pure c
  traverse f (NFix1 a b c) = NFix1
                             <$> traverseEnv (traverseType f pure) a
                             <*> traverse (bitraverse (traverseType f pure) (traverseType f pure)) b
                             <*> pure c
  traverse f (NFix2 a b c) = NFix2
                             <$> traverseEnv (traverseType f pure) a
                             <*> traverse (bitraverse (traverseType f pure) (traverseType f pure)) b
                             <*> pure c
  traverse f (NCase a b c d) = NCase
                               <$> traverseEnv (traverseType f pure) a
                               <*> traverseType f pure b
                               <*> traverseType f pure c
                               <*> traverse traverseCase d
    where traverseCase (Case a b c) = Case <$> f a <*> pure b <*> traverseType f pure c
  traverse f (NInd a b)   = pure $ NInd a b
  traverse f (NICons a b c) = pure $ NICons a b c
  traverse f (NISCons a b c) = pure $ NISCons a b c

newtype AName m = AName (Name m (AName m))
                deriving (Show, Eq, Ord)

instance (Show m, Show n) => Show (Name m n) where
  showsPrec p (NConst n)    = showParen (p >= 11) $ ("(NConst " ++) . (showsPrec 11 n) . (")" ++)
  showsPrec p (NPi sn n t) = showParen (p >= 11) $ ("(NPi " ++) . (showsPrec 11 sn) . (" " ++) . (showsPrec 11 n) .
                                (" " ++) . (showsPrec 11 t) . (")" ++)
  showsPrec p (NLam sn n m t) = showParen (p >= 11) $ ("(NLam " ++) . (showsPrec 11 sn) . (" " ++) . (showsPrec 11 n) .
                                (" " ++) . (showsPrec 11 m) .
                                (" " ++) . (showsPrec 11 t) . (")" ++)
  showsPrec p (NFix sn a b) = showParen (p >= 11) $ ("(NFix " ++) . (showsPrec 11 sn) . (" " ++) . (showsPrec 11 a) .
                              (" " ++) . (showsPrec 11 b) . (")" ++)
  showsPrec p (NFix1 sn a b) = showParen (p >= 11) $ ("(NFix1 " ++) . (showsPrec 11 sn) . (" " ++) . (showsPrec 11 a) .
                               (" " ++) . (showsPrec 11 b) . (")" ++)
  showsPrec p (NFix2 sn a b) = showParen (p >= 11) $ ("(NFix2 " ++) . (showsPrec 11 sn) . (" " ++) . (showsPrec 11 a) .
                               (" " ++) . (showsPrec 11 b) . (")" ++)
  showsPrec p (NCase sn a b c) = showParen (p >= 11) $ ("(NCase " ++) . (showsPrec 11 sn) . (" " ++) . (showsPrec 11 a) .
                                 (" " ++) . (showsPrec 11 b) . (" " ++) . (showsPrec 11 c) . (")" ++)
  showsPrec p (NInd n m)    = showParen (p >= 11) $ ("(NInd " ++) . (showsPrec 11 n) . (" " ++) . (showsPrec 11 m) . (")" ++)
  showsPrec p (NICons n m c) = showParen (p >= 11) $ ("(NICons " ++) . (showsPrec 11 n) . (" " ++) . (showsPrec 11 m) .
                               (" " ++) . (showsPrec 11 c) . (")" ++)
  showsPrec p (NISCons n m c) = showParen (p >= 11) $ ("(NISCons " ++) . (showsPrec 11 n) . (" " ++) . (showsPrec 11 m) .
                                (" " ++) . (showsPrec 11 c) . (")" ++)

instance (Eq n) => Eq (Case n a) where
  (==) = undefined

instance (Eq m, Eq n) => Eq (Name m n) where
  (==) = undefined

instance (Ord n) => Ord (Case n a) where
  Case a b c `compare` Case a' b' c' = case gcompare b b' of
    GEQ -> (a, b, c) `compare` (a', b', c')
    x   -> weakenOrdering x

instance (Ord m, Ord n) => Ord (Name m n) where
  NConst n `compare` NConst n' = n `compare` n'
  NConst _ `compare` _ = LT
  _ `compare` NConst _ = GT
  NPi a n t `compare` NPi a' n' t'
    | GEQ <- gcompare (snOfEnv a) (snOfEnv a') = (a, n, t) `compare` (a', n', t')
    | x <- gcompare (snOfEnv a) (snOfEnv a')   = weakenOrdering x
  NPi _ _ _ `compare` _ = LT
  _ `compare` NPi _ _ _ = GT
  NLam a n p t `compare` NLam a' n' p' t'
    | GEQ <- gcompare (snOfEnv a) (snOfEnv a') = (a, n, p, t) `compare` (a', n', p', t')
    | x <- gcompare (snOfEnv a) (snOfEnv a')   = weakenOrdering x
  NLam _ _ _ _ `compare` _ = LT
  _ `compare` NLam _ _ _ _ = GT
  NFix a b c `compare` NFix a' b' c' = case gcompare (snOfEnv a) (snOfEnv a') of
    GEQ -> case gcompare (snOfVec b) (snOfVec b') of
      GEQ -> (a, b, c) `compare` (a', b', c')
      y   -> weakenOrdering y
    x   -> weakenOrdering x
  NFix _ _ _ `compare` _ = LT
  _ `compare` NFix _ _ _ = GT
  NFix1 a b c `compare` NFix1 a' b' c' = case gcompare (snOfEnv a) (snOfEnv a') of
    GEQ -> case gcompare (snOfVec b) (snOfVec b') of
      GEQ -> (a, b, c) `compare` (a', b', c')
      y   -> weakenOrdering y
    x   -> weakenOrdering x
  NFix1 _ _ _ `compare` _ = LT
  _ `compare` NFix1 _ _ _ = GT
  NFix2 a b c `compare` NFix2 a' b' c' = case gcompare (snOfEnv a) (snOfEnv a') of
    GEQ -> case gcompare (snOfVec b) (snOfVec b') of
      GEQ -> (a, b, c) `compare` (a', b', c')
      y   -> weakenOrdering y
    x   -> weakenOrdering x
  NFix2 _ _ _ `compare` _ = LT
  _ `compare` NFix2 _ _ _ = GT
  NCase a b c d `compare` NCase a' b' c' d' = case gcompare (snOfEnv a) (snOfEnv a') of
    GEQ -> (a, b, c, d) `compare` (a', b', c', d')
    x   -> weakenOrdering x
  NCase _ _ _ _ `compare` _ = LT
  _ `compare` NCase _ _ _ _ = GT
  NInd n m `compare` NInd n' m' = (n, m) `compare` (n', m')
  NInd _ _ `compare` _ = LT
  _ `compare` NInd _ _ = GT
  NICons n m c `compare` NICons n' m' c' = (n, m, c) `compare` (n', m', c')
  NICons _ _ _ `compare` _ = LT
  _ `compare` NICons _ _ _ = GT
  NISCons n m c `compare` NISCons n' m' c' = (n, m, c) `compare` (n', m', c')
  NISCons _ _ _ `compare` _ = LT
  _ `compare` NISCons _ _ _ = GT


data Definition n where
  ConstDef :: n -> Type n Z -> Definition n
  IndDef   :: n -> Signature (Type n) Z -> [((n, n), Constructor (Type n) Z)] -> Definition n
deriving instance Show n => Show (Definition n)

traverseDefinition :: Applicative f => (n -> f m) -> Definition n -> f (Definition m)
traverseDefinition f (ConstDef n t) = ConstDef
                                      <$> f n
                                      <*> traverseType f pure t
traverseDefinition f (IndDef n s c) = IndDef
                                      <$> f n
                                      <*> traverseTelescope (traverseType f pure) (traverseType f pure) s
                                      <*> traverse (bitraverse
                                                    (bitraverse f f)
                                                    (traverseTelescope (traverseType f pure) (traverseApplication (traverseType f pure)))
                                                   ) c

type Definitions n = [Definition n]

-- type Definitions n = Set (Name n)
