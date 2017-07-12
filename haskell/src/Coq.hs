module Coq where

import Data.Nat
import Telescope

data Expr n a = EVar (Fin a)
              | EConst n
              | EInd n Int
              | ECons n Int Int
              | EType
              | EApp (Expr n a) (Expr n a) (Expr n a) -- Last one = result type
              | EPi (Expr n a) (Expr n ('S a))
              | EAbs (Expr n a) (Expr n ('S a))
              | forall m. EFix (Vec m (Expr n a, Expr n (Plus m a))) (Fin m)
              | ECase (n, Int) (Expr n a) (Expr n a) [Expr n a]

deriving instance Show n => Show (Expr n a)
deriving instance Show n => Show (Signature (Expr n) a)
deriving instance Show n => Show (Constructor (Expr n) a)

data Definition n = ConstantDefinition n (Expr n 'Z)
                  | InductiveDefinition n Int (Signature (Expr n) 'Z) [(n, Constructor (Expr n) 'Z)]
                  deriving (Show)
