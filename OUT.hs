{-# LANGUAGE GADTs, RankNTypes, DataKinds, PolyKinds, TypeFamilies, TypeOperators, ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, UndecidableInstances, FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell, EmptyCase, PartialTypeSignatures, NoMonomorphismRestriction, ImpredicativeTypes #-}
{-# OPTIONS_GHC -fno-max-relevant-binds #-}
{-# OPTIONS_GHC -fprint-explicit-kinds #-}
{-# OPTIONS_GHC -fwarn-unticked-promoted-constructors #-}
module OUT where

import Prelude ()
import qualified Prelude as P
import qualified Language.Haskell.TH as TH

data family Sing (k :: *) :: k -> *
type Sing' (x :: k) = Sing k x
type family FromSing (y :: Sing k x) :: k
type family ToSing (x :: k) :: Sing k x
class SingKind (k :: *) where
  fromSing :: Sing k x -> k
data SomeSing (k :: *) where SomeSing :: forall (k :: *) (x :: k). Sing k x -> SomeSing k
$(do TH.reportWarning "Typechecked Sing"; P.return [])

data instance Sing * x where
  SStar :: forall (x :: *). Sing * x
$(do TH.reportWarning "Typechecked SStar"; P.return [])

data TyFun' (a :: *) (b :: *) :: *
type TyFun (a :: *) (b :: *) = TyFun' a b -> *
type family (a :: TyFun k1 k2) @@ (b :: k1) :: k2
data TyPi' (a :: *) (b :: TyFun a *) :: *
type TyPi (a :: *) (b :: TyFun a *) = TyPi' a b -> *
type family (a :: TyPi k1 k2) @@@ (b :: k1) :: k2 @@ b
data instance Sing (TyPi k1 k2) x where
  SLambda :: (forall (t :: k1). Sing k1 t -> Sing (k2 @@ t) (f @@@ t)) -> Sing (TyPi k1 k2) f
unSLambda :: Sing (TyPi k1 k2) f -> (forall t. Sing k1 t -> Sing (k2 @@ t) (f @@@ t))
unSLambda (SLambda x) = x
$(do TH.reportWarning "Typechecked TyFun & TyPi"; P.return [])

data instance Sing (Sing k x) y where
  SSing :: forall (y :: Sing k x). Sing k x -> Sing (Sing k x) y
$(do TH.reportWarning "Typechecked SSing"; P.return [])
type instance ToSing (y :: Sing k x) = 'SSing y
type instance FromSing ('SSing y) = y
instance SingKind (Sing k x) where
  fromSing (SSing x) = x

$(P.return [])
data Nat :: * where
  O ::   Nat
  S ::   Nat -> Nat
$(P.return [])
data C (c :: TyFun' Nat *)
$(P.return [])
type instance (@@) C d = Nat
$(P.return [])
data K (e :: TyPi' Nat C)
$(P.return [])
type family D  :: TyPi Nat C where
   D  = K
$(P.return [])
aaa :: Sing' {- KIND -} D
aaa = P.undefined

$(P.return [])
data P (f :: TyPi' Nat C)
$(P.return [])
type family E  :: TyPi Nat C where
   E  = P
$(P.return [])
data G (h :: Nat) (g :: TyFun' Nat *)
$(P.return [])
type instance (@@) (G j) i = *
$(P.return [])
data L (l :: Nat) (k :: TyPi' Nat (G l))
$(P.return [])
data I (n :: Nat) (m :: TyFun' Nat *)
$(P.return [])
type instance (@@) (I p) o = Nat
$(P.return [])
data M (r :: Nat) (q :: TyPi' Nat (I r))
$(P.return [])
type instance (@@@) (L t) s = Nat
$(P.return [])
type instance (@@@) (M v) u = 'S (E @@@ u)
$(P.return [])
type family N (aa :: Nat) (z :: Nat)  :: Nat where
   N w 'O = 'O
   N y ('S x) = M y @@@ x
$(P.return [])
type instance (@@@) P ab = N ab ab
$(P.return [])
data F (ad :: Nat) (ac :: TyPi' Nat (G ad))
$(P.return [])
data H (af :: Nat) (ae :: TyPi' Nat (I af))
$(P.return [])
type instance (@@@) (F ah) ag = Nat
$(P.return [])
type instance (@@@) (H aj) ai = 'S (D @@@ ai)
$(P.return [])
type family J (ao :: Nat) (an :: Nat)  :: Nat where
   J ak 'O = 'O
   J am ('S al) = H am @@@ al
$(P.return [])
type instance (@@@) K ap = J ap ap
$(P.return [])
data instance Sing Nat ar where
  SO ::   Sing' 'O
  SS ::   forall (aq :: Nat). (Sing Nat aq) -> Sing' ('S aq)
$(P.return [])
data B (as :: TyFun' Nat *)
$(P.return [])
type instance (@@) B at = Nat
$(P.return [])
data A (au :: TyPi' Nat B)
$(P.return [])
b :: Sing' {- KIND -} A
b = SLambda (\av -> SS av)

$(P.return [])
a :: Sing' {- KIND -} 'O
a = SO

$(P.return [])
type instance (@@@) A aw = 'S aw
