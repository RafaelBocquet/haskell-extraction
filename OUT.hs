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
  O ::   forall. Nat
  S ::   forall. Nat -> Nat
$(P.return [])
data instance Sing Nat b where
  SO ::   forall. Sing' 'O
  SS ::   forall (a :: Nat). Sing Nat a -> Sing' ('S a)
$(P.return [])
data N (d :: Nat) (c :: TyFun' Nat *)
$(P.return [])
type instance (@@) (N f) e = Nat
$(P.return [])
data M (h :: Nat) (g :: TyPi' Nat (N h))
$(P.return [])
data R (i :: TyFun' Nat *)
$(P.return [])
type instance (@@) R j = Nat
$(P.return [])
data Q (k :: TyPi' Nat R)

$(P.return [])
data L (t :: Nat) (s :: TyFun' Nat *)
$(P.return [])
type instance (@@) (L v) u = *
$(P.return [])
data K (x :: Nat) (w :: TyPi' Nat (L x))
$(P.return [])
type instance (@@@) (K z) y = Nat
$(P.return [])
type instance (@@@) (M ab) aa = 'S ('S aa)
$(P.return [])
type family P (ag :: Nat) (af :: Nat)  :: Nat where
   P ac 'O = 'S 'O
   P ae ('S ad) = M ae @@@ ad
$(P.return [])
type instance (@@@) Q ah = P ah ah
$(P.return [])
data J (ai :: TyFun' * *)
$(P.return [])
type instance (@@) J aj = *
$(P.return [])
data H (ak :: TyPi' * J)
$(P.return [])
not :: Sing' H
not = let { al :: Sing' H; al = SLambda (\(an :: Sing * am) -> SStar)} in al

$(P.return [])
data G (ap :: *) (ao :: TyFun' ap *)
$(P.return [])
data False :: * where
  
$(P.return [])
type instance (@@) (G ar) aq = False
$(P.return [])
type instance (@@@) H as = TyPi as (G as)
$(P.return [])
data C (au :: *) (at :: TyFun' au *)
$(P.return [])
type instance (@@) (C aw) av = aw
$(P.return [])
data D (ay :: *) (ax :: TyPi' ay (C ay))
$(P.return [])
data F (az :: TyFun' * *)
$(P.return [])
type instance (@@) F ba = TyPi ba (C ba)
$(P.return [])
data E (bb :: TyPi' * F)

$(P.return [])
type instance (@@@) E bi = D bi
$(P.return [])
type instance (@@@) (D bk) bj = bj
$(P.return [])
data Bool :: * where
  True ::   forall. Bool
  False ::   forall. Bool
$(P.return [])
data instance Sing Bool bl where
  STrue ::   forall. Sing' 'True
  SFalse ::   forall. Sing' 'False
$(P.return [])
data B (bm :: TyFun' Nat *)
$(P.return [])
type instance (@@) B bn = Nat
$(P.return [])
data A (bo :: TyPi' Nat B)
$(P.return [])
type instance (@@@) A bp = 'S bp
$(P.return [])
data instance Sing False bq where

$(P.return [])
data True :: * where
  I ::   forall. True
$(P.return [])
data instance Sing True br where
  SI ::   forall. Sing' 'I

$(P.return [])
p1 :: Sing' Q
p1 = let { l :: Sing' Q; l = SLambda (\(n :: Sing Nat m) -> case n of { SO -> SS SO; SS o -> let { p :: Sing' (M m); p
  = SLambda (\(r :: Sing Nat q) -> SS (SS r))} in p `unSLambda` o })} in l

$(P.return [])
id :: Sing' E
id = let { bc :: Sing' E; bc = SLambda (\(be :: Sing * bd) -> let { bf :: Sing' (D bd); bf = SLambda (\(bh :: Sing bd
  bg) -> bh)} in bf)} in bc
