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
data instance Sing Nat d where
  SO ::   Sing' 'O
  SS ::   forall (c :: Nat). (Sing Nat c) -> Sing' ('S c)
$(P.return [])
data I (e :: TyFun' Nat *)
$(P.return [])
type instance (@@) I f = Nat
$(P.return [])
data H (g :: TyPi' Nat I)
$(P.return [])
data F (i :: Nat) (h :: TyFun' Nat *)
$(P.return [])
type instance (@@) (F k) j = Nat
$(P.return [])
data J (m :: Nat) (l :: TyPi' Nat (F m))
$(P.return [])
data N (n :: TyPi' Nat I)
$(P.return [])
$(P.return [])
data D (w :: Nat) (v :: TyFun' Nat *)
$(P.return [])
type instance (@@) (D y) x = *
$(P.return [])
data K (aa :: Nat) (z :: TyPi' Nat (D aa))
$(P.return [])
data L (ac :: Nat) (ab :: TyPi' Nat (F ac))
$(P.return [])
type instance (@@@) (K ae) ad = Nat
$(P.return [])
type instance (@@@) (L ag) af = 'S ('S af)
$(P.return [])
type family M (al :: Nat) (ak :: Nat)  :: Nat where
   M ah 'O = 'S 'O
   M aj ('S ai) = L aj @@@ ai
$(P.return [])
type instance (@@@) N am = M am am
$(P.return [])
type instance (@@@) (J ao) an = 'S ('S an)
$(P.return [])
data C (aq :: Nat) (ap :: TyPi' Nat (D aq))
$(P.return [])
data E (as :: Nat) (ar :: TyPi' Nat (F as))
$(P.return [])
type instance (@@@) (C au) at = Nat
$(P.return [])
type instance (@@@) (E aw) av = 'S ('S av)
$(P.return [])
type family G (bb :: Nat) (ba :: Nat)  :: Nat where
   G ax 'O = 'S 'O
   G az ('S ay) = E az @@@ ay
$(P.return [])
type instance (@@@) H bc = G bc bc
$(P.return [])
data B (bd :: TyFun' Nat *)
$(P.return [])
type instance (@@) B be = Nat
$(P.return [])
data A (bf :: TyPi' Nat B)
$(P.return [])
b :: Sing' {- KIND -} A
b = SLambda (\bg -> SS bg)

$(P.return [])
a :: Sing' {- KIND -} 'O
a = SO

$(P.return [])
type instance (@@@) A bh = 'S bh

nS :: Sing' {- KIND -} N
nS = let { o :: Sing' N; o = SLambda (\(q :: Sing Nat p) -> case q of { SO -> b `unSLambda` a; SS r -> let { s :: Sing'
  (J p); s = SLambda (\(u :: Sing Nat t) -> b `unSLambda` (b `unSLambda` u))} in s `unSLambda` r })} in o

