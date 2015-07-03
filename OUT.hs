{-# LANGUAGE GADTs, RankNTypes, DataKinds, PolyKinds, TypeFamilies, TypeOperators, ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, UndecidableInstances, FlexibleContexts, StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell, EmptyCase, PartialTypeSignatures, NoMonomorphismRestriction, ImpredicativeTypes #-}
{-# OPTIONS_GHC -fno-max-relevant-binds #-}
{-# OPTIONS_GHC -fprint-explicit-kinds #-}
{-# OPTIONS_GHC -fwarn-unticked-promoted-constructors #-}
module Main where

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
deriving instance P.Show (Sing Nat x)
$(P.return [])
data G (e :: Nat) (d :: Nat) (c :: TyFun' Nat *)
$(P.return [])
type instance (@@) (G h g) f = Nat
$(P.return [])
data F (k :: Nat) (j :: Nat) (i :: TyPi' Nat (G k j))
$(P.return [])
data A (m :: Nat) (l :: TyFun' Nat *)
$(P.return [])
type instance (@@) (A o) n = Nat
$(P.return [])
data I (q :: Nat) (p :: TyPi' Nat (A q))
$(P.return [])
data B (r :: TyFun' Nat *)
$(P.return [])
type instance (@@) B s = TyPi Nat (A s)
$(P.return [])
data J (t :: TyPi' Nat B)
$(P.return [])
type family C  :: TyPi Nat B where
   C  = J
$(P.return [])
data M (ah :: Nat) (ag :: Nat) (af :: TyPi' Nat (G ah ag))
$(P.return [])
data P (aj :: Nat) (ai :: TyPi' Nat (A aj))
$(P.return [])
data Q (ak :: TyPi' Nat B)
$(P.return [])
type family K  :: TyPi Nat B where
   K  = Q
$(P.return [])
type instance (@@@) Q aw = P aw
$(P.return [])
data E (az :: Nat) (ay :: Nat) (ax :: TyFun' Nat *)
$(P.return [])
type instance (@@) (E bc bb) ba = *
$(P.return [])
data L (bf :: Nat) (be :: Nat) (bd :: TyPi' Nat (E bf be))
$(P.return [])
type instance (@@@) (L bi bh) bg = Nat
$(P.return [])
type instance (@@@) (M bl bk) bj = C @@@ bk @@@ (K @@@ bj @@@ bk)
$(P.return [])
type family N (bt :: Nat) (bs :: Nat) (br :: Nat)  :: Nat where
   N bn bm 'O = 'O
   N bq bp ('S bo) = M bq bp @@@ bo
$(P.return [])
type instance (@@@) (P bv) bu = N bv bu bv
$(P.return [])
type instance (@@@) J bw = I bw
$(P.return [])
data D (bz :: Nat) (by :: Nat) (bx :: TyPi' Nat (E bz by))
$(P.return [])
type instance (@@@) (D cc cb) ca = Nat
$(P.return [])
type instance (@@@) (F cf ce) cd = 'S (C @@@ cd @@@ ce)
$(P.return [])
type family H (cn :: Nat) (cm :: Nat) (cl :: Nat)  :: Nat where
   H ch cg 'O = cg
   H ck cj ('S ci) = F ck cj @@@ ci
$(P.return [])
type instance (@@@) (I cp) co = H cp co cp

$(P.return [])
add :: Sing' C
add = let { u = let { v :: Sing' J; v = SLambda (\(x :: Sing Nat w) -> let { y :: Sing' (I w); y = SLambda (\(aa ::
  Sing Nat z) -> case x of { SO -> aa; SS ab -> let { ac :: Sing' (F w z); ac = SLambda (\(ae :: Sing Nat ad) -> SS (u
  `unSLambda` ae `unSLambda` aa))} in ac `unSLambda` ab })} in y)} in v; } in u

$(P.return [])
-- without the assertion on line 1024 of compiler/types/Coercion.hs
mul :: Sing' K
mul = let { am :: Sing' Q
          ; am = SLambda (\(ao :: Sing Nat an) ->
                            let { ap :: Sing' (P an)
                                ; ap = SLambda (\(ar :: Sing Nat aq) ->
                                                  case ao of { SO -> SO
                                                             ; SS as -> let { at :: Sing' (M an aq)
                                                                            ; at = SLambda (\(av :: Sing Nat au) ->
                                                                                              add `unSLambda` ar `unSLambda` (mul `unSLambda` av `unSLambda` ar)
                                                                                           )
                                                                            } in at `unSLambda` as
                                                             }
                                               )
                                } in ap
                         )
          } in am

six = SS (SS (SS (SS (SS (SS SO)))))
twelve = add `unSLambda` six `unSLambda` six
main = P.print (mul `unSLambda` twelve `unSLambda` twelve)
