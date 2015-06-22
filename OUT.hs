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

data Nat :: * where
  O ::   Nat
  S ::   Nat -> Nat
data T (c :: Nat) :: * where
  F1 ::   forall (a :: Nat). (Sing Nat a) -> T ('S a)
  FS ::   forall (b :: Nat). (Sing Nat b) -> (T b) -> T ('S b)
data CW (d :: TyFun' Nat *)
$(P.return [])
type instance (@@) CW e = *
$(P.return [])
data CV (f :: TyPi' Nat CW)
$(P.return [])
type instance (@@@) CV g = T g
$(P.return [])
data instance Sing (T n) m where
  SF1 ::   forall (h :: Nat) (i :: Sing Nat h). (Sing Nat h) -> Sing' ('F1 i)
  SFS ::   forall (j :: Nat) (k :: Sing Nat j) (l :: CV @@@ j). (Sing Nat j) -> (Sing (CV @@@ j) l) -> Sing' ('FS k l)
$(P.return [])
data Sumor (u :: *) (v :: *) :: * where
  Inleft ::   forall (o :: *) (p :: *) (q :: o). (Sing * o) -> (Sing * p) -> (Sing o q) -> Sumor o p
  Inright ::   forall (r :: *) (s :: *) (t :: s). (Sing * r) -> (Sing * s) -> (Sing s t) -> Sumor r s
data instance Sing (Sumor aj ak) ai where
  SInleft ::
    forall (w :: *) (x :: *) (y :: w) (z :: Sing * w) (aa :: Sing * x) (ab :: Sing w y). (Sing * w) -> (Sing * x) ->
    (Sing w y) -> Sing' ('Inleft z aa ab)
  SInright ::
    forall (ac :: *) (ad :: *) (ae :: ad) (af :: Sing * ac) (ag :: Sing * ad) (ah :: Sing ad ae). (Sing * ac) -> (Sing
    * ad) -> (Sing ad ae) -> Sing' ('Inright af ag ah)
$(P.return [])
data CS (al :: TyFun' * *)
$(P.return [])
data CU (an :: *) (am :: TyFun' * *)
$(P.return [])
type instance (@@) (CU ap) ao = *
$(P.return [])
type instance (@@) CS aq = TyPi * (CU aq)
$(P.return [])
data CR (ar :: TyPi' * CS)
$(P.return [])
data CT (at :: *) (as :: TyPi' * (CU at))
$(P.return [])
type instance (@@@) CR au = CT au
$(P.return [])
type instance (@@@) (CT aw) av = Sumor aw av
$(P.return [])
data Sumbool (bd :: *) (be :: *) :: * where
  Left ::   forall (ax :: *) (ay :: *) (az :: ax). (Sing * ax) -> (Sing * ay) -> (Sing ax az) -> Sumbool ax ay
  Right ::   forall (ba :: *) (bb :: *) (bc :: bb). (Sing * ba) -> (Sing * bb) -> (Sing bb bc) -> Sumbool ba bb
data instance Sing (Sumbool bs bt) br where
  SLeft ::
    forall (bf :: *) (bg :: *) (bh :: bf) (bi :: Sing * bf) (bj :: Sing * bg) (bk :: Sing bf bh). (Sing * bf) -> (Sing
    * bg) -> (Sing bf bh) -> Sing' ('Left bi bj bk)
  SRight ::
    forall (bl :: *) (bm :: *) (bn :: bm) (bo :: Sing * bl) (bp :: Sing * bm) (bq :: Sing bm bn). (Sing * bl) -> (Sing
    * bm) -> (Sing bm bn) -> Sing' ('Right bo bp bq)
$(P.return [])
data CO (bu :: TyFun' * *)
$(P.return [])
data CQ (bw :: *) (bv :: TyFun' * *)
$(P.return [])
type instance (@@) (CQ by) bx = *
$(P.return [])
type instance (@@) CO bz = TyPi * (CQ bz)
$(P.return [])
data CN (ca :: TyPi' * CO)
$(P.return [])
data CP (cc :: *) (cb :: TyPi' * (CQ cc))
$(P.return [])
type instance (@@@) CN cd = CP cd
$(P.return [])
type instance (@@@) (CP cf) ce = Sumbool cf ce
$(P.return [])
data I (ch :: *) (cg :: TyFun' ch *)
$(P.return [])
type instance (@@) (I cj) ci = *
$(P.return [])
data N (cm :: *) (cl :: TyPi cm (I cm)) (ck :: TyFun' cm *)
$(P.return [])
type instance (@@) (N cp co) cn = *
$(P.return [])
data SigT2 (cw :: *) (cx :: TyPi cw (I cw)) (cy :: TyPi cw (N cw cx)) :: * where
  ExistT2 ::
    forall (cq :: *) (cr :: TyPi cq (I cq)) (cs :: TyPi cq (N cq cr)) (ct :: cq) (cu :: cr @@@ ct) (cv :: cs @@@ ct).
    (Sing * cq) -> (Sing (TyPi cq (I cq)) cr) -> (Sing (TyPi cq (N cq cr)) cs) -> (Sing cq ct) -> (Sing (cr @@@ ct) cu)
    -> (Sing (cs @@@ ct) cv) -> SigT2 cq cr cs
data instance Sing (SigT2 dm dn dp) dl where
  SExistT2 ::
    forall (cz :: *) (da :: TyPi cz (I cz)) (db :: TyPi cz (N cz da)) (dc :: cz) (dd :: da @@@ dc) (de :: db @@@ dc)
    (df :: Sing * cz) (dg :: Sing (TyPi cz (I cz)) da) (dh :: Sing (TyPi cz (N cz da)) db) (di :: Sing cz dc) (dj ::
    Sing (da @@@ dc) dd) (dk :: Sing (db @@@ dc) de). (Sing * cz) -> (Sing (TyPi cz (I cz)) da) -> (Sing (TyPi cz (N cz
    da)) db) -> (Sing cz dc) -> (Sing (da @@@ dc) dd) -> (Sing (db @@@ dc) de) -> Sing' ('ExistT2 df dg dh di dj dk)
$(P.return [])
data CI (dq :: TyFun' * *)
$(P.return [])
data CK (ds :: *) (dr :: TyFun' (TyPi ds (I ds)) *)
$(P.return [])
data CM (dv :: *) (du :: TyPi dv (I dv)) (dt :: TyFun' (TyPi dv (N dv du)) *)
$(P.return [])
type instance (@@) (CM dy dx) dw = *
$(P.return [])
type instance (@@) (CK ea) dz = TyPi (TyPi ea (N ea dz)) (CM ea dz)
$(P.return [])
type instance (@@) CI eb = TyPi (TyPi eb (I eb)) (CK eb)
$(P.return [])
data CH (ec :: TyPi' * CI)
$(P.return [])
data CJ (ee :: *) (ed :: TyPi' (TyPi ee (I ee)) (CK ee))
$(P.return [])
type instance (@@@) CH ef = CJ ef
$(P.return [])
data CL (ei :: *) (eh :: TyPi ei (I ei)) (eg :: TyPi' (TyPi ei (N ei eh)) (CM ei eh))
$(P.return [])
type instance (@@@) (CJ ek) ej = CL ek ej
$(P.return [])
type instance (@@@) (CL en em) el = SigT2 en em el
$(P.return [])
data SigT (es :: *) (et :: TyPi es (I es)) :: * where
  ExistT ::
    forall (eo :: *) (ep :: TyPi eo (I eo)) (eq :: eo) (er :: ep @@@ eq). (Sing * eo) -> (Sing (TyPi eo (I eo)) ep) ->
    (Sing eo eq) -> (Sing (ep @@@ eq) er) -> SigT eo ep
data instance Sing (SigT fd fe) fc where
  SExistT ::
    forall (eu :: *) (ev :: TyPi eu (I eu)) (ew :: eu) (ex :: ev @@@ ew) (ey :: Sing * eu) (ez :: Sing (TyPi eu (I eu))
    ev) (fa :: Sing eu ew) (fb :: Sing (ev @@@ ew) ex). (Sing * eu) -> (Sing (TyPi eu (I eu)) ev) -> (Sing eu ew) ->
    (Sing (ev @@@ ew) ex) -> Sing' ('ExistT ey ez fa fb)
$(P.return [])
data CE (ff :: TyFun' * *)
$(P.return [])
data CG (fh :: *) (fg :: TyFun' (TyPi fh (I fh)) *)
$(P.return [])
type instance (@@) (CG fj) fi = *
$(P.return [])
type instance (@@) CE fk = TyPi (TyPi fk (I fk)) (CG fk)
$(P.return [])
data CD (fl :: TyPi' * CE)
$(P.return [])
data CF (fn :: *) (fm :: TyPi' (TyPi fn (I fn)) (CG fn))
$(P.return [])
type instance (@@@) CD fo = CF fo
$(P.return [])
type instance (@@@) (CF fq) fp = SigT fq fp
$(P.return [])
data Sig2 (fx :: *) (fy :: TyPi fx (I fx)) (fz :: TyPi fx (N fx fy)) :: * where
  Exist2 ::
    forall (fr :: *) (fs :: TyPi fr (I fr)) (ft :: TyPi fr (N fr fs)) (fu :: fr) (fv :: fs @@@ fu) (fw :: ft @@@ fu).
    (Sing * fr) -> (Sing (TyPi fr (I fr)) fs) -> (Sing (TyPi fr (N fr fs)) ft) -> (Sing fr fu) -> (Sing (fs @@@ fu) fv)
    -> (Sing (ft @@@ fu) fw) -> Sig2 fr fs ft
data instance Sing (Sig2 gn go gp) gm where
  SExist2 ::
    forall (ga :: *) (gb :: TyPi ga (I ga)) (gc :: TyPi ga (N ga gb)) (gd :: ga) (ge :: gb @@@ gd) (gf :: gc @@@ gd)
    (gg :: Sing * ga) (gh :: Sing (TyPi ga (I ga)) gb) (gi :: Sing (TyPi ga (N ga gb)) gc) (gj :: Sing ga gd) (gk ::
    Sing (gb @@@ gd) ge) (gl :: Sing (gc @@@ gd) gf). (Sing * ga) -> (Sing (TyPi ga (I ga)) gb) -> (Sing (TyPi ga (N ga
    gb)) gc) -> (Sing ga gd) -> (Sing (gb @@@ gd) ge) -> (Sing (gc @@@ gd) gf) -> Sing' ('Exist2 gg gh gi gj gk gl)
$(P.return [])
data BY (gq :: TyFun' * *)
$(P.return [])
data CA (gs :: *) (gr :: TyFun' (TyPi gs (I gs)) *)
$(P.return [])
data CC (gv :: *) (gu :: TyPi gv (I gv)) (gt :: TyFun' (TyPi gv (N gv gu)) *)
$(P.return [])
type instance (@@) (CC gy gx) gw = *
$(P.return [])
type instance (@@) (CA ha) gz = TyPi (TyPi ha (N ha gz)) (CC ha gz)
$(P.return [])
type instance (@@) BY hb = TyPi (TyPi hb (I hb)) (CA hb)
$(P.return [])
data BX (hc :: TyPi' * BY)
$(P.return [])
data BZ (he :: *) (hd :: TyPi' (TyPi he (I he)) (CA he))
$(P.return [])
type instance (@@@) BX hf = BZ hf
$(P.return [])
data CB (hi :: *) (hh :: TyPi hi (I hi)) (hg :: TyPi' (TyPi hi (N hi hh)) (CC hi hh))
$(P.return [])
type instance (@@@) (BZ hk) hj = CB hk hj
$(P.return [])
type instance (@@@) (CB hn hm) hl = Sig2 hn hm hl
$(P.return [])
data Sig (hs :: *) (ht :: TyPi hs (I hs)) :: * where
  Exist ::
    forall (ho :: *) (hp :: TyPi ho (I ho)) (hq :: ho) (hr :: hp @@@ hq). (Sing * ho) -> (Sing (TyPi ho (I ho)) hp) ->
    (Sing ho hq) -> (Sing (hp @@@ hq) hr) -> Sig ho hp
data instance Sing (Sig id ie) ic where
  SExist ::
    forall (hu :: *) (hv :: TyPi hu (I hu)) (hw :: hu) (hx :: hv @@@ hw) (hy :: Sing * hu) (hz :: Sing (TyPi hu (I hu))
    hv) (ia :: Sing hu hw) (ib :: Sing (hv @@@ hw) hx). (Sing * hu) -> (Sing (TyPi hu (I hu)) hv) -> (Sing hu hw) ->
    (Sing (hv @@@ hw) hx) -> Sing' ('Exist hy hz ia ib)
$(P.return [])
data BU (ig :: TyFun' * *)
$(P.return [])
data BW (ii :: *) (ih :: TyFun' (TyPi ii (I ii)) *)
$(P.return [])
type instance (@@) (BW ik) ij = *
$(P.return [])
type instance (@@) BU il = TyPi (TyPi il (I il)) (BW il)
$(P.return [])
data BT (im :: TyPi' * BU)
$(P.return [])
data BV (ip :: *) (io :: TyPi' (TyPi ip (I ip)) (BW ip))
$(P.return [])
type instance (@@@) BT iq = BV iq
$(P.return [])
type instance (@@@) (BV is) ir = Sig is ir
$(P.return [])
data Identity (iv :: *) (iw :: iv) (ix :: iv) :: * where
  Identity_refl ::   forall (it :: *) (iu :: it). (Sing * it) -> (Sing it iu) -> Identity it iu iu
data instance Sing (Identity jd je jf) jc where
  SIdentity_refl ::
    forall (iy :: *) (iz :: iy) (ja :: Sing * iy) (jb :: Sing iy iz). (Sing * iy) -> (Sing iy iz) -> Sing'
    ('Identity_refl ja jb)
$(P.return [])
data BO (jg :: TyFun' * *)
$(P.return [])
data BQ (ji :: *) (jh :: TyFun' ji *)
$(P.return [])
data BS (jl :: *) (jk :: jl) (jj :: TyFun' jl *)
$(P.return [])
type instance (@@) (BS jo jn) jm = *
$(P.return [])
type instance (@@) (BQ jq) jp = TyPi jq (BS jq jp)
$(P.return [])
type instance (@@) BO jr = TyPi jr (BQ jr)
$(P.return [])
data BN (js :: TyPi' * BO)
$(P.return [])
data BP (ju :: *) (jt :: TyPi' ju (BQ ju))
$(P.return [])
type instance (@@@) BN jv = BP jv
$(P.return [])
data BR (jy :: *) (jx :: jy) (jw :: TyPi' jy (BS jy jx))
$(P.return [])
type instance (@@@) (BP ka) jz = BR ka jz
$(P.return [])
type instance (@@@) (BR kd kc) kb = Identity kd kc kb
$(P.return [])
data Comparison :: * where
  Eq ::   Comparison
  Lt ::   Comparison
  Gt ::   Comparison
data CompareSpecT (kq :: *) (kr :: *) (ks :: *) (kt :: Comparison) :: * where
  CompEqT ::
    forall (ke :: *) (kf :: *) (kg :: *) (kh :: ke). (Sing * ke) -> (Sing * kf) -> (Sing * kg) -> (Sing ke kh) ->
    CompareSpecT ke kf kg 'Eq
  CompLtT ::
    forall (ki :: *) (kj :: *) (kk :: *) (kl :: kj). (Sing * ki) -> (Sing * kj) -> (Sing * kk) -> (Sing kj kl) ->
    CompareSpecT ki kj kk 'Lt
  CompGtT ::
    forall (km :: *) (kn :: *) (ko :: *) (kp :: ko). (Sing * km) -> (Sing * kn) -> (Sing * ko) -> (Sing ko kp) ->
    CompareSpecT km kn ko 'Gt
data instance Sing (CompareSpecT lt lu lv lw) ls where
  SCompEqT ::
    forall (ku :: *) (kv :: *) (kw :: *) (kx :: ku) (ky :: Sing * ku) (kz :: Sing * kv) (la :: Sing * kw) (lb :: Sing
    ku kx). (Sing * ku) -> (Sing * kv) -> (Sing * kw) -> (Sing ku kx) -> Sing' ('CompEqT ky kz la lb)
  SCompLtT ::
    forall (lc :: *) (ld :: *) (le :: *) (lf :: ld) (lg :: Sing * lc) (lh :: Sing * ld) (li :: Sing * le) (lj :: Sing
    ld lf). (Sing * lc) -> (Sing * ld) -> (Sing * le) -> (Sing ld lf) -> Sing' ('CompLtT lg lh li lj)
  SCompGtT ::
    forall (lk :: *) (ll :: *) (lm :: *) (ln :: lm) (lo :: Sing * lk) (lp :: Sing * ll) (lq :: Sing * lm) (lr :: Sing
    lm ln). (Sing * lk) -> (Sing * ll) -> (Sing * lm) -> (Sing lm ln) -> Sing' ('CompGtT lo lp lq lr)
$(P.return [])
data BG (lx :: TyFun' * *)
$(P.return [])
data BI (lz :: *) (ly :: TyFun' * *)
$(P.return [])
data BK (mc :: *) (mb :: *) (ma :: TyFun' * *)
$(P.return [])
data BM (mg :: *) (mf :: *) (me :: *) (md :: TyFun' Comparison *)
$(P.return [])
type instance (@@) (BM mk mj mi) mh = *
$(P.return [])
type instance (@@) (BK mn mm) ml = TyPi Comparison (BM mn mm ml)
$(P.return [])
type instance (@@) (BI mp) mo = TyPi * (BK mp mo)
$(P.return [])
type instance (@@) BG mq = TyPi * (BI mq)
$(P.return [])
data BF (mr :: TyPi' * BG)
$(P.return [])
data BH (mt :: *) (ms :: TyPi' * (BI mt))
$(P.return [])
type instance (@@@) BF mu = BH mu
$(P.return [])
data BJ (mx :: *) (mw :: *) (mv :: TyPi' * (BK mx mw))
$(P.return [])
type instance (@@@) (BH mz) my = BJ mz my
$(P.return [])
data BL (nd :: *) (nc :: *) (nb :: *) (na :: TyPi' Comparison (BM nd nc nb))
$(P.return [])
type instance (@@@) (BJ ng nf) ne = BL ng nf ne
$(P.return [])
type instance (@@@) (BL nk nj ni) nh = CompareSpecT nk nj ni nh
$(P.return [])
data CompareSpec (nx :: *) (ny :: *) (nz :: *) (oa :: Comparison) :: * where
  CompEq ::
    forall (nl :: *) (nm :: *) (nn :: *) (no :: nl). (Sing * nl) -> (Sing * nm) -> (Sing * nn) -> (Sing nl no) ->
    CompareSpec nl nm nn 'Eq
  CompLt ::
    forall (np :: *) (nq :: *) (nr :: *) (ns :: nq). (Sing * np) -> (Sing * nq) -> (Sing * nr) -> (Sing nq ns) ->
    CompareSpec np nq nr 'Lt
  CompGt ::
    forall (nt :: *) (nu :: *) (nv :: *) (nw :: nv). (Sing * nt) -> (Sing * nu) -> (Sing * nv) -> (Sing nv nw) ->
    CompareSpec nt nu nv 'Gt
data instance Sing (CompareSpec pb pc pd pe) pa where
  SCompEq ::
    forall (ob :: *) (oc :: *) (od :: *) (oe :: ob) (og :: Sing * ob) (oh :: Sing * oc) (oi :: Sing * od) (oj :: Sing
    ob oe). (Sing * ob) -> (Sing * oc) -> (Sing * od) -> (Sing ob oe) -> Sing' ('CompEq og oh oi oj)
  SCompLt ::
    forall (ok :: *) (ol :: *) (om :: *) (on :: ol) (oo :: Sing * ok) (op :: Sing * ol) (oq :: Sing * om) (or :: Sing
    ol on). (Sing * ok) -> (Sing * ol) -> (Sing * om) -> (Sing ol on) -> Sing' ('CompLt oo op oq or)
  SCompGt ::
    forall (os :: *) (ot :: *) (ou :: *) (ov :: ou) (ow :: Sing * os) (ox :: Sing * ot) (oy :: Sing * ou) (oz :: Sing
    ou ov). (Sing * os) -> (Sing * ot) -> (Sing * ou) -> (Sing ou ov) -> Sing' ('CompGt ow ox oy oz)
$(P.return [])
data AY (pf :: TyFun' * *)
$(P.return [])
data BA (ph :: *) (pg :: TyFun' * *)
$(P.return [])
data BC (pk :: *) (pj :: *) (pi :: TyFun' * *)
$(P.return [])
data BE (po :: *) (pn :: *) (pm :: *) (pl :: TyFun' Comparison *)
$(P.return [])
type instance (@@) (BE ps pr pq) pp = *
$(P.return [])
type instance (@@) (BC pv pu) pt = TyPi Comparison (BE pv pu pt)
$(P.return [])
type instance (@@) (BA px) pw = TyPi * (BC px pw)
$(P.return [])
type instance (@@) AY py = TyPi * (BA py)
$(P.return [])
data AX (pz :: TyPi' * AY)
$(P.return [])
data AZ (qb :: *) (qa :: TyPi' * (BA qb))
$(P.return [])
type instance (@@@) AX qc = AZ qc
$(P.return [])
data BB (qf :: *) (qe :: *) (qd :: TyPi' * (BC qf qe))
$(P.return [])
type instance (@@@) (AZ qh) qg = BB qh qg
$(P.return [])
data BD (ql :: *) (qk :: *) (qj :: *) (qi :: TyPi' Comparison (BE ql qk qj))
$(P.return [])
type instance (@@@) (BB qo qn) qm = BD qo qn qm
$(P.return [])
type instance (@@@) (BD qs qr qq) qp = CompareSpec qs qr qq qp
$(P.return [])
data instance Sing Comparison qt where
  SEq ::   Sing' 'Eq
  SLt ::   Sing' 'Lt
  SGt ::   Sing' 'Gt
$(P.return [])
data List (qx :: *) :: * where
  Nil ::   forall (qu :: *). (Sing * qu) -> List qu
  Cons ::   forall (qv :: *) (qw :: qv). (Sing * qv) -> (Sing qv qw) -> (List qv) -> List qv
data AW (qy :: TyFun' * *)
$(P.return [])
type instance (@@) AW qz = *
$(P.return [])
data AV (ra :: TyPi' * AW)
$(P.return [])
type instance (@@@) AV rb = List rb
$(P.return [])
data instance Sing (List rk) rj where
  SNil ::   forall (rc :: *) (rd :: Sing * rc). (Sing * rc) -> Sing' ('Nil rd)
  SCons ::
    forall (re :: *) (rf :: re) (rg :: Sing * re) (rh :: Sing re rf) (ri :: AV @@@ re). (Sing * re) -> (Sing re rf) ->
    (Sing (AV @@@ re) ri) -> Sing' ('Cons rg rh ri)
$(P.return [])
data Prod (rp :: *) (rq :: *) :: * where
  Pair ::
    forall (rl :: *) (rm :: *) (rn :: rl) (ro :: rm). (Sing * rl) -> (Sing * rm) -> (Sing rl rn) -> (Sing rm ro) ->
    Prod rl rm
data instance Sing (Prod sa sb) rz where
  SPair ::
    forall (rr :: *) (rs :: *) (rt :: rr) (ru :: rs) (rv :: Sing * rr) (rw :: Sing * rs) (rx :: Sing rr rt) (ry :: Sing
    rs ru). (Sing * rr) -> (Sing * rs) -> (Sing rr rt) -> (Sing rs ru) -> Sing' ('Pair rv rw rx ry)
$(P.return [])
data AS (sc :: TyFun' * *)
$(P.return [])
data AU (se :: *) (sd :: TyFun' * *)
$(P.return [])
type instance (@@) (AU sg) sf = *
$(P.return [])
type instance (@@) AS sh = TyPi * (AU sh)
$(P.return [])
data AR (si :: TyPi' * AS)
$(P.return [])
data AT (sk :: *) (sj :: TyPi' * (AU sk))
$(P.return [])
type instance (@@@) AR sl = AT sl
$(P.return [])
type instance (@@@) (AT sn) sm = Prod sn sm
$(P.return [])
data Sum (su :: *) (sv :: *) :: * where
  Inl ::   forall (so :: *) (sp :: *) (sq :: so). (Sing * so) -> (Sing * sp) -> (Sing so sq) -> Sum so sp
  Inr ::   forall (sr :: *) (ss :: *) (st :: ss). (Sing * sr) -> (Sing * ss) -> (Sing ss st) -> Sum sr ss
data instance Sing (Sum tj tk) ti where
  SInl ::
    forall (sw :: *) (sx :: *) (sy :: sw) (sz :: Sing * sw) (ta :: Sing * sx) (tb :: Sing sw sy). (Sing * sw) -> (Sing
    * sx) -> (Sing sw sy) -> Sing' ('Inl sz ta tb)
  SInr ::
    forall (tc :: *) (td :: *) (te :: td) (tf :: Sing * tc) (tg :: Sing * td) (th :: Sing td te). (Sing * tc) -> (Sing
    * td) -> (Sing td te) -> Sing' ('Inr tf tg th)
$(P.return [])
data AO (tl :: TyFun' * *)
$(P.return [])
data AQ (tn :: *) (tm :: TyFun' * *)
$(P.return [])
type instance (@@) (AQ tp) to = *
$(P.return [])
type instance (@@) AO tq = TyPi * (AQ tq)
$(P.return [])
data AN (tr :: TyPi' * AO)
$(P.return [])
data AP (tt :: *) (ts :: TyPi' * (AQ tt))
$(P.return [])
type instance (@@@) AN tu = AP tu
$(P.return [])
type instance (@@@) (AP tw) tv = Sum tw tv
$(P.return [])
data Option (ua :: *) :: * where
  Some ::   forall (tx :: *) (ty :: tx). (Sing * tx) -> (Sing tx ty) -> Option tx
  None ::   forall (tz :: *). (Sing * tz) -> Option tz
data instance Sing (Option ui) uh where
  SSome ::
    forall (ub :: *) (uc :: ub) (ud :: Sing * ub) (ue :: Sing ub uc). (Sing * ub) -> (Sing ub uc) -> Sing' ('Some ud
    ue)
  SNone ::   forall (uf :: *) (ug :: Sing * uf). (Sing * uf) -> Sing' ('None ug)
$(P.return [])
data AM (uj :: TyFun' * *)
$(P.return [])
type instance (@@) AM uk = *
$(P.return [])
data AL (ul :: TyPi' * AM)
$(P.return [])
type instance (@@@) AL um = Option um
$(P.return [])
data instance Sing Nat uo where
  SO ::   Sing' 'O
  SS ::   forall (un :: Nat). (Sing Nat un) -> Sing' ('S un)
$(P.return [])
data Bool :: * where
  True ::   Bool
  False ::   Bool
data BoolSpec (uv :: *) (uw :: *) (ux :: Bool) :: * where
  BoolSpecT ::
    forall (up :: *) (uq :: *) (ur :: up). (Sing * up) -> (Sing * uq) -> (Sing up ur) -> BoolSpec up uq 'True
  BoolSpecF ::
    forall (us :: *) (ut :: *) (uu :: ut). (Sing * us) -> (Sing * ut) -> (Sing ut uu) -> BoolSpec us ut 'False
data instance Sing (BoolSpec vl vm vn) vk where
  SBoolSpecT ::
    forall (uy :: *) (uz :: *) (va :: uy) (vb :: Sing * uy) (vc :: Sing * uz) (vd :: Sing uy va). (Sing * uy) -> (Sing
    * uz) -> (Sing uy va) -> Sing' ('BoolSpecT vb vc vd)
  SBoolSpecF ::
    forall (ve :: *) (vf :: *) (vg :: vf) (vh :: Sing * ve) (vi :: Sing * vf) (vj :: Sing vf vg). (Sing * ve) -> (Sing
    * vf) -> (Sing vf vg) -> Sing' ('BoolSpecF vh vi vj)
$(P.return [])
data AG (vo :: TyFun' * *)
$(P.return [])
data AI (vq :: *) (vp :: TyFun' * *)
$(P.return [])
data AK (vt :: *) (vs :: *) (vr :: TyFun' Bool *)
$(P.return [])
type instance (@@) (AK vw vv) vu = *
$(P.return [])
type instance (@@) (AI vy) vx = TyPi Bool (AK vy vx)
$(P.return [])
type instance (@@) AG vz = TyPi * (AI vz)
$(P.return [])
data AF (wa :: TyPi' * AG)
$(P.return [])
data AH (wc :: *) (wb :: TyPi' * (AI wc))
$(P.return [])
type instance (@@@) AF wd = AH wd
$(P.return [])
data AJ (wg :: *) (wf :: *) (we :: TyPi' Bool (AK wg wf))
$(P.return [])
type instance (@@@) (AH wi) wh = AJ wi wh
$(P.return [])
type instance (@@@) (AJ wl wk) wj = BoolSpec wl wk wj
$(P.return [])
data Eq_true (wm :: Bool) :: * where
  Is_eq_true ::   Eq_true 'True
data instance Sing (Eq_true wo) wn where
  SIs_eq_true ::   Sing' 'Is_eq_true
$(P.return [])
data AE (wp :: TyFun' Bool *)
$(P.return [])
type instance (@@) AE wq = *
$(P.return [])
data AD (wr :: TyPi' Bool AE)
$(P.return [])
type instance (@@@) AD ws = Eq_true ws
$(P.return [])
data instance Sing Bool wt where
  STrue ::   Sing' 'True
  SFalse ::   Sing' 'False
$(P.return [])
data Unit :: * where
  Tt ::   Unit
data instance Sing Unit wu where
  STt ::   Sing' 'Tt
$(P.return [])
data Empty_set :: * where
  
data instance Sing Empty_set wv where
  
$(P.return [])
data Inhabited (wy :: *) :: * where
  Inhabits ::   forall (ww :: *) (wx :: ww). (Sing * ww) -> (Sing ww wx) -> Inhabited ww
data instance Sing (Inhabited xe) xd where
  SInhabits ::
    forall (wz :: *) (xa :: wz) (xb :: Sing * wz) (xc :: Sing wz xa). (Sing * wz) -> (Sing wz xa) -> Sing' ('Inhabits
    xb xc)
$(P.return [])
data AC (xf :: TyFun' * *)
$(P.return [])
type instance (@@) AC xg = *
$(P.return [])
data AB (xh :: TyPi' * AC)
$(P.return [])
type instance (@@@) AB xi = Inhabited xi
$(P.return [])
data Eq (xl :: *) (xm :: xl) (xn :: xl) :: * where
  Eq_refl ::   forall (xj :: *) (xk :: xj). (Sing * xj) -> (Sing xj xk) -> Eq xj xk xk
data instance Sing (Eq xt xu xv) xs where
  SEq_refl ::
    forall (xo :: *) (xp :: xo) (xq :: Sing * xo) (xr :: Sing xo xp). (Sing * xo) -> (Sing xo xp) -> Sing' ('Eq_refl xq
    xr)
$(P.return [])
data W (xw :: TyFun' * *)
$(P.return [])
data Y (xy :: *) (xx :: TyFun' xy *)
$(P.return [])
data AA (yb :: *) (ya :: yb) (xz :: TyFun' yb *)
$(P.return [])
type instance (@@) (AA ye yd) yc = *
$(P.return [])
type instance (@@) (Y yg) yf = TyPi yg (AA yg yf)
$(P.return [])
type instance (@@) W yh = TyPi yh (Y yh)
$(P.return [])
data V (yi :: TyPi' * W)
$(P.return [])
data X (yk :: *) (yj :: TyPi' yk (Y yk))
$(P.return [])
type instance (@@@) V yl = X yl
$(P.return [])
data Z (yo :: *) (yn :: yo) (ym :: TyPi' yo (AA yo yn))
$(P.return [])
type instance (@@@) (X yq) yp = Z yq yp
$(P.return [])
type instance (@@@) (Z yt ys) yr = Eq yt ys yr
$(P.return [])
data Ex2 (za :: *) (zb :: TyPi za (I za)) (zc :: TyPi za (N za zb)) :: * where
  Ex_intro2 ::
    forall (yu :: *) (yv :: TyPi yu (I yu)) (yw :: TyPi yu (N yu yv)) (yx :: yu) (yy :: yv @@@ yx) (yz :: yw @@@ yx).
    (Sing * yu) -> (Sing (TyPi yu (I yu)) yv) -> (Sing (TyPi yu (N yu yv)) yw) -> (Sing yu yx) -> (Sing (yv @@@ yx) yy)
    -> (Sing (yw @@@ yx) yz) -> Ex2 yu yv yw
data instance Sing (Ex2 zq zr zs) zp where
  SEx_intro2 ::
    forall (zd :: *) (ze :: TyPi zd (I zd)) (zf :: TyPi zd (N zd ze)) (zg :: zd) (zh :: ze @@@ zg) (zi :: zf @@@ zg)
    (zj :: Sing * zd) (zk :: Sing (TyPi zd (I zd)) ze) (zl :: Sing (TyPi zd (N zd ze)) zf) (zm :: Sing zd zg) (zn ::
    Sing (ze @@@ zg) zh) (zo :: Sing (zf @@@ zg) zi). (Sing * zd) -> (Sing (TyPi zd (I zd)) ze) -> (Sing (TyPi zd (N zd
    ze)) zf) -> (Sing zd zg) -> (Sing (ze @@@ zg) zh) -> (Sing (zf @@@ zg) zi) -> Sing' ('Ex_intro2 zj zk zl zm zn zo)
$(P.return [])
data P (zt :: TyFun' * *)
$(P.return [])
data R (zv :: *) (zu :: TyFun' (TyPi zv (I zv)) *)
$(P.return [])
data U (zy :: *) (zx :: TyPi zy (I zy)) (zw :: TyFun' (TyPi zy (N zy zx)) *)
$(P.return [])
type instance (@@) (U aab aaa) zz = *
$(P.return [])
type instance (@@) (R aad) aac = TyPi (TyPi aad (N aad aac)) (U aad aac)
$(P.return [])
type instance (@@) P aae = TyPi (TyPi aae (I aae)) (R aae)
$(P.return [])
data O (aaf :: TyPi' * P)
$(P.return [])
data Q (aah :: *) (aag :: TyPi' (TyPi aah (I aah)) (R aah))
$(P.return [])
type instance (@@@) O aai = Q aai
$(P.return [])
data S (aal :: *) (aak :: TyPi aal (I aal)) (aaj :: TyPi' (TyPi aal (N aal aak)) (U aal aak))
$(P.return [])
type instance (@@@) (Q aan) aam = S aan aam
$(P.return [])
type instance (@@@) (S aaq aap) aao = Ex2 aaq aap aao
$(P.return [])
data Ex (aav :: *) (aaw :: TyPi aav (I aav)) :: * where
  Ex_intro ::
    forall (aar :: *) (aas :: TyPi aar (I aar)) (aat :: aar) (aau :: aas @@@ aat). (Sing * aar) -> (Sing (TyPi aar (I
    aar)) aas) -> (Sing aar aat) -> (Sing (aas @@@ aat) aau) -> Ex aar aas
data instance Sing (Ex abg abh) abf where
  SEx_intro ::
    forall (aax :: *) (aay :: TyPi aax (I aax)) (aaz :: aax) (aba :: aay @@@ aaz) (abb :: Sing * aax) (abc :: Sing
    (TyPi aax (I aax)) aay) (abd :: Sing aax aaz) (abe :: Sing (aay @@@ aaz) aba). (Sing * aax) -> (Sing (TyPi aax (I
    aax)) aay) -> (Sing aax aaz) -> (Sing (aay @@@ aaz) aba) -> Sing' ('Ex_intro abb abc abd abe)
$(P.return [])
data K (abi :: TyFun' * *)
$(P.return [])
data M (abk :: *) (abj :: TyFun' (TyPi abk (I abk)) *)
$(P.return [])
type instance (@@) (M abm) abl = *
$(P.return [])
type instance (@@) K abn = TyPi (TyPi abn (I abn)) (M abn)
$(P.return [])
data J (abo :: TyPi' * K)
$(P.return [])
data L (abq :: *) (abp :: TyPi' (TyPi abq (I abq)) (M abq))
$(P.return [])
type instance (@@@) J abr = L abr
$(P.return [])
type instance (@@@) (L abt) abs = Ex abt abs
$(P.return [])
data Or (aca :: *) (acb :: *) :: * where
  Or_introl ::
    forall (abu :: *) (abv :: *) (abw :: abu). (Sing * abu) -> (Sing * abv) -> (Sing abu abw) -> Or abu abv
  Or_intror ::
    forall (abx :: *) (aby :: *) (abz :: aby). (Sing * abx) -> (Sing * aby) -> (Sing aby abz) -> Or abx aby
data instance Sing (Or acp acq) aco where
  SOr_introl ::
    forall (acc :: *) (acd :: *) (ace :: acc) (acf :: Sing * acc) (acg :: Sing * acd) (ach :: Sing acc ace). (Sing *
    acc) -> (Sing * acd) -> (Sing acc ace) -> Sing' ('Or_introl acf acg ach)
  SOr_intror ::
    forall (aci :: *) (acj :: *) (ack :: acj) (acl :: Sing * aci) (acm :: Sing * acj) (acn :: Sing acj ack). (Sing *
    aci) -> (Sing * acj) -> (Sing acj ack) -> Sing' ('Or_intror acl acm acn)
$(P.return [])
data F (acr :: TyFun' * *)
$(P.return [])
data H (act :: *) (acs :: TyFun' * *)
$(P.return [])
type instance (@@) (H acv) acu = *
$(P.return [])
type instance (@@) F acw = TyPi * (H acw)
$(P.return [])
data E (acx :: TyPi' * F)
$(P.return [])
data G (acz :: *) (acy :: TyPi' * (H acz))
$(P.return [])
type instance (@@@) E ada = G ada
$(P.return [])
type instance (@@@) (G adc) adb = Or adc adb
$(P.return [])
data And (adh :: *) (adi :: *) :: * where
  Conj ::
    forall (add :: *) (ade :: *) (adf :: add) (adg :: ade). (Sing * add) -> (Sing * ade) -> (Sing add adf) -> (Sing ade
    adg) -> And add ade
data instance Sing (And ads adt) adr where
  SConj ::
    forall (adj :: *) (adk :: *) (adl :: adj) (adm :: adk) (adn :: Sing * adj) (ado :: Sing * adk) (adp :: Sing adj
    adl) (adq :: Sing adk adm). (Sing * adj) -> (Sing * adk) -> (Sing adj adl) -> (Sing adk adm) -> Sing' ('Conj adn
    ado adp adq)
$(P.return [])
data B (adu :: TyFun' * *)
$(P.return [])
data D (adw :: *) (adv :: TyFun' * *)
$(P.return [])
type instance (@@) (D ady) adx = *
$(P.return [])
type instance (@@) B adz = TyPi * (D adz)
$(P.return [])
data A (aea :: TyPi' * B)
$(P.return [])
data C (aec :: *) (aeb :: TyPi' * (D aec))
$(P.return [])
type instance (@@@) A aed = C aed
$(P.return [])
type instance (@@@) (C aef) aee = And aef aee
$(P.return [])
data False :: * where
  
data instance Sing False aeg where
  
$(P.return [])
data True :: * where
  I ::   True
data instance Sing True aeh where
  SI ::   Sing' 'I
$(P.return [])
