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
data T0 (e :: *) (f :: Nat) :: * where
  Nil0 ::   forall (a :: *). (Sing * a) -> T0 a 'O
  Cons0 ::   forall (b :: *) (c :: b) (d :: Nat). (Sing * b) -> (Sing b c) -> (Sing Nat d) -> (T0 b d) -> T0 b ('S d)
$(P.return [])
data ED (i :: *) (h :: *) (g :: TyFun' i *)
$(P.return [])
data EE (m :: *) (l :: *) (k :: m) (j :: TyFun' l *)
$(P.return [])
type instance (@@) (EE q p o) n = *
$(P.return [])
type instance (@@) (ED t s) r = TyPi s (EE t s r)
$(P.return [])
data Exists2 (al :: *) (am :: *) (an :: TyPi al (ED al am)) (ao :: Nat) (ap :: T0 al ao) (aq :: T0 am ao) :: * where
  Exists2_cons_hd ::
    forall (u :: *) (v :: *) (w :: TyPi u (ED u v)) (x :: Nat) (y :: u) (z :: v) (aa :: T0 u x) (ab :: T0 v x) (ac :: w
    @@@ y @@@ z). (Sing * u) -> (Sing * v) -> (Sing (TyPi u (ED u v)) w) -> (Sing Nat x) -> (Sing u y) -> (Sing v z) ->
    (Sing (T0 u x) aa) -> (Sing (T0 v x) ab) -> (Sing (w @@@ y @@@ z) ac) -> Exists2 u v w ('S x) ('Cons0 (ToSing u)
    (ToSing y) (ToSing x) aa) ('Cons0 (ToSing v) (ToSing z) (ToSing x) ab)
  Exists2_cons_tl ::
    forall (ad :: *) (ae :: *) (af :: TyPi ad (ED ad ae)) (ag :: Nat) (ah :: ad) (ai :: ae) (aj :: T0 ad ag) (ak :: T0
    ae ag). (Sing * ad) -> (Sing * ae) -> (Sing (TyPi ad (ED ad ae)) af) -> (Sing Nat ag) -> (Sing ad ah) -> (Sing ae
    ai) -> (Sing (T0 ad ag) aj) -> (Sing (T0 ae ag) ak) -> (Exists2 ad ae af ag aj ak) -> Exists2 ad ae af ('S ag)
    ('Cons0 (ToSing ad) (ToSing ah) (ToSing ag) aj) ('Cons0 (ToSing ae) (ToSing ai) (ToSing ag) ak)
$(P.return [])
data instance Sing (Exists2 cb cc cd ce cf cg) ca where
  SExists2_cons_hd ::
    forall (ar :: *) (as :: *) (at :: TyPi ar (ED ar as)) (au :: Nat) (av :: ar) (aw :: as) (ax :: T0 ar au) (ay :: T0
    as au) (az :: at @@@ av @@@ aw) (ba :: Sing * ar) (bb :: Sing * as) (bc :: Sing (TyPi ar (ED ar as)) at) (bd ::
    Sing Nat au) (be :: Sing ar av) (bf :: Sing as aw) (bg :: Sing (T0 ar au) ax) (bh :: Sing (T0 as au) ay) (bi ::
    Sing (at @@@ av @@@ aw) az). (Sing * ar) -> (Sing * as) -> (Sing (TyPi ar (ED ar as)) at) -> (Sing Nat au) -> (Sing
    ar av) -> (Sing as aw) -> (Sing (T0 ar au) ax) -> (Sing (T0 as au) ay) -> (Sing (at @@@ av @@@ aw) az) -> Sing'
    ('Exists2_cons_hd ba bb bc bd be bf bg bh bi)
  SExists2_cons_tl ::
    forall (bj :: *) (bk :: *) (bl :: TyPi bj (ED bj bk)) (bm :: Nat) (bn :: bj) (bo :: bk) (bp :: T0 bj bm) (bq :: T0
    bk bm) (br :: Sing * bj) (bs :: Sing * bk) (bt :: Sing (TyPi bj (ED bj bk)) bl) (bu :: Sing Nat bm) (bv :: Sing bj
    bn) (bw :: Sing bk bo) (bx :: Sing (T0 bj bm) bp) (by :: Sing (T0 bk bm) bq) (bz :: Exists2 bj bk bl bm bp bq).
    (Sing * bj) -> (Sing * bk) -> (Sing (TyPi bj (ED bj bk)) bl) -> (Sing Nat bm) -> (Sing bj bn) -> (Sing bk bo) ->
    (Sing (T0 bj bm) bp) -> (Sing (T0 bk bm) bq) -> (Sing (Exists2 bj bk bl bm bp bq) bz) -> Sing' ('Exists2_cons_tl br
    bs bt bu bv bw bx by bz)
$(P.return [])
data ES (ch :: TyFun' * *)
$(P.return [])
data EU (cj :: *) (ci :: TyFun' * *)
$(P.return [])
data EW (cm :: *) (cl :: *) (ck :: TyFun' (TyPi cm (ED cm cl)) *)
$(P.return [])
data EY (cq :: *) (cp :: *) (co :: TyPi cq (ED cq cp)) (cn :: TyFun' Nat *)
$(P.return [])
data FA (cv :: *) (cu :: *) (ct :: TyPi cv (ED cv cu)) (cs :: Nat) (cr :: TyFun' (T0 cv cs) *)
$(P.return [])
data FC (db :: *) (da :: *) (cz :: TyPi db (ED db da)) (cy :: Nat) (cx :: T0 db cy) (cw :: TyFun' (T0 da cy) *)
$(P.return [])
type instance (@@) (FC dh dg df de dd) dc = *
$(P.return [])
type instance (@@) (FA dm dl dk dj) di = TyPi (T0 dl dj) (FC dm dl dk dj di)
$(P.return [])
type instance (@@) (EY dr dq dp) dn = TyPi (T0 dr dn) (FA dr dq dp dn)
$(P.return [])
type instance (@@) (EW du dt) ds = TyPi Nat (EY du dt ds)
$(P.return [])
type instance (@@) (EU dw) dv = TyPi (TyPi dw (ED dw dv)) (EW dw dv)
$(P.return [])
type instance (@@) ES dx = TyPi * (EU dx)
$(P.return [])
data ER (dy :: TyPi' * ES)
$(P.return [])
data ET (ea :: *) (dz :: TyPi' * (EU ea))
$(P.return [])
type instance (@@@) ER eb = ET eb
$(P.return [])
data EV (ee :: *) (ed :: *) (ec :: TyPi' (TyPi ee (ED ee ed)) (EW ee ed))
$(P.return [])
type instance (@@@) (ET eg) ef = EV eg ef
$(P.return [])
data EX (ek :: *) (ej :: *) (ei :: TyPi ek (ED ek ej)) (eh :: TyPi' Nat (EY ek ej ei))
$(P.return [])
type instance (@@@) (EV en em) el = EX en em el
$(P.return [])
data EZ (es :: *) (er :: *) (eq :: TyPi es (ED es er)) (ep :: Nat) (eo :: TyPi' (T0 es ep) (FA es er eq ep))
$(P.return [])
type instance (@@@) (EX ew ev eu) et = EZ ew ev eu et
$(P.return [])
data FB (fc :: *) (fb :: *) (fa :: TyPi fc (ED fc fb)) (ez :: Nat) (ey :: T0 fc ez) (ex :: TyPi' (T0 fb ez) (FC fc fb fa ez ey))
$(P.return [])
type instance (@@@) (EZ fh fg ff fe) fd = FB fh fg ff fe fd
$(P.return [])
type instance (@@@) (FB fn fm fl fk fj) fi = Exists2 fn fm fl fk fj fi
$(P.return [])
data Forall2 (ga :: *) (gb :: *) (gc :: TyPi ga (ED ga gb)) (gd :: Nat) (ge :: T0 ga gd) (gf :: T0 gb gd) :: * where
  Forall2_nil ::
    forall (fo :: *) (fp :: *) (fq :: TyPi fo (ED fo fp)). (Sing * fo) -> (Sing * fp) -> (Sing (TyPi fo (ED fo fp)) fq)
    -> Forall2 fo fp fq 'O ('Nil0 (ToSing fo)) ('Nil0 (ToSing fp))
  Forall2_cons ::
    forall (fr :: *) (fs :: *) (ft :: TyPi fr (ED fr fs)) (fu :: Nat) (fv :: fr) (fw :: fs) (fx :: T0 fr fu) (fy :: T0
    fs fu) (fz :: ft @@@ fv @@@ fw). (Sing * fr) -> (Sing * fs) -> (Sing (TyPi fr (ED fr fs)) ft) -> (Sing Nat fu) ->
    (Sing fr fv) -> (Sing fs fw) -> (Sing (T0 fr fu) fx) -> (Sing (T0 fs fu) fy) -> (Sing (ft @@@ fv @@@ fw) fz) ->
    (Forall2 fr fs ft fu fx fy) -> Forall2 fr fs ft ('S fu) ('Cons0 (ToSing fr) (ToSing fv) (ToSing fu) fx) ('Cons0
    (ToSing fs) (ToSing fw) (ToSing fu) fy)
$(P.return [])
data instance Sing (Forall2 hg hh hi hj hk hl) hf where
  SForall2_nil ::
    forall (gg :: *) (gh :: *) (gi :: TyPi gg (ED gg gh)) (gj :: Sing * gg) (gk :: Sing * gh) (gl :: Sing (TyPi gg (ED
    gg gh)) gi). (Sing * gg) -> (Sing * gh) -> (Sing (TyPi gg (ED gg gh)) gi) -> Sing' ('Forall2_nil gj gk gl)
  SForall2_cons ::
    forall (gm :: *) (gn :: *) (go :: TyPi gm (ED gm gn)) (gp :: Nat) (gq :: gm) (gr :: gn) (gs :: T0 gm gp) (gt :: T0
    gn gp) (gu :: go @@@ gq @@@ gr) (gv :: Sing * gm) (gw :: Sing * gn) (gx :: Sing (TyPi gm (ED gm gn)) go) (gy ::
    Sing Nat gp) (gz :: Sing gm gq) (ha :: Sing gn gr) (hb :: Sing (T0 gm gp) gs) (hc :: Sing (T0 gn gp) gt) (hd ::
    Sing (go @@@ gq @@@ gr) gu) (he :: Forall2 gm gn go gp gs gt). (Sing * gm) -> (Sing * gn) -> (Sing (TyPi gm (ED gm
    gn)) go) -> (Sing Nat gp) -> (Sing gm gq) -> (Sing gn gr) -> (Sing (T0 gm gp) gs) -> (Sing (T0 gn gp) gt) -> (Sing
    (go @@@ gq @@@ gr) gu) -> (Sing (Forall2 gm gn go gp gs gt) he) -> Sing' ('Forall2_cons gv gw gx gy gz ha hb hc hd
    he)
$(P.return [])
data EG (hm :: TyFun' * *)
$(P.return [])
data EI (ho :: *) (hn :: TyFun' * *)
$(P.return [])
data EK (hr :: *) (hq :: *) (hp :: TyFun' (TyPi hr (ED hr hq)) *)
$(P.return [])
data EM (hv :: *) (hu :: *) (ht :: TyPi hv (ED hv hu)) (hs :: TyFun' Nat *)
$(P.return [])
data EO (ia :: *) (hz :: *) (hy :: TyPi ia (ED ia hz)) (hx :: Nat) (hw :: TyFun' (T0 ia hx) *)
$(P.return [])
data EQ (ih :: *) (ig :: *) (ie :: TyPi ih (ED ih ig)) (id :: Nat) (ic :: T0 ih id) (ib :: TyFun' (T0 ig id) *)
$(P.return [])
type instance (@@) (EQ io im il ik ij) ii = *
$(P.return [])
type instance (@@) (EO it is ir iq) ip = TyPi (T0 is iq) (EQ it is ir iq ip)
$(P.return [])
type instance (@@) (EM ix iw iv) iu = TyPi (T0 ix iu) (EO ix iw iv iu)
$(P.return [])
type instance (@@) (EK ja iz) iy = TyPi Nat (EM ja iz iy)
$(P.return [])
type instance (@@) (EI jc) jb = TyPi (TyPi jc (ED jc jb)) (EK jc jb)
$(P.return [])
type instance (@@) EG jd = TyPi * (EI jd)
$(P.return [])
data EF (je :: TyPi' * EG)
$(P.return [])
data EH (jg :: *) (jf :: TyPi' * (EI jg))
$(P.return [])
type instance (@@@) EF jh = EH jh
$(P.return [])
data EJ (jk :: *) (jj :: *) (ji :: TyPi' (TyPi jk (ED jk jj)) (EK jk jj))
$(P.return [])
type instance (@@@) (EH jm) jl = EJ jm jl
$(P.return [])
data EL (jq :: *) (jp :: *) (jo :: TyPi jq (ED jq jp)) (jn :: TyPi' Nat (EM jq jp jo))
$(P.return [])
type instance (@@@) (EJ jt js) jr = EL jt js jr
$(P.return [])
data EN (jy :: *) (jx :: *) (jw :: TyPi jy (ED jy jx)) (jv :: Nat) (ju :: TyPi' (T0 jy jv) (EO jy jx jw jv))
$(P.return [])
type instance (@@@) (EL kc kb ka) jz = EN kc kb ka jz
$(P.return [])
data EP (ki :: *) (kh :: *) (kg :: TyPi ki (ED ki kh)) (kf :: Nat) (ke :: T0 ki kf) (kd :: TyPi' (T0 kh kf) (EQ ki kh kg kf ke))
$(P.return [])
type instance (@@@) (EN kn km kl kk) kj = EP kn km kl kk kj
$(P.return [])
type instance (@@@) (EP kt ks kr kq kp) ko = Forall2 kt ks kr kq kp ko
$(P.return [])
data In (ld :: *) (le :: ld) (lf :: Nat) (lg :: T0 ld lf) :: * where
  In_cons_hd ::
    forall (ku :: *) (kv :: ku) (kw :: Nat) (kx :: T0 ku kw). (Sing * ku) -> (Sing ku kv) -> (Sing Nat kw) -> (Sing (T0
    ku kw) kx) -> In ku kv ('S kw) ('Cons0 (ToSing ku) (ToSing kv) (ToSing kw) kx)
  In_cons_tl ::
    forall (ky :: *) (kz :: ky) (la :: Nat) (lb :: ky) (lc :: T0 ky la). (Sing * ky) -> (Sing ky kz) -> (Sing Nat la)
    -> (Sing ky lb) -> (Sing (T0 ky la) lc) -> (In ky kz la lc) -> In ky kz ('S la) ('Cons0 (ToSing ky) (ToSing lb)
    (ToSing la) lc)
$(P.return [])
data instance Sing (In mb mc md me) ma where
  SIn_cons_hd ::
    forall (lh :: *) (li :: lh) (lj :: Nat) (lk :: T0 lh lj) (ll :: Sing * lh) (lm :: Sing lh li) (ln :: Sing Nat lj)
    (lo :: Sing (T0 lh lj) lk). (Sing * lh) -> (Sing lh li) -> (Sing Nat lj) -> (Sing (T0 lh lj) lk) -> Sing'
    ('In_cons_hd ll lm ln lo)
  SIn_cons_tl ::
    forall (lp :: *) (lq :: lp) (lr :: Nat) (ls :: lp) (lt :: T0 lp lr) (lu :: Sing * lp) (lv :: Sing lp lq) (lw ::
    Sing Nat lr) (lx :: Sing lp ls) (ly :: Sing (T0 lp lr) lt) (lz :: In lp lq lr lt). (Sing * lp) -> (Sing lp lq) ->
    (Sing Nat lr) -> (Sing lp ls) -> (Sing (T0 lp lr) lt) -> (Sing (In lp lq lr lt) lz) -> Sing' ('In_cons_tl lu lv lw
    lx ly lz)
$(P.return [])
data DW (mf :: TyFun' * *)
$(P.return [])
data DY (mh :: *) (mg :: TyFun' mh *)
$(P.return [])
data EA (mk :: *) (mj :: mk) (mi :: TyFun' Nat *)
$(P.return [])
data EC (mo :: *) (mn :: mo) (mm :: Nat) (ml :: TyFun' (T0 mo mm) *)
$(P.return [])
type instance (@@) (EC ms mr mq) mp = *
$(P.return [])
type instance (@@) (EA mv mu) mt = TyPi (T0 mv mt) (EC mv mu mt)
$(P.return [])
type instance (@@) (DY mx) mw = TyPi Nat (EA mx mw)
$(P.return [])
type instance (@@) DW my = TyPi my (DY my)
$(P.return [])
data DV (mz :: TyPi' * DW)
$(P.return [])
data DX (nb :: *) (na :: TyPi' nb (DY nb))
$(P.return [])
type instance (@@@) DV nc = DX nc
$(P.return [])
data DZ (nf :: *) (ne :: nf) (nd :: TyPi' Nat (EA nf ne))
$(P.return [])
type instance (@@@) (DX nh) ng = DZ nh ng
$(P.return [])
data EB (nl :: *) (nk :: nl) (nj :: Nat) (ni :: TyPi' (T0 nl nj) (EC nl nk nj))
$(P.return [])
type instance (@@@) (DZ no nn) nm = EB no nn nm
$(P.return [])
type instance (@@@) (EB ns nr nq) np = In ns nr nq np
$(P.return [])
data I (nu :: *) (nt :: TyFun' nu *)
$(P.return [])
type instance (@@) (I nw) nv = *
$(P.return [])
data Exists (oj :: *) (ok :: TyPi oj (I oj)) (ol :: Nat) (om :: T0 oj ol) :: * where
  Exists_cons_hd ::
    forall (nx :: *) (ny :: TyPi nx (I nx)) (nz :: Nat) (oa :: nx) (ob :: T0 nx nz) (oc :: ny @@@ oa). (Sing * nx) ->
    (Sing (TyPi nx (I nx)) ny) -> (Sing Nat nz) -> (Sing nx oa) -> (Sing (T0 nx nz) ob) -> (Sing (ny @@@ oa) oc) ->
    Exists nx ny ('S nz) ('Cons0 (ToSing nx) (ToSing oa) (ToSing nz) ob)
  Exists_cons_tl ::
    forall (od :: *) (oe :: TyPi od (I od)) (og :: Nat) (oh :: od) (oi :: T0 od og). (Sing * od) -> (Sing (TyPi od (I
    od)) oe) -> (Sing Nat og) -> (Sing od oh) -> (Sing (T0 od og) oi) -> (Exists od oe og oi) -> Exists od oe ('S og)
    ('Cons0 (ToSing od) (ToSing oh) (ToSing og) oi)
$(P.return [])
data instance Sing (Exists pl pm pn po) pk where
  SExists_cons_hd ::
    forall (on :: *) (oo :: TyPi on (I on)) (op :: Nat) (oq :: on) (or :: T0 on op) (os :: oo @@@ oq) (ot :: Sing * on)
    (ou :: Sing (TyPi on (I on)) oo) (ov :: Sing Nat op) (ow :: Sing on oq) (ox :: Sing (T0 on op) or) (oy :: Sing (oo
    @@@ oq) os). (Sing * on) -> (Sing (TyPi on (I on)) oo) -> (Sing Nat op) -> (Sing on oq) -> (Sing (T0 on op) or) ->
    (Sing (oo @@@ oq) os) -> Sing' ('Exists_cons_hd ot ou ov ow ox oy)
  SExists_cons_tl ::
    forall (oz :: *) (pa :: TyPi oz (I oz)) (pb :: Nat) (pc :: oz) (pd :: T0 oz pb) (pe :: Sing * oz) (pf :: Sing (TyPi
    oz (I oz)) pa) (pg :: Sing Nat pb) (ph :: Sing oz pc) (pi :: Sing (T0 oz pb) pd) (pj :: Exists oz pa pb pd). (Sing
    * oz) -> (Sing (TyPi oz (I oz)) pa) -> (Sing Nat pb) -> (Sing oz pc) -> (Sing (T0 oz pb) pd) -> (Sing (Exists oz pa
    pb pd) pj) -> Sing' ('Exists_cons_tl pe pf pg ph pi pj)
$(P.return [])
data DO (pp :: TyFun' * *)
$(P.return [])
data DQ (pr :: *) (pq :: TyFun' (TyPi pr (I pr)) *)
$(P.return [])
data DS (pu :: *) (pt :: TyPi pu (I pu)) (ps :: TyFun' Nat *)
$(P.return [])
data DU (py :: *) (px :: TyPi py (I py)) (pw :: Nat) (pv :: TyFun' (T0 py pw) *)
$(P.return [])
type instance (@@) (DU qc qb qa) pz = *
$(P.return [])
type instance (@@) (DS qf qe) qd = TyPi (T0 qf qd) (DU qf qe qd)
$(P.return [])
type instance (@@) (DQ qh) qg = TyPi Nat (DS qh qg)
$(P.return [])
type instance (@@) DO qi = TyPi (TyPi qi (I qi)) (DQ qi)
$(P.return [])
data DN (qj :: TyPi' * DO)
$(P.return [])
data DP (ql :: *) (qk :: TyPi' (TyPi ql (I ql)) (DQ ql))
$(P.return [])
type instance (@@@) DN qm = DP qm
$(P.return [])
data DR (qp :: *) (qo :: TyPi qp (I qp)) (qn :: TyPi' Nat (DS qp qo))
$(P.return [])
type instance (@@@) (DP qr) qq = DR qr qq
$(P.return [])
data DT (qv :: *) (qu :: TyPi qv (I qv)) (qt :: Nat) (qs :: TyPi' (T0 qv qt) (DU qv qu qt))
$(P.return [])
type instance (@@@) (DR qy qx) qw = DT qy qx qw
$(P.return [])
type instance (@@@) (DT rc rb ra) qz = Exists rc rb ra qz
$(P.return [])
data Forall (rl :: *) (rm :: TyPi rl (I rl)) (rn :: Nat) (ro :: T0 rl rn) :: * where
  Forall_nil ::
    forall (rd :: *) (re :: TyPi rd (I rd)). (Sing * rd) -> (Sing (TyPi rd (I rd)) re) -> Forall rd re 'O ('Nil0
    (ToSing rd))
  Forall_cons ::
    forall (rf :: *) (rg :: TyPi rf (I rf)) (rh :: Nat) (ri :: rf) (rj :: T0 rf rh) (rk :: rg @@@ ri). (Sing * rf) ->
    (Sing (TyPi rf (I rf)) rg) -> (Sing Nat rh) -> (Sing rf ri) -> (Sing (T0 rf rh) rj) -> (Sing (rg @@@ ri) rk) ->
    (Forall rf rg rh rj) -> Forall rf rg ('S rh) ('Cons0 (ToSing rf) (ToSing ri) (ToSing rh) rj)
$(P.return [])
data instance Sing (Forall sh si sj sk) sg where
  SForall_nil ::
    forall (rp :: *) (rq :: TyPi rp (I rp)) (rr :: Sing * rp) (rs :: Sing (TyPi rp (I rp)) rq). (Sing * rp) -> (Sing
    (TyPi rp (I rp)) rq) -> Sing' ('Forall_nil rr rs)
  SForall_cons ::
    forall (rt :: *) (ru :: TyPi rt (I rt)) (rv :: Nat) (rw :: rt) (rx :: T0 rt rv) (ry :: ru @@@ rw) (rz :: Sing * rt)
    (sa :: Sing (TyPi rt (I rt)) ru) (sb :: Sing Nat rv) (sc :: Sing rt rw) (sd :: Sing (T0 rt rv) rx) (se :: Sing (ru
    @@@ rw) ry) (sf :: Forall rt ru rv rx). (Sing * rt) -> (Sing (TyPi rt (I rt)) ru) -> (Sing Nat rv) -> (Sing rt rw)
    -> (Sing (T0 rt rv) rx) -> (Sing (ru @@@ rw) ry) -> (Sing (Forall rt ru rv rx) sf) -> Sing' ('Forall_cons rz sa sb
    sc sd se sf)
$(P.return [])
data DG (sl :: TyFun' * *)
$(P.return [])
data DI (sn :: *) (sm :: TyFun' (TyPi sn (I sn)) *)
$(P.return [])
data DK (sq :: *) (sp :: TyPi sq (I sq)) (so :: TyFun' Nat *)
$(P.return [])
data DM (su :: *) (st :: TyPi su (I su)) (ss :: Nat) (sr :: TyFun' (T0 su ss) *)
$(P.return [])
type instance (@@) (DM sy sx sw) sv = *
$(P.return [])
type instance (@@) (DK tb ta) sz = TyPi (T0 tb sz) (DM tb ta sz)
$(P.return [])
type instance (@@) (DI td) tc = TyPi Nat (DK td tc)
$(P.return [])
type instance (@@) DG te = TyPi (TyPi te (I te)) (DI te)
$(P.return [])
data DF (tf :: TyPi' * DG)
$(P.return [])
data DH (th :: *) (tg :: TyPi' (TyPi th (I th)) (DI th))
$(P.return [])
type instance (@@@) DF ti = DH ti
$(P.return [])
data DJ (tl :: *) (tk :: TyPi tl (I tl)) (tj :: TyPi' Nat (DK tl tk))
$(P.return [])
type instance (@@@) (DH tn) tm = DJ tn tm
$(P.return [])
data DL (tr :: *) (tq :: TyPi tr (I tr)) (tp :: Nat) (to :: TyPi' (T0 tr tp) (DM tr tq tp))
$(P.return [])
type instance (@@@) (DJ tu tt) ts = DL tu tt ts
$(P.return [])
type instance (@@@) (DL ty tx tw) tv = Forall ty tx tw tv
$(P.return [])
data instance Sing (T0 uj uk) ui where
  SNil0 ::   forall (tz :: *) (ua :: Sing * tz). (Sing * tz) -> Sing' ('Nil0 ua)
  SCons0 ::
    forall (ub :: *) (uc :: ub) (ud :: Nat) (ue :: Sing * ub) (uf :: Sing ub uc) (ug :: Sing Nat ud) (uh :: T0 ub ud).
    (Sing * ub) -> (Sing ub uc) -> (Sing Nat ud) -> (Sing (T0 ub ud) uh) -> Sing' ('Cons0 ue uf ug uh)
$(P.return [])
data DC (ul :: TyFun' * *)
$(P.return [])
data DE (un :: *) (um :: TyFun' Nat *)
$(P.return [])
type instance (@@) (DE up) uo = *
$(P.return [])
type instance (@@) DC uq = TyPi Nat (DE uq)
$(P.return [])
data DB (ur :: TyPi' * DC)
$(P.return [])
data DD (ut :: *) (us :: TyPi' Nat (DE ut))
$(P.return [])
type instance (@@@) DB uu = DD uu
$(P.return [])
type instance (@@@) (DD uw) uv = T0 uw uv
$(P.return [])
data T (uz :: Nat) :: * where
  F1 ::   forall (ux :: Nat). (Sing Nat ux) -> T ('S ux)
  FS ::   forall (uy :: Nat). (Sing Nat uy) -> (T uy) -> T ('S uy)
$(P.return [])
data instance Sing (T vg) vf where
  SF1 ::   forall (va :: Nat) (vb :: Sing Nat va). (Sing Nat va) -> Sing' ('F1 vb)
  SFS ::   forall (vc :: Nat) (vd :: Sing Nat vc) (ve :: T vc). (Sing Nat vc) -> (Sing (T vc) ve) -> Sing' ('FS vd ve)
$(P.return [])
data DA (vh :: TyFun' Nat *)
$(P.return [])
type instance (@@) DA vi = *
$(P.return [])
data CZ (vj :: TyPi' Nat DA)
$(P.return [])
type instance (@@@) CZ vk = T vk
$(P.return [])
data Sumor (vr :: *) (vs :: *) :: * where
  Inleft ::   forall (vl :: *) (vm :: *) (vn :: vl). (Sing * vl) -> (Sing * vm) -> (Sing vl vn) -> Sumor vl vm
  Inright ::   forall (vo :: *) (vp :: *) (vq :: vp). (Sing * vo) -> (Sing * vp) -> (Sing vp vq) -> Sumor vo vp
$(P.return [])
data instance Sing (Sumor wg wh) wf where
  SInleft ::
    forall (vt :: *) (vu :: *) (vv :: vt) (vw :: Sing * vt) (vx :: Sing * vu) (vy :: Sing vt vv). (Sing * vt) -> (Sing
    * vu) -> (Sing vt vv) -> Sing' ('Inleft vw vx vy)
  SInright ::
    forall (vz :: *) (wa :: *) (wb :: wa) (wc :: Sing * vz) (wd :: Sing * wa) (we :: Sing wa wb). (Sing * vz) -> (Sing
    * wa) -> (Sing wa wb) -> Sing' ('Inright wc wd we)
$(P.return [])
data CW (wi :: TyFun' * *)
$(P.return [])
data CY (wk :: *) (wj :: TyFun' * *)
$(P.return [])
type instance (@@) (CY wm) wl = *
$(P.return [])
type instance (@@) CW wn = TyPi * (CY wn)
$(P.return [])
data CV (wo :: TyPi' * CW)
$(P.return [])
data CX (wq :: *) (wp :: TyPi' * (CY wq))
$(P.return [])
type instance (@@@) CV wr = CX wr
$(P.return [])
type instance (@@@) (CX wt) ws = Sumor wt ws
$(P.return [])
data Sumbool (xa :: *) (xb :: *) :: * where
  Left ::   forall (wu :: *) (wv :: *) (ww :: wu). (Sing * wu) -> (Sing * wv) -> (Sing wu ww) -> Sumbool wu wv
  Right ::   forall (wx :: *) (wy :: *) (wz :: wy). (Sing * wx) -> (Sing * wy) -> (Sing wy wz) -> Sumbool wx wy
$(P.return [])
data instance Sing (Sumbool xp xq) xo where
  SLeft ::
    forall (xc :: *) (xd :: *) (xe :: xc) (xf :: Sing * xc) (xg :: Sing * xd) (xh :: Sing xc xe). (Sing * xc) -> (Sing
    * xd) -> (Sing xc xe) -> Sing' ('Left xf xg xh)
  SRight ::
    forall (xi :: *) (xj :: *) (xk :: xj) (xl :: Sing * xi) (xm :: Sing * xj) (xn :: Sing xj xk). (Sing * xi) -> (Sing
    * xj) -> (Sing xj xk) -> Sing' ('Right xl xm xn)
$(P.return [])
data CS (xr :: TyFun' * *)
$(P.return [])
data CU (xt :: *) (xs :: TyFun' * *)
$(P.return [])
type instance (@@) (CU xv) xu = *
$(P.return [])
type instance (@@) CS xw = TyPi * (CU xw)
$(P.return [])
data CR (xx :: TyPi' * CS)
$(P.return [])
data CT (xz :: *) (xy :: TyPi' * (CU xz))
$(P.return [])
type instance (@@@) CR ya = CT ya
$(P.return [])
type instance (@@@) (CT yc) yb = Sumbool yc yb
$(P.return [])
data N (yf :: *) (ye :: TyPi yf (I yf)) (yd :: TyFun' yf *)
$(P.return [])
type instance (@@) (N yi yh) yg = *
$(P.return [])
data SigT2 (yp :: *) (yq :: TyPi yp (I yp)) (yr :: TyPi yp (N yp yq)) :: * where
  ExistT2 ::
    forall (yj :: *) (yk :: TyPi yj (I yj)) (yl :: TyPi yj (N yj yk)) (ym :: yj) (yn :: yk @@@ ym) (yo :: yl @@@ ym).
    (Sing * yj) -> (Sing (TyPi yj (I yj)) yk) -> (Sing (TyPi yj (N yj yk)) yl) -> (Sing yj ym) -> (Sing (yk @@@ ym) yn)
    -> (Sing (yl @@@ ym) yo) -> SigT2 yj yk yl
$(P.return [])
data instance Sing (SigT2 zf zg zh) ze where
  SExistT2 ::
    forall (ys :: *) (yt :: TyPi ys (I ys)) (yu :: TyPi ys (N ys yt)) (yv :: ys) (yw :: yt @@@ yv) (yx :: yu @@@ yv)
    (yy :: Sing * ys) (yz :: Sing (TyPi ys (I ys)) yt) (za :: Sing (TyPi ys (N ys yt)) yu) (zb :: Sing ys yv) (zc ::
    Sing (yt @@@ yv) yw) (zd :: Sing (yu @@@ yv) yx). (Sing * ys) -> (Sing (TyPi ys (I ys)) yt) -> (Sing (TyPi ys (N ys
    yt)) yu) -> (Sing ys yv) -> (Sing (yt @@@ yv) yw) -> (Sing (yu @@@ yv) yx) -> Sing' ('ExistT2 yy yz za zb zc zd)
$(P.return [])
data CM (zi :: TyFun' * *)
$(P.return [])
data CO (zk :: *) (zj :: TyFun' (TyPi zk (I zk)) *)
$(P.return [])
data CQ (zn :: *) (zm :: TyPi zn (I zn)) (zl :: TyFun' (TyPi zn (N zn zm)) *)
$(P.return [])
type instance (@@) (CQ zq zp) zo = *
$(P.return [])
type instance (@@) (CO zs) zr = TyPi (TyPi zs (N zs zr)) (CQ zs zr)
$(P.return [])
type instance (@@) CM zt = TyPi (TyPi zt (I zt)) (CO zt)
$(P.return [])
data CL (zu :: TyPi' * CM)
$(P.return [])
data CN (zw :: *) (zv :: TyPi' (TyPi zw (I zw)) (CO zw))
$(P.return [])
type instance (@@@) CL zx = CN zx
$(P.return [])
data CP (aaa :: *) (zz :: TyPi aaa (I aaa)) (zy :: TyPi' (TyPi aaa (N aaa zz)) (CQ aaa zz))
$(P.return [])
type instance (@@@) (CN aac) aab = CP aac aab
$(P.return [])
type instance (@@@) (CP aaf aae) aad = SigT2 aaf aae aad
$(P.return [])
data SigT (aak :: *) (aal :: TyPi aak (I aak)) :: * where
  ExistT ::
    forall (aag :: *) (aah :: TyPi aag (I aag)) (aai :: aag) (aaj :: aah @@@ aai). (Sing * aag) -> (Sing (TyPi aag (I
    aag)) aah) -> (Sing aag aai) -> (Sing (aah @@@ aai) aaj) -> SigT aag aah
$(P.return [])
data instance Sing (SigT aav aaw) aau where
  SExistT ::
    forall (aam :: *) (aan :: TyPi aam (I aam)) (aao :: aam) (aap :: aan @@@ aao) (aaq :: Sing * aam) (aar :: Sing
    (TyPi aam (I aam)) aan) (aas :: Sing aam aao) (aat :: Sing (aan @@@ aao) aap). (Sing * aam) -> (Sing (TyPi aam (I
    aam)) aan) -> (Sing aam aao) -> (Sing (aan @@@ aao) aap) -> Sing' ('ExistT aaq aar aas aat)
$(P.return [])
data CI (aax :: TyFun' * *)
$(P.return [])
data CK (aaz :: *) (aay :: TyFun' (TyPi aaz (I aaz)) *)
$(P.return [])
type instance (@@) (CK abb) aba = *
$(P.return [])
type instance (@@) CI abc = TyPi (TyPi abc (I abc)) (CK abc)
$(P.return [])
data CH (abd :: TyPi' * CI)
$(P.return [])
data CJ (abf :: *) (abe :: TyPi' (TyPi abf (I abf)) (CK abf))
$(P.return [])
type instance (@@@) CH abg = CJ abg
$(P.return [])
type instance (@@@) (CJ abi) abh = SigT abi abh
$(P.return [])
data Sig2 (abp :: *) (abq :: TyPi abp (I abp)) (abr :: TyPi abp (N abp abq)) :: * where
  Exist2 ::
    forall (abj :: *) (abk :: TyPi abj (I abj)) (abl :: TyPi abj (N abj abk)) (abm :: abj) (abn :: abk @@@ abm) (abo ::
    abl @@@ abm). (Sing * abj) -> (Sing (TyPi abj (I abj)) abk) -> (Sing (TyPi abj (N abj abk)) abl) -> (Sing abj abm)
    -> (Sing (abk @@@ abm) abn) -> (Sing (abl @@@ abm) abo) -> Sig2 abj abk abl
$(P.return [])
data instance Sing (Sig2 acf acg ach) ace where
  SExist2 ::
    forall (abs :: *) (abt :: TyPi abs (I abs)) (abu :: TyPi abs (N abs abt)) (abv :: abs) (abw :: abt @@@ abv) (abx ::
    abu @@@ abv) (aby :: Sing * abs) (abz :: Sing (TyPi abs (I abs)) abt) (aca :: Sing (TyPi abs (N abs abt)) abu) (acb
    :: Sing abs abv) (acc :: Sing (abt @@@ abv) abw) (acd :: Sing (abu @@@ abv) abx). (Sing * abs) -> (Sing (TyPi abs
    (I abs)) abt) -> (Sing (TyPi abs (N abs abt)) abu) -> (Sing abs abv) -> (Sing (abt @@@ abv) abw) -> (Sing (abu @@@
    abv) abx) -> Sing' ('Exist2 aby abz aca acb acc acd)
$(P.return [])
data CC (aci :: TyFun' * *)
$(P.return [])
data CE (ack :: *) (acj :: TyFun' (TyPi ack (I ack)) *)
$(P.return [])
data CG (acn :: *) (acm :: TyPi acn (I acn)) (acl :: TyFun' (TyPi acn (N acn acm)) *)
$(P.return [])
type instance (@@) (CG acq acp) aco = *
$(P.return [])
type instance (@@) (CE acs) acr = TyPi (TyPi acs (N acs acr)) (CG acs acr)
$(P.return [])
type instance (@@) CC act = TyPi (TyPi act (I act)) (CE act)
$(P.return [])
data CB (acu :: TyPi' * CC)
$(P.return [])
data CD (acw :: *) (acv :: TyPi' (TyPi acw (I acw)) (CE acw))
$(P.return [])
type instance (@@@) CB acx = CD acx
$(P.return [])
data CF (ada :: *) (acz :: TyPi ada (I ada)) (acy :: TyPi' (TyPi ada (N ada acz)) (CG ada acz))
$(P.return [])
type instance (@@@) (CD adc) adb = CF adc adb
$(P.return [])
type instance (@@@) (CF adf ade) add = Sig2 adf ade add
$(P.return [])
data Sig (adk :: *) (adl :: TyPi adk (I adk)) :: * where
  Exist ::
    forall (adg :: *) (adh :: TyPi adg (I adg)) (adi :: adg) (adj :: adh @@@ adi). (Sing * adg) -> (Sing (TyPi adg (I
    adg)) adh) -> (Sing adg adi) -> (Sing (adh @@@ adi) adj) -> Sig adg adh
$(P.return [])
data instance Sing (Sig adv adw) adu where
  SExist ::
    forall (adm :: *) (adn :: TyPi adm (I adm)) (ado :: adm) (adp :: adn @@@ ado) (adq :: Sing * adm) (adr :: Sing
    (TyPi adm (I adm)) adn) (ads :: Sing adm ado) (adt :: Sing (adn @@@ ado) adp). (Sing * adm) -> (Sing (TyPi adm (I
    adm)) adn) -> (Sing adm ado) -> (Sing (adn @@@ ado) adp) -> Sing' ('Exist adq adr ads adt)
$(P.return [])
data BY (adx :: TyFun' * *)
$(P.return [])
data CA (adz :: *) (ady :: TyFun' (TyPi adz (I adz)) *)
$(P.return [])
type instance (@@) (CA aeb) aea = *
$(P.return [])
type instance (@@) BY aec = TyPi (TyPi aec (I aec)) (CA aec)
$(P.return [])
data BX (aed :: TyPi' * BY)
$(P.return [])
data BZ (aef :: *) (aee :: TyPi' (TyPi aef (I aef)) (CA aef))
$(P.return [])
type instance (@@@) BX aeg = BZ aeg
$(P.return [])
type instance (@@@) (BZ aei) aeh = Sig aei aeh
$(P.return [])
data Le (aem :: Nat) (aen :: Nat) :: * where
  Le_n ::   forall (aej :: Nat). (Sing Nat aej) -> Le aej aej
  Le_S ::   forall (aek :: Nat) (ael :: Nat). (Sing Nat aek) -> (Sing Nat ael) -> (Le aek ael) -> Le aek ('S ael)
$(P.return [])
data instance Sing (Le aew aex) aev where
  SLe_n ::   forall (aeo :: Nat) (aep :: Sing Nat aeo). (Sing Nat aeo) -> Sing' ('Le_n aep)
  SLe_S ::
    forall (aeq :: Nat) (aer :: Nat) (aes :: Sing Nat aeq) (aet :: Sing Nat aer) (aeu :: Le aeq aer). (Sing Nat aeq) ->
    (Sing Nat aer) -> (Sing (Le aeq aer) aeu) -> Sing' ('Le_S aes aet aeu)
$(P.return [])
data BU (aey :: TyFun' Nat *)
$(P.return [])
data BW (afa :: Nat) (aez :: TyFun' Nat *)
$(P.return [])
type instance (@@) (BW afc) afb = *
$(P.return [])
type instance (@@) BU afd = TyPi Nat (BW afd)
$(P.return [])
data BT (afe :: TyPi' Nat BU)
$(P.return [])
data BV (afg :: Nat) (aff :: TyPi' Nat (BW afg))
$(P.return [])
type instance (@@@) BT afh = BV afh
$(P.return [])
type instance (@@@) (BV afj) afi = Le afj afi
$(P.return [])
data Identity (afm :: *) (afn :: afm) (afo :: afm) :: * where
  Identity_refl ::   forall (afk :: *) (afl :: afk). (Sing * afk) -> (Sing afk afl) -> Identity afk afl afl
$(P.return [])
data instance Sing (Identity afu afv afw) aft where
  SIdentity_refl ::
    forall (afp :: *) (afq :: afp) (afr :: Sing * afp) (afs :: Sing afp afq). (Sing * afp) -> (Sing afp afq) -> Sing'
    ('Identity_refl afr afs)
$(P.return [])
data BO (afx :: TyFun' * *)
$(P.return [])
data BQ (afz :: *) (afy :: TyFun' afz *)
$(P.return [])
data BS (agc :: *) (agb :: agc) (aga :: TyFun' agc *)
$(P.return [])
type instance (@@) (BS agf age) agd = *
$(P.return [])
type instance (@@) (BQ agh) agg = TyPi agh (BS agh agg)
$(P.return [])
type instance (@@) BO agi = TyPi agi (BQ agi)
$(P.return [])
data BN (agj :: TyPi' * BO)
$(P.return [])
data BP (agl :: *) (agk :: TyPi' agl (BQ agl))
$(P.return [])
type instance (@@@) BN agm = BP agm
$(P.return [])
data BR (agp :: *) (ago :: agp) (agn :: TyPi' agp (BS agp ago))
$(P.return [])
type instance (@@@) (BP agr) agq = BR agr agq
$(P.return [])
type instance (@@@) (BR agu agt) ags = Identity agu agt ags
$(P.return [])
data Comparison :: * where
  Eq ::   Comparison
  Lt ::   Comparison
  Gt ::   Comparison
$(P.return [])
data CompareSpecT (ahh :: *) (ahi :: *) (ahj :: *) (ahk :: Comparison) :: * where
  CompEqT ::
    forall (agv :: *) (agw :: *) (agx :: *) (agy :: agv). (Sing * agv) -> (Sing * agw) -> (Sing * agx) -> (Sing agv
    agy) -> CompareSpecT agv agw agx 'Eq
  CompLtT ::
    forall (agz :: *) (aha :: *) (ahb :: *) (ahc :: aha). (Sing * agz) -> (Sing * aha) -> (Sing * ahb) -> (Sing aha
    ahc) -> CompareSpecT agz aha ahb 'Lt
  CompGtT ::
    forall (ahd :: *) (ahe :: *) (ahf :: *) (ahg :: ahf). (Sing * ahd) -> (Sing * ahe) -> (Sing * ahf) -> (Sing ahf
    ahg) -> CompareSpecT ahd ahe ahf 'Gt
$(P.return [])
data instance Sing (CompareSpecT aik ail aim ain) aij where
  SCompEqT ::
    forall (ahl :: *) (ahm :: *) (ahn :: *) (aho :: ahl) (ahp :: Sing * ahl) (ahq :: Sing * ahm) (ahr :: Sing * ahn)
    (ahs :: Sing ahl aho). (Sing * ahl) -> (Sing * ahm) -> (Sing * ahn) -> (Sing ahl aho) -> Sing' ('CompEqT ahp ahq
    ahr ahs)
  SCompLtT ::
    forall (aht :: *) (ahu :: *) (ahv :: *) (ahw :: ahu) (ahx :: Sing * aht) (ahy :: Sing * ahu) (ahz :: Sing * ahv)
    (aia :: Sing ahu ahw). (Sing * aht) -> (Sing * ahu) -> (Sing * ahv) -> (Sing ahu ahw) -> Sing' ('CompLtT ahx ahy
    ahz aia)
  SCompGtT ::
    forall (aib :: *) (aic :: *) (aid :: *) (aie :: aid) (aif :: Sing * aib) (aig :: Sing * aic) (aih :: Sing * aid)
    (aii :: Sing aid aie). (Sing * aib) -> (Sing * aic) -> (Sing * aid) -> (Sing aid aie) -> Sing' ('CompGtT aif aig
    aih aii)
$(P.return [])
data BG (aio :: TyFun' * *)
$(P.return [])
data BI (aiq :: *) (aip :: TyFun' * *)
$(P.return [])
data BK (ait :: *) (ais :: *) (air :: TyFun' * *)
$(P.return [])
data BM (aix :: *) (aiw :: *) (aiv :: *) (aiu :: TyFun' Comparison *)
$(P.return [])
type instance (@@) (BM ajb aja aiz) aiy = *
$(P.return [])
type instance (@@) (BK aje ajd) ajc = TyPi Comparison (BM aje ajd ajc)
$(P.return [])
type instance (@@) (BI ajg) ajf = TyPi * (BK ajg ajf)
$(P.return [])
type instance (@@) BG ajh = TyPi * (BI ajh)
$(P.return [])
data BF (aji :: TyPi' * BG)
$(P.return [])
data BH (ajk :: *) (ajj :: TyPi' * (BI ajk))
$(P.return [])
type instance (@@@) BF ajl = BH ajl
$(P.return [])
data BJ (ajo :: *) (ajn :: *) (ajm :: TyPi' * (BK ajo ajn))
$(P.return [])
type instance (@@@) (BH ajq) ajp = BJ ajq ajp
$(P.return [])
data BL (aju :: *) (ajt :: *) (ajs :: *) (ajr :: TyPi' Comparison (BM aju ajt ajs))
$(P.return [])
type instance (@@@) (BJ ajx ajw) ajv = BL ajx ajw ajv
$(P.return [])
type instance (@@@) (BL akb aka ajz) ajy = CompareSpecT akb aka ajz ajy
$(P.return [])
data CompareSpec (ako :: *) (akp :: *) (akq :: *) (akr :: Comparison) :: * where
  CompEq ::
    forall (akc :: *) (akd :: *) (ake :: *) (akf :: akc). (Sing * akc) -> (Sing * akd) -> (Sing * ake) -> (Sing akc
    akf) -> CompareSpec akc akd ake 'Eq
  CompLt ::
    forall (akg :: *) (akh :: *) (aki :: *) (akj :: akh). (Sing * akg) -> (Sing * akh) -> (Sing * aki) -> (Sing akh
    akj) -> CompareSpec akg akh aki 'Lt
  CompGt ::
    forall (akk :: *) (akl :: *) (akm :: *) (akn :: akm). (Sing * akk) -> (Sing * akl) -> (Sing * akm) -> (Sing akm
    akn) -> CompareSpec akk akl akm 'Gt
$(P.return [])
data instance Sing (CompareSpec alr als alt alu) alq where
  SCompEq ::
    forall (aks :: *) (akt :: *) (aku :: *) (akv :: aks) (akw :: Sing * aks) (akx :: Sing * akt) (aky :: Sing * aku)
    (akz :: Sing aks akv). (Sing * aks) -> (Sing * akt) -> (Sing * aku) -> (Sing aks akv) -> Sing' ('CompEq akw akx aky
    akz)
  SCompLt ::
    forall (ala :: *) (alb :: *) (alc :: *) (ald :: alb) (ale :: Sing * ala) (alf :: Sing * alb) (alg :: Sing * alc)
    (alh :: Sing alb ald). (Sing * ala) -> (Sing * alb) -> (Sing * alc) -> (Sing alb ald) -> Sing' ('CompLt ale alf alg
    alh)
  SCompGt ::
    forall (ali :: *) (alj :: *) (alk :: *) (all :: alk) (alm :: Sing * ali) (aln :: Sing * alj) (alo :: Sing * alk)
    (alp :: Sing alk all). (Sing * ali) -> (Sing * alj) -> (Sing * alk) -> (Sing alk all) -> Sing' ('CompGt alm aln alo
    alp)
$(P.return [])
data AY (alv :: TyFun' * *)
$(P.return [])
data BA (alx :: *) (alw :: TyFun' * *)
$(P.return [])
data BC (ama :: *) (alz :: *) (aly :: TyFun' * *)
$(P.return [])
data BE (ame :: *) (amd :: *) (amc :: *) (amb :: TyFun' Comparison *)
$(P.return [])
type instance (@@) (BE ami amh amg) amf = *
$(P.return [])
type instance (@@) (BC aml amk) amj = TyPi Comparison (BE aml amk amj)
$(P.return [])
type instance (@@) (BA amn) amm = TyPi * (BC amn amm)
$(P.return [])
type instance (@@) AY amo = TyPi * (BA amo)
$(P.return [])
data AX (amp :: TyPi' * AY)
$(P.return [])
data AZ (amr :: *) (amq :: TyPi' * (BA amr))
$(P.return [])
type instance (@@@) AX ams = AZ ams
$(P.return [])
data BB (amv :: *) (amu :: *) (amt :: TyPi' * (BC amv amu))
$(P.return [])
type instance (@@@) (AZ amx) amw = BB amx amw
$(P.return [])
data BD (anb :: *) (ana :: *) (amz :: *) (amy :: TyPi' Comparison (BE anb ana amz))
$(P.return [])
type instance (@@@) (BB ane and) anc = BD ane and anc
$(P.return [])
type instance (@@@) (BD ani anh ang) anf = CompareSpec ani anh ang anf
$(P.return [])
data instance Sing Comparison anj where
  SEq ::   Sing' 'Eq
  SLt ::   Sing' 'Lt
  SGt ::   Sing' 'Gt
$(P.return [])
data List (ann :: *) :: * where
  Nil ::   forall (ank :: *). (Sing * ank) -> List ank
  Cons ::   forall (anl :: *) (anm :: anl). (Sing * anl) -> (Sing anl anm) -> (List anl) -> List anl
$(P.return [])
data instance Sing (List anw) anv where
  SNil ::   forall (ano :: *) (anp :: Sing * ano). (Sing * ano) -> Sing' ('Nil anp)
  SCons ::
    forall (anq :: *) (anr :: anq) (ans :: Sing * anq) (ant :: Sing anq anr) (anu :: List anq). (Sing * anq) -> (Sing
    anq anr) -> (Sing (List anq) anu) -> Sing' ('Cons ans ant anu)
$(P.return [])
data AW (anx :: TyFun' * *)
$(P.return [])
type instance (@@) AW any = *
$(P.return [])
data AV (anz :: TyPi' * AW)
$(P.return [])
type instance (@@@) AV aoa = List aoa
$(P.return [])
data Prod (aof :: *) (aog :: *) :: * where
  Pair ::
    forall (aob :: *) (aoc :: *) (aod :: aob) (aoe :: aoc). (Sing * aob) -> (Sing * aoc) -> (Sing aob aod) -> (Sing aoc
    aoe) -> Prod aob aoc
$(P.return [])
data instance Sing (Prod aoq aor) aop where
  SPair ::
    forall (aoh :: *) (aoi :: *) (aoj :: aoh) (aok :: aoi) (aol :: Sing * aoh) (aom :: Sing * aoi) (aon :: Sing aoh
    aoj) (aoo :: Sing aoi aok). (Sing * aoh) -> (Sing * aoi) -> (Sing aoh aoj) -> (Sing aoi aok) -> Sing' ('Pair aol
    aom aon aoo)
$(P.return [])
data AS (aos :: TyFun' * *)
$(P.return [])
data AU (aou :: *) (aot :: TyFun' * *)
$(P.return [])
type instance (@@) (AU aow) aov = *
$(P.return [])
type instance (@@) AS aox = TyPi * (AU aox)
$(P.return [])
data AR (aoy :: TyPi' * AS)
$(P.return [])
data AT (apa :: *) (aoz :: TyPi' * (AU apa))
$(P.return [])
type instance (@@@) AR apb = AT apb
$(P.return [])
type instance (@@@) (AT apd) apc = Prod apd apc
$(P.return [])
data Sum (apk :: *) (apl :: *) :: * where
  Inl ::   forall (ape :: *) (apf :: *) (apg :: ape). (Sing * ape) -> (Sing * apf) -> (Sing ape apg) -> Sum ape apf
  Inr ::   forall (aph :: *) (api :: *) (apj :: api). (Sing * aph) -> (Sing * api) -> (Sing api apj) -> Sum aph api
$(P.return [])
data instance Sing (Sum apz aqa) apy where
  SInl ::
    forall (apm :: *) (apn :: *) (apo :: apm) (app :: Sing * apm) (apq :: Sing * apn) (apr :: Sing apm apo). (Sing *
    apm) -> (Sing * apn) -> (Sing apm apo) -> Sing' ('Inl app apq apr)
  SInr ::
    forall (aps :: *) (apt :: *) (apu :: apt) (apv :: Sing * aps) (apw :: Sing * apt) (apx :: Sing apt apu). (Sing *
    aps) -> (Sing * apt) -> (Sing apt apu) -> Sing' ('Inr apv apw apx)
$(P.return [])
data AO (aqb :: TyFun' * *)
$(P.return [])
data AQ (aqd :: *) (aqc :: TyFun' * *)
$(P.return [])
type instance (@@) (AQ aqf) aqe = *
$(P.return [])
type instance (@@) AO aqg = TyPi * (AQ aqg)
$(P.return [])
data AN (aqh :: TyPi' * AO)
$(P.return [])
data AP (aqj :: *) (aqi :: TyPi' * (AQ aqj))
$(P.return [])
type instance (@@@) AN aqk = AP aqk
$(P.return [])
type instance (@@@) (AP aqm) aql = Sum aqm aql
$(P.return [])
data Option (aqq :: *) :: * where
  Some ::   forall (aqn :: *) (aqo :: aqn). (Sing * aqn) -> (Sing aqn aqo) -> Option aqn
  None ::   forall (aqp :: *). (Sing * aqp) -> Option aqp
$(P.return [])
data instance Sing (Option aqy) aqx where
  SSome ::
    forall (aqr :: *) (aqs :: aqr) (aqt :: Sing * aqr) (aqu :: Sing aqr aqs). (Sing * aqr) -> (Sing aqr aqs) -> Sing'
    ('Some aqt aqu)
  SNone ::   forall (aqv :: *) (aqw :: Sing * aqv). (Sing * aqv) -> Sing' ('None aqw)
$(P.return [])
data AM (aqz :: TyFun' * *)
$(P.return [])
type instance (@@) AM ara = *
$(P.return [])
data AL (arb :: TyPi' * AM)
$(P.return [])
type instance (@@@) AL arc = Option arc
$(P.return [])
data instance Sing Nat are where
  SO ::   Sing' 'O
  SS ::   forall (ard :: Nat). (Sing Nat ard) -> Sing' ('S ard)
$(P.return [])
data Bool :: * where
  True ::   Bool
  False ::   Bool
$(P.return [])
data BoolSpec (arl :: *) (arm :: *) (arn :: Bool) :: * where
  BoolSpecT ::
    forall (arf :: *) (arg :: *) (arh :: arf). (Sing * arf) -> (Sing * arg) -> (Sing arf arh) -> BoolSpec arf arg 'True
  BoolSpecF ::
    forall (ari :: *) (arj :: *) (ark :: arj). (Sing * ari) -> (Sing * arj) -> (Sing arj ark) -> BoolSpec ari arj
    'False
$(P.return [])
data instance Sing (BoolSpec asb asc asd) asa where
  SBoolSpecT ::
    forall (aro :: *) (arp :: *) (arq :: aro) (arr :: Sing * aro) (ars :: Sing * arp) (art :: Sing aro arq). (Sing *
    aro) -> (Sing * arp) -> (Sing aro arq) -> Sing' ('BoolSpecT arr ars art)
  SBoolSpecF ::
    forall (aru :: *) (arv :: *) (arw :: arv) (arx :: Sing * aru) (ary :: Sing * arv) (arz :: Sing arv arw). (Sing *
    aru) -> (Sing * arv) -> (Sing arv arw) -> Sing' ('BoolSpecF arx ary arz)
$(P.return [])
data AG (ase :: TyFun' * *)
$(P.return [])
data AI (asg :: *) (asf :: TyFun' * *)
$(P.return [])
data AK (asj :: *) (asi :: *) (ash :: TyFun' Bool *)
$(P.return [])
type instance (@@) (AK asm asl) ask = *
$(P.return [])
type instance (@@) (AI aso) asn = TyPi Bool (AK aso asn)
$(P.return [])
type instance (@@) AG asp = TyPi * (AI asp)
$(P.return [])
data AF (asq :: TyPi' * AG)
$(P.return [])
data AH (ass :: *) (asr :: TyPi' * (AI ass))
$(P.return [])
type instance (@@@) AF ast = AH ast
$(P.return [])
data AJ (asw :: *) (asv :: *) (asu :: TyPi' Bool (AK asw asv))
$(P.return [])
type instance (@@@) (AH asy) asx = AJ asy asx
$(P.return [])
type instance (@@@) (AJ atb ata) asz = BoolSpec atb ata asz
$(P.return [])
data Eq_true (atc :: Bool) :: * where
  Is_eq_true ::   Eq_true 'True
$(P.return [])
data instance Sing (Eq_true ate) atd where
  SIs_eq_true ::   Sing' 'Is_eq_true
$(P.return [])
data AE (atf :: TyFun' Bool *)
$(P.return [])
type instance (@@) AE atg = *
$(P.return [])
data AD (ath :: TyPi' Bool AE)
$(P.return [])
type instance (@@@) AD ati = Eq_true ati
$(P.return [])
data instance Sing Bool atj where
  STrue ::   Sing' 'True
  SFalse ::   Sing' 'False
$(P.return [])
data Unit :: * where
  Tt ::   Unit
$(P.return [])
data instance Sing Unit atk where
  STt ::   Sing' 'Tt
$(P.return [])
data Empty_set :: * where
  
$(P.return [])
data instance Sing Empty_set atl where
  
$(P.return [])
data Inhabited (ato :: *) :: * where
  Inhabits ::   forall (atm :: *) (atn :: atm). (Sing * atm) -> (Sing atm atn) -> Inhabited atm
$(P.return [])
data instance Sing (Inhabited atu) att where
  SInhabits ::
    forall (atp :: *) (atq :: atp) (atr :: Sing * atp) (ats :: Sing atp atq). (Sing * atp) -> (Sing atp atq) -> Sing'
    ('Inhabits atr ats)
$(P.return [])
data AC (atv :: TyFun' * *)
$(P.return [])
type instance (@@) AC atw = *
$(P.return [])
data AB (atx :: TyPi' * AC)
$(P.return [])
type instance (@@@) AB aty = Inhabited aty
$(P.return [])
data Eq (aub :: *) (auc :: aub) (aud :: aub) :: * where
  Eq_refl ::   forall (atz :: *) (aua :: atz). (Sing * atz) -> (Sing atz aua) -> Eq atz aua aua
$(P.return [])
data instance Sing (Eq auj auk aul) aui where
  SEq_refl ::
    forall (aue :: *) (auf :: aue) (aug :: Sing * aue) (auh :: Sing aue auf). (Sing * aue) -> (Sing aue auf) -> Sing'
    ('Eq_refl aug auh)
$(P.return [])
data W (aum :: TyFun' * *)
$(P.return [])
data Y (auo :: *) (aun :: TyFun' auo *)
$(P.return [])
data AA (aur :: *) (auq :: aur) (aup :: TyFun' aur *)
$(P.return [])
type instance (@@) (AA auu aut) aus = *
$(P.return [])
type instance (@@) (Y auw) auv = TyPi auw (AA auw auv)
$(P.return [])
type instance (@@) W aux = TyPi aux (Y aux)
$(P.return [])
data V (auy :: TyPi' * W)
$(P.return [])
data X (ava :: *) (auz :: TyPi' ava (Y ava))
$(P.return [])
type instance (@@@) V avb = X avb
$(P.return [])
data Z (ave :: *) (avd :: ave) (avc :: TyPi' ave (AA ave avd))
$(P.return [])
type instance (@@@) (X avg) avf = Z avg avf
$(P.return [])
type instance (@@@) (Z avj avi) avh = Eq avj avi avh
$(P.return [])
data Ex2 (avq :: *) (avr :: TyPi avq (I avq)) (avs :: TyPi avq (N avq avr)) :: * where
  Ex_intro2 ::
    forall (avk :: *) (avl :: TyPi avk (I avk)) (avm :: TyPi avk (N avk avl)) (avn :: avk) (avo :: avl @@@ avn) (avp ::
    avm @@@ avn). (Sing * avk) -> (Sing (TyPi avk (I avk)) avl) -> (Sing (TyPi avk (N avk avl)) avm) -> (Sing avk avn)
    -> (Sing (avl @@@ avn) avo) -> (Sing (avm @@@ avn) avp) -> Ex2 avk avl avm
$(P.return [])
data instance Sing (Ex2 awg awh awi) awf where
  SEx_intro2 ::
    forall (avt :: *) (avu :: TyPi avt (I avt)) (avv :: TyPi avt (N avt avu)) (avw :: avt) (avx :: avu @@@ avw) (avy ::
    avv @@@ avw) (avz :: Sing * avt) (awa :: Sing (TyPi avt (I avt)) avu) (awb :: Sing (TyPi avt (N avt avu)) avv) (awc
    :: Sing avt avw) (awd :: Sing (avu @@@ avw) avx) (awe :: Sing (avv @@@ avw) avy). (Sing * avt) -> (Sing (TyPi avt
    (I avt)) avu) -> (Sing (TyPi avt (N avt avu)) avv) -> (Sing avt avw) -> (Sing (avu @@@ avw) avx) -> (Sing (avv @@@
    avw) avy) -> Sing' ('Ex_intro2 avz awa awb awc awd awe)
$(P.return [])
data P (awj :: TyFun' * *)
$(P.return [])
data R (awl :: *) (awk :: TyFun' (TyPi awl (I awl)) *)
$(P.return [])
data U (awo :: *) (awn :: TyPi awo (I awo)) (awm :: TyFun' (TyPi awo (N awo awn)) *)
$(P.return [])
type instance (@@) (U awr awq) awp = *
$(P.return [])
type instance (@@) (R awt) aws = TyPi (TyPi awt (N awt aws)) (U awt aws)
$(P.return [])
type instance (@@) P awu = TyPi (TyPi awu (I awu)) (R awu)
$(P.return [])
data O (awv :: TyPi' * P)
$(P.return [])
data Q (awx :: *) (aww :: TyPi' (TyPi awx (I awx)) (R awx))
$(P.return [])
type instance (@@@) O awy = Q awy
$(P.return [])
data S (axb :: *) (axa :: TyPi axb (I axb)) (awz :: TyPi' (TyPi axb (N axb axa)) (U axb axa))
$(P.return [])
type instance (@@@) (Q axd) axc = S axd axc
$(P.return [])
type instance (@@@) (S axg axf) axe = Ex2 axg axf axe
$(P.return [])
data Ex (axl :: *) (axm :: TyPi axl (I axl)) :: * where
  Ex_intro ::
    forall (axh :: *) (axi :: TyPi axh (I axh)) (axj :: axh) (axk :: axi @@@ axj). (Sing * axh) -> (Sing (TyPi axh (I
    axh)) axi) -> (Sing axh axj) -> (Sing (axi @@@ axj) axk) -> Ex axh axi
$(P.return [])
data instance Sing (Ex axw axx) axv where
  SEx_intro ::
    forall (axn :: *) (axo :: TyPi axn (I axn)) (axp :: axn) (axq :: axo @@@ axp) (axr :: Sing * axn) (axs :: Sing
    (TyPi axn (I axn)) axo) (axt :: Sing axn axp) (axu :: Sing (axo @@@ axp) axq). (Sing * axn) -> (Sing (TyPi axn (I
    axn)) axo) -> (Sing axn axp) -> (Sing (axo @@@ axp) axq) -> Sing' ('Ex_intro axr axs axt axu)
$(P.return [])
data K (axy :: TyFun' * *)
$(P.return [])
data M (aya :: *) (axz :: TyFun' (TyPi aya (I aya)) *)
$(P.return [])
type instance (@@) (M ayc) ayb = *
$(P.return [])
type instance (@@) K ayd = TyPi (TyPi ayd (I ayd)) (M ayd)
$(P.return [])
data J (aye :: TyPi' * K)
$(P.return [])
data L (ayg :: *) (ayf :: TyPi' (TyPi ayg (I ayg)) (M ayg))
$(P.return [])
type instance (@@@) J ayh = L ayh
$(P.return [])
type instance (@@@) (L ayj) ayi = Ex ayj ayi
$(P.return [])
data Or (ayq :: *) (ayr :: *) :: * where
  Or_introl ::
    forall (ayk :: *) (ayl :: *) (aym :: ayk). (Sing * ayk) -> (Sing * ayl) -> (Sing ayk aym) -> Or ayk ayl
  Or_intror ::
    forall (ayn :: *) (ayo :: *) (ayp :: ayo). (Sing * ayn) -> (Sing * ayo) -> (Sing ayo ayp) -> Or ayn ayo
$(P.return [])
data instance Sing (Or azf azg) aze where
  SOr_introl ::
    forall (ays :: *) (ayt :: *) (ayu :: ays) (ayv :: Sing * ays) (ayw :: Sing * ayt) (ayx :: Sing ays ayu). (Sing *
    ays) -> (Sing * ayt) -> (Sing ays ayu) -> Sing' ('Or_introl ayv ayw ayx)
  SOr_intror ::
    forall (ayy :: *) (ayz :: *) (aza :: ayz) (azb :: Sing * ayy) (azc :: Sing * ayz) (azd :: Sing ayz aza). (Sing *
    ayy) -> (Sing * ayz) -> (Sing ayz aza) -> Sing' ('Or_intror azb azc azd)
$(P.return [])
data F (azh :: TyFun' * *)
$(P.return [])
data H (azj :: *) (azi :: TyFun' * *)
$(P.return [])
type instance (@@) (H azl) azk = *
$(P.return [])
type instance (@@) F azm = TyPi * (H azm)
$(P.return [])
data E (azn :: TyPi' * F)
$(P.return [])
data G (azp :: *) (azo :: TyPi' * (H azp))
$(P.return [])
type instance (@@@) E azq = G azq
$(P.return [])
type instance (@@@) (G azs) azr = Or azs azr
$(P.return [])
data And (azx :: *) (azy :: *) :: * where
  Conj ::
    forall (azt :: *) (azu :: *) (azv :: azt) (azw :: azu). (Sing * azt) -> (Sing * azu) -> (Sing azt azv) -> (Sing azu
    azw) -> And azt azu
$(P.return [])
data instance Sing (And bai baj) bah where
  SConj ::
    forall (azz :: *) (baa :: *) (bab :: azz) (bac :: baa) (bad :: Sing * azz) (bae :: Sing * baa) (baf :: Sing azz
    bab) (bag :: Sing baa bac). (Sing * azz) -> (Sing * baa) -> (Sing azz bab) -> (Sing baa bac) -> Sing' ('Conj bad
    bae baf bag)
$(P.return [])
data B (bak :: TyFun' * *)
$(P.return [])
data D (bam :: *) (bal :: TyFun' * *)
$(P.return [])
type instance (@@) (D bao) ban = *
$(P.return [])
type instance (@@) B bap = TyPi * (D bap)
$(P.return [])
data A (baq :: TyPi' * B)
$(P.return [])
data C (bas :: *) (bar :: TyPi' * (D bas))
$(P.return [])
type instance (@@@) A bat = C bat
$(P.return [])
type instance (@@@) (C bav) bau = And bav bau
$(P.return [])
data False :: * where
  
$(P.return [])
data instance Sing False baw where
  
$(P.return [])
data True :: * where
  I ::   True
$(P.return [])
data instance Sing True bax where
  SI ::   Sing' 'I
