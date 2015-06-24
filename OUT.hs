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
data HU (b :: Nat) (a :: TyFun' (Sing Nat b) *)
$(P.return [])
data T (e :: Nat) :: * where
  F1 ::   forall (c :: Nat). (Sing Nat c) -> T ('S {- KIND -} c)
  FS ::   forall (d :: Nat). (Sing Nat d) -> (T {- KIND -} d) -> T ('S {- KIND -} d)
$(P.return [])
data HW (h :: Nat) (g :: Sing Nat h) (f :: TyFun' (T h) *)
$(P.return [])
type instance (@@) (HW k j) i = T ('S k)
$(P.return [])
type instance (@@) (HU m) l = TyPi (T m) (HW m l)
$(P.return [])
data HT (o :: Nat) (n :: TyPi' (Sing Nat o) (HU o))
$(P.return [])
data HV (r :: Nat) (q :: Sing Nat r) (p :: TyPi' (T r) (HW r q))
$(P.return [])
type instance (@@@) (HT t) s = HV t s
$(P.return [])
type instance (@@@) (HV w v) u = 'FS v u
$(P.return [])
data HS (y :: Nat) (x :: TyFun' (Sing Nat y) *)
$(P.return [])
type instance (@@) (HS aa) z = T ('S aa)
$(P.return [])
data HR (ac :: Nat) (ab :: TyPi' (Sing Nat ac) (HS ac))
$(P.return [])
type instance (@@@) (HR ae) ad = 'F1 ad
$(P.return [])
data instance Sing (T al) ak where
  SF1 ::   forall (af :: Nat) (ag :: Sing Nat af). (Sing Nat af) -> Sing' ('F1 ag)
  SFS ::   forall (ah :: Nat) (ai :: Sing Nat ah) (aj :: T ah). (Sing Nat ah) -> (Sing (T ah) aj) -> Sing' ('FS ai aj)
$(P.return [])
data HP (am :: TyFun' Nat *)
$(P.return [])
type instance (@@) HP an = *
$(P.return [])
data HO (ao :: TyPi' Nat HP)
$(P.return [])
type instance (@@@) HO ap = T ap
$(P.return [])
data HK (as :: *) (ar :: as) (aq :: TyFun' (Sing * as) *)
$(P.return [])
data HM (aw :: *) (av :: aw) (au :: Sing * aw) (at :: TyFun' (Sing aw av) *)
$(P.return [])
data Identity (az :: *) (ba :: az) (bb :: az) :: * where
  Identity_refl ::
    forall (ax :: *) (ay :: ax). (Sing * ax) -> (Sing ax ay) -> Identity {- KIND -} ax {- KIND -} ay {- KIND -} ay
$(P.return [])
type instance (@@) (HM bf be bd) bc = Identity bf be be
$(P.return [])
type instance (@@) (HK bi bh) bg = TyPi (Sing bi bh) (HM bi bh bg)
$(P.return [])
data HJ (bl :: *) (bk :: bl) (bj :: TyPi' (Sing * bl) (HK bl bk))
$(P.return [])
data HL (bp :: *) (bo :: bp) (bn :: Sing * bp) (bm :: TyPi' (Sing bp bo) (HM bp bo bn))
$(P.return [])
type instance (@@@) (HJ bs br) bq = HL bs br bq
$(P.return [])
type instance (@@@) (HL bw bv bu) bt = 'Identity_refl bu bt
$(P.return [])
data instance Sing (Identity cc cd ce) cb where
  SIdentity_refl ::
    forall (bx :: *) (by :: bx) (bz :: Sing * bx) (ca :: Sing bx by). (Sing * bx) -> (Sing bx by) -> Sing'
    ('Identity_refl bz ca)
$(P.return [])
data HE (cf :: TyFun' * *)
$(P.return [])
data HG (ch :: *) (cg :: TyFun' ch *)
$(P.return [])
data HI (ck :: *) (cj :: ck) (ci :: TyFun' ck *)
$(P.return [])
type instance (@@) (HI cn cm) cl = *
$(P.return [])
type instance (@@) (HG cp) co = TyPi cp (HI cp co)
$(P.return [])
type instance (@@) HE cq = TyPi cq (HG cq)
$(P.return [])
data HD (cr :: TyPi' * HE)
$(P.return [])
data HF (ct :: *) (cs :: TyPi' ct (HG ct))
$(P.return [])
type instance (@@@) HD cu = HF cu
$(P.return [])
data HH (cx :: *) (cw :: cx) (cv :: TyPi' cx (HI cx cw))
$(P.return [])
type instance (@@@) (HF cz) cy = HH cz cy
$(P.return [])
type instance (@@@) (HH dc db) da = Identity dc db da
$(P.return [])
data GW (dh :: *) (dg :: *) (df :: *) (de :: df) (dd :: TyFun' (Sing * dh) *)
$(P.return [])
data GY (dn :: *) (dm :: *) (dl :: *) (dk :: dl) (dj :: Sing * dn) (di :: TyFun' (Sing * dm) *)
$(P.return [])
data HA (dv :: *) (du :: *) (dt :: *) (ds :: dt) (dr :: Sing * dv) (dq :: Sing * du) (dp :: TyFun' (Sing * dt) *)
$(P.return [])
data HC (ed :: *) (ec :: *) (eb :: *) (ea :: eb) (dz :: Sing * ed) (dy :: Sing * ec) (dx :: Sing * eb) (dw :: TyFun' (Sing eb ea) *)
$(P.return [])
data Comparison :: * where
  Eq ::   Comparison
  Lt ::   Comparison
  Gt ::   Comparison
$(P.return [])
data CompareSpecT (eq :: *) (er :: *) (es :: *) (et :: Comparison) :: * where
  CompEqT ::
    forall (ee :: *) (ef :: *) (eg :: *) (eh :: ee). (Sing * ee) -> (Sing * ef) -> (Sing * eg) -> (Sing ee eh) ->
    CompareSpecT {- KIND -} ee {- KIND -} ef {- KIND -} eg 'Eq
  CompLtT ::
    forall (ei :: *) (ej :: *) (ek :: *) (el :: ej). (Sing * ei) -> (Sing * ej) -> (Sing * ek) -> (Sing ej el) ->
    CompareSpecT {- KIND -} ei {- KIND -} ej {- KIND -} ek 'Lt
  CompGtT ::
    forall (em :: *) (en :: *) (eo :: *) (ep :: eo). (Sing * em) -> (Sing * en) -> (Sing * eo) -> (Sing eo ep) ->
    CompareSpecT {- KIND -} em {- KIND -} en {- KIND -} eo 'Gt
$(P.return [])
type instance (@@) (HC fb fa ez ey ex ew ev) eu = CompareSpecT fb fa ez 'Gt
$(P.return [])
type instance (@@) (HA fi fh fg ff fe fd) fc = TyPi (Sing fg ff) (HC fi fh fg ff fe fd fc)
$(P.return [])
type instance (@@) (GY fo fn fm fl fk) fj = TyPi (Sing * fm) (HA fo fn fm fl fk fj)
$(P.return [])
type instance (@@) (GW ft fs fr fq) fp = TyPi (Sing * fs) (GY ft fs fr fq fp)
$(P.return [])
data GV (fy :: *) (fx :: *) (fw :: *) (fv :: fw) (fu :: TyPi' (Sing * fy) (GW fy fx fw fv))
$(P.return [])
data GX (ge :: *) (gd :: *) (gc :: *) (gb :: gc) (ga :: Sing * ge) (fz :: TyPi' (Sing * gd) (GY ge gd gc gb ga))
$(P.return [])
type instance (@@@) (GV gj gi gh gg) gf = GX gj gi gh gg gf
$(P.return [])
data GZ (gq :: *) (gp :: *) (go :: *) (gn :: go) (gm :: Sing * gq) (gl :: Sing * gp) (gk :: TyPi' (Sing * go) (HA gq gp go gn gm gl))
$(P.return [])
type instance (@@@) (GX gw gv gu gt gs) gr = GZ gw gv gu gt gs gr
$(P.return [])
data HB (he :: *) (hd :: *) (hc :: *) (hb :: hc) (ha :: Sing * he) (gz :: Sing * hd) (gy :: Sing * hc) (gx :: TyPi' (Sing hc hb) (HC he hd hc hb ha gz gy))
$(P.return [])
type instance (@@@) (GZ hl hk hj hi hh hg) hf = HB hl hk hj hi hh hg hf
$(P.return [])
type instance (@@@) (HB ht hs hr hq hp ho hn) hm = 'CompGtT hp ho hn hm
$(P.return [])
data GO (hy :: *) (hx :: *) (hw :: *) (hv :: hx) (hu :: TyFun' (Sing * hy) *)
$(P.return [])
data GQ (ie :: *) (id :: *) (ic :: *) (ib :: id) (ia :: Sing * ie) (hz :: TyFun' (Sing * id) *)
$(P.return [])
data GS (im :: *) (il :: *) (ik :: *) (ij :: il) (ii :: Sing * im) (ih :: Sing * il) (ig :: TyFun' (Sing * ik) *)
$(P.return [])
data GU (iv :: *) (iu :: *) (it :: *) (is :: iu) (ir :: Sing * iv) (iq :: Sing * iu) (ip :: Sing * it) (io :: TyFun' (Sing iu is) *)
$(P.return [])
type instance (@@) (GU jd jc jb ja iz iy ix) iw = CompareSpecT jd jc jb 'Lt
$(P.return [])
type instance (@@) (GS jk jj ji jh jg jf) je = TyPi (Sing jj jh) (GU jk jj ji jh jg jf je)
$(P.return [])
type instance (@@) (GQ jq jp jo jn jm) jl = TyPi (Sing * jo) (GS jq jp jo jn jm jl)
$(P.return [])
type instance (@@) (GO jv ju jt js) jr = TyPi (Sing * ju) (GQ jv ju jt js jr)
$(P.return [])
data GN (ka :: *) (jz :: *) (jy :: *) (jx :: jz) (jw :: TyPi' (Sing * ka) (GO ka jz jy jx))
$(P.return [])
data GP (kg :: *) (kf :: *) (ke :: *) (kd :: kf) (kc :: Sing * kg) (kb :: TyPi' (Sing * kf) (GQ kg kf ke kd kc))
$(P.return [])
type instance (@@@) (GN kl kk kj ki) kh = GP kl kk kj ki kh
$(P.return [])
data GR (ks :: *) (kr :: *) (kq :: *) (kp :: kr) (ko :: Sing * ks) (kn :: Sing * kr) (km :: TyPi' (Sing * kq) (GS ks kr kq kp ko kn))
$(P.return [])
type instance (@@@) (GP ky kx kw kv ku) kt = GR ky kx kw kv ku kt
$(P.return [])
data GT (lg :: *) (lf :: *) (le :: *) (ld :: lf) (lc :: Sing * lg) (lb :: Sing * lf) (la :: Sing * le) (kz :: TyPi' (Sing lf ld) (GU lg lf le ld lc lb la))
$(P.return [])
type instance (@@@) (GR ln lm ll lk lj li) lh = GT ln lm ll lk lj li lh
$(P.return [])
type instance (@@@) (GT lv lu lt ls lr lq lp) lo = 'CompLtT lr lq lp lo
$(P.return [])
data GG (ma :: *) (lz :: *) (ly :: *) (lx :: ma) (lw :: TyFun' (Sing * ma) *)
$(P.return [])
data GI (mg :: *) (mf :: *) (me :: *) (md :: mg) (mc :: Sing * mg) (mb :: TyFun' (Sing * mf) *)
$(P.return [])
data GK (mn :: *) (mm :: *) (ml :: *) (mk :: mn) (mj :: Sing * mn) (mi :: Sing * mm) (mh :: TyFun' (Sing * ml) *)
$(P.return [])
data GM (mv :: *) (mu :: *) (mt :: *) (ms :: mv) (mr :: Sing * mv) (mq :: Sing * mu) (mp :: Sing * mt) (mo :: TyFun' (Sing mv ms) *)
$(P.return [])
type instance (@@) (GM nd nc nb na mz my mx) mw = CompareSpecT nd nc nb 'Eq
$(P.return [])
type instance (@@) (GK nk nj ni nh ng nf) ne = TyPi (Sing nk nh) (GM nk nj ni nh ng nf ne)
$(P.return [])
type instance (@@) (GI nq np no nn nm) nl = TyPi (Sing * no) (GK nq np no nn nm nl)
$(P.return [])
type instance (@@) (GG nv nu nt ns) nr = TyPi (Sing * nu) (GI nv nu nt ns nr)
$(P.return [])
data GF (oa :: *) (nz :: *) (ny :: *) (nx :: oa) (nw :: TyPi' (Sing * oa) (GG oa nz ny nx))
$(P.return [])
data GH (oh :: *) (og :: *) (oe :: *) (od :: oh) (oc :: Sing * oh) (ob :: TyPi' (Sing * og) (GI oh og oe od oc))
$(P.return [])
type instance (@@@) (GF om ol ok oj) oi = GH om ol ok oj oi
$(P.return [])
data GJ (ot :: *) (os :: *) (or :: *) (oq :: ot) (op :: Sing * ot) (oo :: Sing * os) (on :: TyPi' (Sing * or) (GK ot os or oq op oo))
$(P.return [])
type instance (@@@) (GH oz oy ox ow ov) ou = GJ oz oy ox ow ov ou
$(P.return [])
data GL (ph :: *) (pg :: *) (pf :: *) (pe :: ph) (pd :: Sing * ph) (pc :: Sing * pg) (pb :: Sing * pf) (pa :: TyPi' (Sing ph pe) (GM ph pg pf pe pd pc pb))
$(P.return [])
type instance (@@@) (GJ po pn pm pl pk pj) pi = GL po pn pm pl pk pj pi
$(P.return [])
type instance (@@@) (GL pw pv pu pt ps pr pq) pp = 'CompEqT ps pr pq pp
$(P.return [])
data instance Sing (CompareSpecT qw qx qy qz) qv where
  SCompEqT ::
    forall (px :: *) (py :: *) (pz :: *) (qa :: px) (qb :: Sing * px) (qc :: Sing * py) (qd :: Sing * pz) (qe :: Sing
    px qa). (Sing * px) -> (Sing * py) -> (Sing * pz) -> (Sing px qa) -> Sing' ('CompEqT qb qc qd qe)
  SCompLtT ::
    forall (qf :: *) (qg :: *) (qh :: *) (qi :: qg) (qj :: Sing * qf) (qk :: Sing * qg) (ql :: Sing * qh) (qm :: Sing
    qg qi). (Sing * qf) -> (Sing * qg) -> (Sing * qh) -> (Sing qg qi) -> Sing' ('CompLtT qj qk ql qm)
  SCompGtT ::
    forall (qn :: *) (qo :: *) (qp :: *) (qq :: qp) (qr :: Sing * qn) (qs :: Sing * qo) (qt :: Sing * qp) (qu :: Sing
    qp qq). (Sing * qn) -> (Sing * qo) -> (Sing * qp) -> (Sing qp qq) -> Sing' ('CompGtT qr qs qt qu)
$(P.return [])
data FY (ra :: TyFun' * *)
$(P.return [])
data GA (rc :: *) (rb :: TyFun' * *)
$(P.return [])
data GC (rf :: *) (re :: *) (rd :: TyFun' * *)
$(P.return [])
data GE (rj :: *) (ri :: *) (rh :: *) (rg :: TyFun' Comparison *)
$(P.return [])
type instance (@@) (GE rn rm rl) rk = *
$(P.return [])
type instance (@@) (GC rq rp) ro = TyPi Comparison (GE rq rp ro)
$(P.return [])
type instance (@@) (GA rs) rr = TyPi * (GC rs rr)
$(P.return [])
type instance (@@) FY rt = TyPi * (GA rt)
$(P.return [])
data FX (ru :: TyPi' * FY)
$(P.return [])
data FZ (rw :: *) (rv :: TyPi' * (GA rw))
$(P.return [])
type instance (@@@) FX rx = FZ rx
$(P.return [])
data GB (sa :: *) (rz :: *) (ry :: TyPi' * (GC sa rz))
$(P.return [])
type instance (@@@) (FZ sc) sb = GB sc sb
$(P.return [])
data GD (sg :: *) (sf :: *) (se :: *) (sd :: TyPi' Comparison (GE sg sf se))
$(P.return [])
type instance (@@@) (GB sj si) sh = GD sj si sh
$(P.return [])
type instance (@@@) (GD sn sm sl) sk = CompareSpecT sn sm sl sk
$(P.return [])
data FQ (ss :: *) (sr :: *) (sq :: *) (sp :: sq) (so :: TyFun' (Sing * ss) *)
$(P.return [])
data FS (sy :: *) (sx :: *) (sw :: *) (sv :: sw) (su :: Sing * sy) (st :: TyFun' (Sing * sx) *)
$(P.return [])
data FU (tf :: *) (te :: *) (td :: *) (tc :: td) (tb :: Sing * tf) (ta :: Sing * te) (sz :: TyFun' (Sing * td) *)
$(P.return [])
data FW (tn :: *) (tm :: *) (tl :: *) (tk :: tl) (tj :: Sing * tn) (ti :: Sing * tm) (th :: Sing * tl) (tg :: TyFun' (Sing tl tk) *)
$(P.return [])
data CompareSpec (ua :: *) (ub :: *) (uc :: *) (ud :: Comparison) :: * where
  CompEq ::
    forall (to :: *) (tp :: *) (tq :: *) (tr :: to). (Sing * to) -> (Sing * tp) -> (Sing * tq) -> (Sing to tr) ->
    CompareSpec {- KIND -} to {- KIND -} tp {- KIND -} tq 'Eq
  CompLt ::
    forall (ts :: *) (tt :: *) (tu :: *) (tv :: tt). (Sing * ts) -> (Sing * tt) -> (Sing * tu) -> (Sing tt tv) ->
    CompareSpec {- KIND -} ts {- KIND -} tt {- KIND -} tu 'Lt
  CompGt ::
    forall (tw :: *) (tx :: *) (ty :: *) (tz :: ty). (Sing * tw) -> (Sing * tx) -> (Sing * ty) -> (Sing ty tz) ->
    CompareSpec {- KIND -} tw {- KIND -} tx {- KIND -} ty 'Gt
$(P.return [])
type instance (@@) (FW ul uk uj ui uh ug uf) ue = CompareSpec ul uk uj 'Gt
$(P.return [])
type instance (@@) (FU us ur uq up uo un) um = TyPi (Sing uq up) (FW us ur uq up uo un um)
$(P.return [])
type instance (@@) (FS uy ux uw uv uu) ut = TyPi (Sing * uw) (FU uy ux uw uv uu ut)
$(P.return [])
type instance (@@) (FQ vd vc vb va) uz = TyPi (Sing * vc) (FS vd vc vb va uz)
$(P.return [])
data FP (vi :: *) (vh :: *) (vg :: *) (vf :: vg) (ve :: TyPi' (Sing * vi) (FQ vi vh vg vf))
$(P.return [])
data FR (vo :: *) (vn :: *) (vm :: *) (vl :: vm) (vk :: Sing * vo) (vj :: TyPi' (Sing * vn) (FS vo vn vm vl vk))
$(P.return [])
type instance (@@@) (FP vt vs vr vq) vp = FR vt vs vr vq vp
$(P.return [])
data FT (wa :: *) (vz :: *) (vy :: *) (vx :: vy) (vw :: Sing * wa) (vv :: Sing * vz) (vu :: TyPi' (Sing * vy) (FU wa vz vy vx vw vv))
$(P.return [])
type instance (@@@) (FR wg wf we wd wc) wb = FT wg wf we wd wc wb
$(P.return [])
data FV (wo :: *) (wn :: *) (wm :: *) (wl :: wm) (wk :: Sing * wo) (wj :: Sing * wn) (wi :: Sing * wm) (wh :: TyPi' (Sing wm wl) (FW wo wn wm wl wk wj wi))
$(P.return [])
type instance (@@@) (FT wv wu wt ws wr wq) wp = FV wv wu wt ws wr wq wp
$(P.return [])
type instance (@@@) (FV xd xc xb xa wz wy wx) ww = 'CompGt wz wy wx ww
$(P.return [])
data FI (xi :: *) (xh :: *) (xg :: *) (xf :: xh) (xe :: TyFun' (Sing * xi) *)
$(P.return [])
data FK (xo :: *) (xn :: *) (xm :: *) (xl :: xn) (xk :: Sing * xo) (xj :: TyFun' (Sing * xn) *)
$(P.return [])
data FM (xv :: *) (xu :: *) (xt :: *) (xs :: xu) (xr :: Sing * xv) (xq :: Sing * xu) (xp :: TyFun' (Sing * xt) *)
$(P.return [])
data FO (yd :: *) (yc :: *) (yb :: *) (ya :: yc) (xz :: Sing * yd) (xy :: Sing * yc) (xx :: Sing * yb) (xw :: TyFun' (Sing yc ya) *)
$(P.return [])
type instance (@@) (FO yl yk yj yi yh yg yf) ye = CompareSpec yl yk yj 'Lt
$(P.return [])
type instance (@@) (FM ys yr yq yp yo yn) ym = TyPi (Sing yr yp) (FO ys yr yq yp yo yn ym)
$(P.return [])
type instance (@@) (FK yy yx yw yv yu) yt = TyPi (Sing * yw) (FM yy yx yw yv yu yt)
$(P.return [])
type instance (@@) (FI zd zc zb za) yz = TyPi (Sing * zc) (FK zd zc zb za yz)
$(P.return [])
data FH (zi :: *) (zh :: *) (zg :: *) (zf :: zh) (ze :: TyPi' (Sing * zi) (FI zi zh zg zf))
$(P.return [])
data FJ (zo :: *) (zn :: *) (zm :: *) (zl :: zn) (zk :: Sing * zo) (zj :: TyPi' (Sing * zn) (FK zo zn zm zl zk))
$(P.return [])
type instance (@@@) (FH zt zs zr zq) zp = FJ zt zs zr zq zp
$(P.return [])
data FL (aaa :: *) (zz :: *) (zy :: *) (zx :: zz) (zw :: Sing * aaa) (zv :: Sing * zz) (zu :: TyPi' (Sing * zy) (FM aaa zz zy zx zw zv))
$(P.return [])
type instance (@@@) (FJ aag aaf aae aad aac) aab = FL aag aaf aae aad aac aab
$(P.return [])
data FN (aao :: *) (aan :: *) (aam :: *) (aal :: aan) (aak :: Sing * aao) (aaj :: Sing * aan) (aai :: Sing * aam) (aah :: TyPi' (Sing aan aal) (FO aao aan aam aal aak aaj aai))
$(P.return [])
type instance (@@@) (FL aav aau aat aas aar aaq) aap = FN aav aau aat aas aar aaq aap
$(P.return [])
type instance (@@@) (FN abd abc abb aba aaz aay aax) aaw = 'CompLt aaz aay aax aaw
$(P.return [])
data FA (abi :: *) (abh :: *) (abg :: *) (abf :: abi) (abe :: TyFun' (Sing * abi) *)
$(P.return [])
data FC (abo :: *) (abn :: *) (abm :: *) (abl :: abo) (abk :: Sing * abo) (abj :: TyFun' (Sing * abn) *)
$(P.return [])
data FE (abv :: *) (abu :: *) (abt :: *) (abs :: abv) (abr :: Sing * abv) (abq :: Sing * abu) (abp :: TyFun' (Sing * abt) *)
$(P.return [])
data FG (acd :: *) (acc :: *) (acb :: *) (aca :: acd) (abz :: Sing * acd) (aby :: Sing * acc) (abx :: Sing * acb) (abw :: TyFun' (Sing acd aca) *)
$(P.return [])
type instance (@@) (FG acl ack acj aci ach acg acf) ace = CompareSpec acl ack acj 'Eq
$(P.return [])
type instance (@@) (FE acs acr acq acp aco acn) acm = TyPi (Sing acs acp) (FG acs acr acq acp aco acn acm)
$(P.return [])
type instance (@@) (FC acy acx acw acv acu) act = TyPi (Sing * acw) (FE acy acx acw acv acu act)
$(P.return [])
type instance (@@) (FA add adc adb ada) acz = TyPi (Sing * adc) (FC add adc adb ada acz)
$(P.return [])
data EZ (adi :: *) (adh :: *) (adg :: *) (adf :: adi) (ade :: TyPi' (Sing * adi) (FA adi adh adg adf))
$(P.return [])
data FB (ado :: *) (adn :: *) (adm :: *) (adl :: ado) (adk :: Sing * ado) (adj :: TyPi' (Sing * adn) (FC ado adn adm adl adk))
$(P.return [])
type instance (@@@) (EZ adt ads adr adq) adp = FB adt ads adr adq adp
$(P.return [])
data FD (aea :: *) (adz :: *) (ady :: *) (adx :: aea) (adw :: Sing * aea) (adv :: Sing * adz) (adu :: TyPi' (Sing * ady) (FE aea adz ady adx adw adv))
$(P.return [])
type instance (@@@) (FB aeg aef aee aed aec) aeb = FD aeg aef aee aed aec aeb
$(P.return [])
data FF (aeo :: *) (aen :: *) (aem :: *) (ael :: aeo) (aek :: Sing * aeo) (aej :: Sing * aen) (aei :: Sing * aem) (aeh :: TyPi' (Sing aeo ael) (FG aeo aen aem ael aek aej aei))
$(P.return [])
type instance (@@@) (FD aev aeu aet aes aer aeq) aep = FF aev aeu aet aes aer aeq aep
$(P.return [])
type instance (@@@) (FF afd afc afb afa aez aey aex) aew = 'CompEq aez aey aex aew
$(P.return [])
data instance Sing (CompareSpec agd age agf agg) agc where
  SCompEq ::
    forall (afe :: *) (aff :: *) (afg :: *) (afh :: afe) (afi :: Sing * afe) (afj :: Sing * aff) (afk :: Sing * afg)
    (afl :: Sing afe afh). (Sing * afe) -> (Sing * aff) -> (Sing * afg) -> (Sing afe afh) -> Sing' ('CompEq afi afj afk
    afl)
  SCompLt ::
    forall (afm :: *) (afn :: *) (afo :: *) (afp :: afn) (afq :: Sing * afm) (afr :: Sing * afn) (afs :: Sing * afo)
    (aft :: Sing afn afp). (Sing * afm) -> (Sing * afn) -> (Sing * afo) -> (Sing afn afp) -> Sing' ('CompLt afq afr afs
    aft)
  SCompGt ::
    forall (afu :: *) (afv :: *) (afw :: *) (afx :: afw) (afy :: Sing * afu) (afz :: Sing * afv) (aga :: Sing * afw)
    (agb :: Sing afw afx). (Sing * afu) -> (Sing * afv) -> (Sing * afw) -> (Sing afw afx) -> Sing' ('CompGt afy afz aga
    agb)
$(P.return [])
data ES (agh :: TyFun' * *)
$(P.return [])
data EU (agj :: *) (agi :: TyFun' * *)
$(P.return [])
data EW (agm :: *) (agl :: *) (agk :: TyFun' * *)
$(P.return [])
data EY (agq :: *) (agp :: *) (ago :: *) (agn :: TyFun' Comparison *)
$(P.return [])
type instance (@@) (EY agu agt ags) agr = *
$(P.return [])
type instance (@@) (EW agx agw) agv = TyPi Comparison (EY agx agw agv)
$(P.return [])
type instance (@@) (EU agz) agy = TyPi * (EW agz agy)
$(P.return [])
type instance (@@) ES aha = TyPi * (EU aha)
$(P.return [])
data ER (ahb :: TyPi' * ES)
$(P.return [])
data ET (ahd :: *) (ahc :: TyPi' * (EU ahd))
$(P.return [])
type instance (@@@) ER ahe = ET ahe
$(P.return [])
data EV (ahh :: *) (ahg :: *) (ahf :: TyPi' * (EW ahh ahg))
$(P.return [])
type instance (@@@) (ET ahj) ahi = EV ahj ahi
$(P.return [])
data EX (ahn :: *) (ahm :: *) (ahl :: *) (ahk :: TyPi' Comparison (EY ahn ahm ahl))
$(P.return [])
type instance (@@@) (EV ahq ahp) aho = EX ahq ahp aho
$(P.return [])
type instance (@@@) (EX ahu aht ahs) ahr = CompareSpec ahu aht ahs ahr
$(P.return [])
data instance Sing Comparison ahv where
  SEq ::   Sing' 'Eq
  SLt ::   Sing' 'Lt
  SGt ::   Sing' 'Gt
$(P.return [])
data EM (ahy :: *) (ahx :: ahy) (ahw :: TyFun' (Sing * ahy) *)
$(P.return [])
data EO (aic :: *) (aib :: aic) (aia :: Sing * aic) (ahz :: TyFun' (Sing aic aib) *)
$(P.return [])
data List (aig :: *) :: * where
  Nil ::   forall (aid :: *). (Sing * aid) -> List {- KIND -} aid
  Cons ::
    forall (aie :: *) (aif :: aie). (Sing * aie) -> (Sing aie aif) -> (List {- KIND -} aie) -> List {- KIND -} aie
$(P.return [])
data EQ (ail :: *) (aik :: ail) (aij :: Sing * ail) (aii :: Sing ail aik) (aih :: TyFun' (List ail) *)
$(P.return [])
type instance (@@) (EQ aiq aip aio ain) aim = List aiq
$(P.return [])
type instance (@@) (EO aiu ait ais) air = TyPi (List aiu) (EQ aiu ait ais air)
$(P.return [])
type instance (@@) (EM aix aiw) aiv = TyPi (Sing aix aiw) (EO aix aiw aiv)
$(P.return [])
data EL (aja :: *) (aiz :: aja) (aiy :: TyPi' (Sing * aja) (EM aja aiz))
$(P.return [])
data EN (aje :: *) (ajd :: aje) (ajc :: Sing * aje) (ajb :: TyPi' (Sing aje ajd) (EO aje ajd ajc))
$(P.return [])
type instance (@@@) (EL ajh ajg) ajf = EN ajh ajg ajf
$(P.return [])
data EP (ajm :: *) (ajl :: ajm) (ajk :: Sing * ajm) (ajj :: Sing ajm ajl) (aji :: TyPi' (List ajm) (EQ ajm ajl ajk ajj))
$(P.return [])
type instance (@@@) (EN ajq ajp ajo) ajn = EP ajq ajp ajo ajn
$(P.return [])
type instance (@@@) (EP ajv aju ajt ajs) ajr = 'Cons ajt ajs ajr
$(P.return [])
data EK (ajx :: *) (ajw :: TyFun' (Sing * ajx) *)
$(P.return [])
type instance (@@) (EK ajz) ajy = List ajz
$(P.return [])
data EJ (akb :: *) (aka :: TyPi' (Sing * akb) (EK akb))
$(P.return [])
type instance (@@@) (EJ akd) akc = 'Nil akc
$(P.return [])
data instance Sing (List akm) akl where
  SNil ::   forall (ake :: *) (akf :: Sing * ake). (Sing * ake) -> Sing' ('Nil akf)
  SCons ::
    forall (akg :: *) (akh :: akg) (aki :: Sing * akg) (akj :: Sing akg akh) (akk :: List akg). (Sing * akg) -> (Sing
    akg akh) -> (Sing (List akg) akk) -> Sing' ('Cons aki akj akk)
$(P.return [])
data EI (akn :: TyFun' * *)
$(P.return [])
type instance (@@) EI ako = *
$(P.return [])
data EH (akp :: TyPi' * EI)
$(P.return [])
type instance (@@@) EH akq = List akq
$(P.return [])
data EA (akv :: *) (aku :: *) (akt :: akv) (aks :: aku) (akr :: TyFun' (Sing * akv) *)
$(P.return [])
data EC (alb :: *) (ala :: *) (akz :: alb) (aky :: ala) (akx :: Sing * alb) (akw :: TyFun' (Sing * ala) *)
$(P.return [])
data EE (ali :: *) (alh :: *) (alg :: ali) (alf :: alh) (ale :: Sing * ali) (ald :: Sing * alh) (alc :: TyFun' (Sing ali alg) *)
$(P.return [])
data EG (alq :: *) (alp :: *) (alo :: alq) (aln :: alp) (alm :: Sing * alq) (all :: Sing * alp) (alk :: Sing alq alo) (alj :: TyFun' (Sing alp aln) *)
$(P.return [])
data Prod (alv :: *) (alw :: *) :: * where
  Pair ::
    forall (alr :: *) (als :: *) (alt :: alr) (alu :: als). (Sing * alr) -> (Sing * als) -> (Sing alr alt) -> (Sing als
    alu) -> Prod {- KIND -} alr {- KIND -} als
$(P.return [])
type instance (@@) (EG ame amd amc amb ama alz aly) alx = Prod ame amd
$(P.return [])
type instance (@@) (EE aml amk amj ami amh amg) amf = TyPi (Sing amk ami) (EG aml amk amj ami amh amg amf)
$(P.return [])
type instance (@@) (EC amr amq amp amo amn) amm = TyPi (Sing amr amp) (EE amr amq amp amo amn amm)
$(P.return [])
type instance (@@) (EA amw amv amu amt) ams = TyPi (Sing * amv) (EC amw amv amu amt ams)
$(P.return [])
data DZ (anb :: *) (ana :: *) (amz :: anb) (amy :: ana) (amx :: TyPi' (Sing * anb) (EA anb ana amz amy))
$(P.return [])
data EB (anh :: *) (ang :: *) (anf :: anh) (ane :: ang) (and :: Sing * anh) (anc :: TyPi' (Sing * ang) (EC anh ang anf ane and))
$(P.return [])
type instance (@@@) (DZ anm anl ank anj) ani = EB anm anl ank anj ani
$(P.return [])
data ED (ant :: *) (ans :: *) (anr :: ant) (anq :: ans) (anp :: Sing * ant) (ano :: Sing * ans) (ann :: TyPi' (Sing ant anr) (EE ant ans anr anq anp ano))
$(P.return [])
type instance (@@@) (EB anz any anx anw anv) anu = ED anz any anx anw anv anu
$(P.return [])
data EF (aoh :: *) (aog :: *) (aof :: aoh) (aoe :: aog) (aod :: Sing * aoh) (aoc :: Sing * aog) (aob :: Sing aoh aof) (aoa :: TyPi' (Sing aog aoe) (EG aoh aog aof aoe aod aoc aob))
$(P.return [])
type instance (@@@) (ED aoo aon aom aol aok aoj) aoi = EF aoo aon aom aol aok aoj aoi
$(P.return [])
type instance (@@@) (EF aow aov aou aot aos aor aoq) aop = 'Pair aos aor aoq aop
$(P.return [])
data instance Sing (Prod apg aph) apf where
  SPair ::
    forall (aox :: *) (aoy :: *) (aoz :: aox) (apa :: aoy) (apb :: Sing * aox) (apc :: Sing * aoy) (apd :: Sing aox
    aoz) (ape :: Sing aoy apa). (Sing * aox) -> (Sing * aoy) -> (Sing aox aoz) -> (Sing aoy apa) -> Sing' ('Pair apb
    apc apd ape)
$(P.return [])
data DW (api :: TyFun' * *)
$(P.return [])
data DY (apk :: *) (apj :: TyFun' * *)
$(P.return [])
type instance (@@) (DY apm) apl = *
$(P.return [])
type instance (@@) DW apn = TyPi * (DY apn)
$(P.return [])
data DV (apo :: TyPi' * DW)
$(P.return [])
data DX (apq :: *) (app :: TyPi' * (DY apq))
$(P.return [])
type instance (@@@) DV apr = DX apr
$(P.return [])
type instance (@@@) (DX apt) aps = Prod apt aps
$(P.return [])
data DQ (apx :: *) (apw :: *) (apv :: apw) (apu :: TyFun' (Sing * apx) *)
$(P.return [])
data DS (aqc :: *) (aqb :: *) (aqa :: aqb) (apz :: Sing * aqc) (apy :: TyFun' (Sing * aqb) *)
$(P.return [])
data DU (aqi :: *) (aqh :: *) (aqg :: aqh) (aqf :: Sing * aqi) (aqe :: Sing * aqh) (aqd :: TyFun' (Sing aqh aqg) *)
$(P.return [])
data Sum (aqp :: *) (aqq :: *) :: * where
  Inl ::
    forall (aqj :: *) (aqk :: *) (aql :: aqj). (Sing * aqj) -> (Sing * aqk) -> (Sing aqj aql) -> Sum {- KIND -} aqj
    {- KIND -} aqk
  Inr ::
    forall (aqm :: *) (aqn :: *) (aqo :: aqn). (Sing * aqm) -> (Sing * aqn) -> (Sing aqn aqo) -> Sum {- KIND -} aqm
    {- KIND -} aqn
$(P.return [])
type instance (@@) (DU aqw aqv aqu aqt aqs) aqr = Sum aqw aqv
$(P.return [])
type instance (@@) (DS arb ara aqz aqy) aqx = TyPi (Sing ara aqz) (DU arb ara aqz aqy aqx)
$(P.return [])
type instance (@@) (DQ arf are ard) arc = TyPi (Sing * are) (DS arf are ard arc)
$(P.return [])
data DP (arj :: *) (ari :: *) (arh :: ari) (arg :: TyPi' (Sing * arj) (DQ arj ari arh))
$(P.return [])
data DR (aro :: *) (arn :: *) (arm :: arn) (arl :: Sing * aro) (ark :: TyPi' (Sing * arn) (DS aro arn arm arl))
$(P.return [])
type instance (@@@) (DP ars arr arq) arp = DR ars arr arq arp
$(P.return [])
data DT (ary :: *) (arx :: *) (arw :: arx) (arv :: Sing * ary) (aru :: Sing * arx) (art :: TyPi' (Sing arx arw) (DU ary arx arw arv aru))
$(P.return [])
type instance (@@@) (DR asd asc asb asa) arz = DT asd asc asb asa arz
$(P.return [])
type instance (@@@) (DT asj asi ash asg asf) ase = 'Inr asg asf ase
$(P.return [])
data DK (asn :: *) (asm :: *) (asl :: asn) (ask :: TyFun' (Sing * asn) *)
$(P.return [])
data DM (ass :: *) (asr :: *) (asq :: ass) (asp :: Sing * ass) (aso :: TyFun' (Sing * asr) *)
$(P.return [])
data DO (asy :: *) (asx :: *) (asw :: asy) (asv :: Sing * asy) (asu :: Sing * asx) (ast :: TyFun' (Sing asy asw) *)
$(P.return [])
type instance (@@) (DO ate atd atc atb ata) asz = Sum ate atd
$(P.return [])
type instance (@@) (DM atj ati ath atg) atf = TyPi (Sing atj ath) (DO atj ati ath atg atf)
$(P.return [])
type instance (@@) (DK atn atm atl) atk = TyPi (Sing * atm) (DM atn atm atl atk)
$(P.return [])
data DJ (atr :: *) (atq :: *) (atp :: atr) (ato :: TyPi' (Sing * atr) (DK atr atq atp))
$(P.return [])
data DL (atw :: *) (atv :: *) (atu :: atw) (att :: Sing * atw) (ats :: TyPi' (Sing * atv) (DM atw atv atu att))
$(P.return [])
type instance (@@@) (DJ aua atz aty) atx = DL aua atz aty atx
$(P.return [])
data DN (aug :: *) (auf :: *) (aue :: aug) (aud :: Sing * aug) (auc :: Sing * auf) (aub :: TyPi' (Sing aug aue) (DO aug auf aue aud auc))
$(P.return [])
type instance (@@@) (DL aul auk auj aui) auh = DN aul auk auj aui auh
$(P.return [])
type instance (@@@) (DN aur auq aup auo aun) aum = 'Inl auo aun aum
$(P.return [])
data instance Sing (Sum avf avg) ave where
  SInl ::
    forall (aus :: *) (aut :: *) (auu :: aus) (auv :: Sing * aus) (auw :: Sing * aut) (aux :: Sing aus auu). (Sing *
    aus) -> (Sing * aut) -> (Sing aus auu) -> Sing' ('Inl auv auw aux)
  SInr ::
    forall (auy :: *) (auz :: *) (ava :: auz) (avb :: Sing * auy) (avc :: Sing * auz) (avd :: Sing auz ava). (Sing *
    auy) -> (Sing * auz) -> (Sing auz ava) -> Sing' ('Inr avb avc avd)
$(P.return [])
data DG (avh :: TyFun' * *)
$(P.return [])
data DI (avj :: *) (avi :: TyFun' * *)
$(P.return [])
type instance (@@) (DI avl) avk = *
$(P.return [])
type instance (@@) DG avm = TyPi * (DI avm)
$(P.return [])
data DF (avn :: TyPi' * DG)
$(P.return [])
data DH (avp :: *) (avo :: TyPi' * (DI avp))
$(P.return [])
type instance (@@@) DF avq = DH avq
$(P.return [])
type instance (@@@) (DH avs) avr = Sum avs avr
$(P.return [])
data DE (avu :: *) (avt :: TyFun' (Sing * avu) *)
$(P.return [])
data Option (avy :: *) :: * where
  Some ::   forall (avv :: *) (avw :: avv). (Sing * avv) -> (Sing avv avw) -> Option {- KIND -} avv
  None ::   forall (avx :: *). (Sing * avx) -> Option {- KIND -} avx
$(P.return [])
type instance (@@) (DE awa) avz = Option awa
$(P.return [])
data DD (awc :: *) (awb :: TyPi' (Sing * awc) (DE awc))
$(P.return [])
type instance (@@@) (DD awe) awd = 'None awd
$(P.return [])
data DA (awh :: *) (awg :: awh) (awf :: TyFun' (Sing * awh) *)
$(P.return [])
data DC (awl :: *) (awk :: awl) (awj :: Sing * awl) (awi :: TyFun' (Sing awl awk) *)
$(P.return [])
type instance (@@) (DC awp awo awn) awm = Option awp
$(P.return [])
type instance (@@) (DA aws awr) awq = TyPi (Sing aws awr) (DC aws awr awq)
$(P.return [])
data CZ (awv :: *) (awu :: awv) (awt :: TyPi' (Sing * awv) (DA awv awu))
$(P.return [])
data DB (awz :: *) (awy :: awz) (awx :: Sing * awz) (aww :: TyPi' (Sing awz awy) (DC awz awy awx))
$(P.return [])
type instance (@@@) (CZ axc axb) axa = DB axc axb axa
$(P.return [])
type instance (@@@) (DB axg axf axe) axd = 'Some axe axd
$(P.return [])
data instance Sing (Option axo) axn where
  SSome ::
    forall (axh :: *) (axi :: axh) (axj :: Sing * axh) (axk :: Sing axh axi). (Sing * axh) -> (Sing axh axi) -> Sing'
    ('Some axj axk)
  SNone ::   forall (axl :: *) (axm :: Sing * axl). (Sing * axl) -> Sing' ('None axm)
$(P.return [])
data CY (axp :: TyFun' * *)
$(P.return [])
type instance (@@) CY axq = *
$(P.return [])
data CX (axr :: TyPi' * CY)
$(P.return [])
type instance (@@@) CX axs = Option axs
$(P.return [])
data CW (axt :: TyFun' Nat *)
$(P.return [])
type instance (@@) CW axu = Nat
$(P.return [])
data CV (axv :: TyPi' Nat CW)
$(P.return [])
type instance (@@@) CV axw = 'S axw
$(P.return [])
data instance Sing Nat axy where
  SO ::   Sing' 'O
  SS ::   forall (axx :: Nat). (Sing Nat axx) -> Sing' ('S axx)
$(P.return [])
data CO (ayc :: *) (ayb :: *) (aya :: ayb) (axz :: TyFun' (Sing * ayc) *)
$(P.return [])
data CQ (ayh :: *) (ayg :: *) (ayf :: ayg) (aye :: Sing * ayh) (ayd :: TyFun' (Sing * ayg) *)
$(P.return [])
data CS (ayn :: *) (aym :: *) (ayl :: aym) (ayk :: Sing * ayn) (ayj :: Sing * aym) (ayi :: TyFun' (Sing aym ayl) *)
$(P.return [])
data Bool :: * where
  True ::   Bool
  False ::   Bool
$(P.return [])
data BoolSpec (ayu :: *) (ayv :: *) (ayw :: Bool) :: * where
  BoolSpecT ::
    forall (ayo :: *) (ayp :: *) (ayq :: ayo). (Sing * ayo) -> (Sing * ayp) -> (Sing ayo ayq) -> BoolSpec
    {- KIND -} ayo {- KIND -} ayp 'True
  BoolSpecF ::
    forall (ayr :: *) (ays :: *) (ayt :: ays). (Sing * ayr) -> (Sing * ays) -> (Sing ays ayt) -> BoolSpec
    {- KIND -} ayr {- KIND -} ays 'False
$(P.return [])
type instance (@@) (CS azc azb aza ayz ayy) ayx = BoolSpec azc azb 'False
$(P.return [])
type instance (@@) (CQ azh azg azf aze) azd = TyPi (Sing azg azf) (CS azh azg azf aze azd)
$(P.return [])
type instance (@@) (CO azl azk azj) azi = TyPi (Sing * azk) (CQ azl azk azj azi)
$(P.return [])
data CN (azp :: *) (azo :: *) (azn :: azo) (azm :: TyPi' (Sing * azp) (CO azp azo azn))
$(P.return [])
data CP (azu :: *) (azt :: *) (azs :: azt) (azr :: Sing * azu) (azq :: TyPi' (Sing * azt) (CQ azu azt azs azr))
$(P.return [])
type instance (@@@) (CN azy azx azw) azv = CP azy azx azw azv
$(P.return [])
data CR (bae :: *) (bad :: *) (bac :: bad) (bab :: Sing * bae) (baa :: Sing * bad) (azz :: TyPi' (Sing bad bac) (CS bae bad bac bab baa))
$(P.return [])
type instance (@@@) (CP baj bai bah bag) baf = CR baj bai bah bag baf
$(P.return [])
type instance (@@@) (CR bap bao ban bam bal) bak = 'BoolSpecF bam bal bak
$(P.return [])
data CI (bat :: *) (bas :: *) (bar :: bat) (baq :: TyFun' (Sing * bat) *)
$(P.return [])
data CK (bay :: *) (bax :: *) (baw :: bay) (bav :: Sing * bay) (bau :: TyFun' (Sing * bax) *)
$(P.return [])
data CM (bbe :: *) (bbd :: *) (bbc :: bbe) (bbb :: Sing * bbe) (bba :: Sing * bbd) (baz :: TyFun' (Sing bbe bbc) *)
$(P.return [])
type instance (@@) (CM bbk bbj bbi bbh bbg) bbf = BoolSpec bbk bbj 'True
$(P.return [])
type instance (@@) (CK bbp bbo bbn bbm) bbl = TyPi (Sing bbp bbn) (CM bbp bbo bbn bbm bbl)
$(P.return [])
type instance (@@) (CI bbt bbs bbr) bbq = TyPi (Sing * bbs) (CK bbt bbs bbr bbq)
$(P.return [])
data CH (bbx :: *) (bbw :: *) (bbv :: bbx) (bbu :: TyPi' (Sing * bbx) (CI bbx bbw bbv))
$(P.return [])
data CJ (bcc :: *) (bcb :: *) (bca :: bcc) (bbz :: Sing * bcc) (bby :: TyPi' (Sing * bcb) (CK bcc bcb bca bbz))
$(P.return [])
type instance (@@@) (CH bcg bcf bce) bcd = CJ bcg bcf bce bcd
$(P.return [])
data CL (bcm :: *) (bcl :: *) (bck :: bcm) (bcj :: Sing * bcm) (bci :: Sing * bcl) (bch :: TyPi' (Sing bcm bck) (CM bcm bcl bck bcj bci))
$(P.return [])
type instance (@@@) (CJ bcr bcq bcp bco) bcn = CL bcr bcq bcp bco bcn
$(P.return [])
type instance (@@@) (CL bcx bcw bcv bcu bct) bcs = 'BoolSpecT bcu bct bcs
$(P.return [])
data instance Sing (BoolSpec bdl bdm bdn) bdk where
  SBoolSpecT ::
    forall (bcy :: *) (bcz :: *) (bda :: bcy) (bdb :: Sing * bcy) (bdc :: Sing * bcz) (bdd :: Sing bcy bda). (Sing *
    bcy) -> (Sing * bcz) -> (Sing bcy bda) -> Sing' ('BoolSpecT bdb bdc bdd)
  SBoolSpecF ::
    forall (bde :: *) (bdf :: *) (bdg :: bdf) (bdh :: Sing * bde) (bdi :: Sing * bdf) (bdj :: Sing bdf bdg). (Sing *
    bde) -> (Sing * bdf) -> (Sing bdf bdg) -> Sing' ('BoolSpecF bdh bdi bdj)
$(P.return [])
data CC (bdo :: TyFun' * *)
$(P.return [])
data CE (bdq :: *) (bdp :: TyFun' * *)
$(P.return [])
data CG (bdt :: *) (bds :: *) (bdr :: TyFun' Bool *)
$(P.return [])
type instance (@@) (CG bdw bdv) bdu = *
$(P.return [])
type instance (@@) (CE bdy) bdx = TyPi Bool (CG bdy bdx)
$(P.return [])
type instance (@@) CC bdz = TyPi * (CE bdz)
$(P.return [])
data CB (bea :: TyPi' * CC)
$(P.return [])
data CD (bec :: *) (beb :: TyPi' * (CE bec))
$(P.return [])
type instance (@@@) CB bed = CD bed
$(P.return [])
data CF (beg :: *) (bef :: *) (bee :: TyPi' Bool (CG beg bef))
$(P.return [])
type instance (@@@) (CD bei) beh = CF bei beh
$(P.return [])
type instance (@@@) (CF bel bek) bej = BoolSpec bel bek bej
$(P.return [])
data Eq_true (bem :: Bool) :: * where
  Is_eq_true ::   Eq_true 'True
$(P.return [])
data instance Sing (Eq_true beo) ben where
  SIs_eq_true ::   Sing' 'Is_eq_true
$(P.return [])
data CA (bep :: TyFun' Bool *)
$(P.return [])
type instance (@@) CA beq = *
$(P.return [])
data BZ (ber :: TyPi' Bool CA)
$(P.return [])
type instance (@@@) BZ bes = Eq_true bes
$(P.return [])
data instance Sing Bool bet where
  STrue ::   Sing' 'True
  SFalse ::   Sing' 'False
$(P.return [])
data Unit :: * where
  Tt ::   Unit
$(P.return [])
data instance Sing Unit beu where
  STt ::   Sing' 'Tt
$(P.return [])
data Empty_set :: * where
  
$(P.return [])
data instance Sing Empty_set bev where
  
$(P.return [])
data BW (bey :: *) (bex :: bey) (bew :: TyFun' (Sing * bey) *)
$(P.return [])
data BY (bfc :: *) (bfb :: bfc) (bfa :: Sing * bfc) (bez :: TyFun' (Sing bfc bfb) *)
$(P.return [])
data Inhabited (bff :: *) :: * where
  Inhabits ::   forall (bfd :: *) (bfe :: bfd). (Sing * bfd) -> (Sing bfd bfe) -> Inhabited {- KIND -} bfd
$(P.return [])
type instance (@@) (BY bfj bfi bfh) bfg = Inhabited bfj
$(P.return [])
type instance (@@) (BW bfm bfl) bfk = TyPi (Sing bfm bfl) (BY bfm bfl bfk)
$(P.return [])
data BV (bfp :: *) (bfo :: bfp) (bfn :: TyPi' (Sing * bfp) (BW bfp bfo))
$(P.return [])
data BX (bft :: *) (bfs :: bft) (bfr :: Sing * bft) (bfq :: TyPi' (Sing bft bfs) (BY bft bfs bfr))
$(P.return [])
type instance (@@@) (BV bfw bfv) bfu = BX bfw bfv bfu
$(P.return [])
type instance (@@@) (BX bga bfz bfy) bfx = 'Inhabits bfy bfx
$(P.return [])
data instance Sing (Inhabited bgg) bgf where
  SInhabits ::
    forall (bgb :: *) (bgc :: bgb) (bgd :: Sing * bgb) (bge :: Sing bgb bgc). (Sing * bgb) -> (Sing bgb bgc) -> Sing'
    ('Inhabits bgd bge)
$(P.return [])
data BU (bgh :: TyFun' * *)
$(P.return [])
type instance (@@) BU bgi = *
$(P.return [])
data BT (bgj :: TyPi' * BU)
$(P.return [])
type instance (@@@) BT bgk = Inhabited bgk
$(P.return [])
data BQ (bgn :: *) (bgm :: bgn) (bgl :: TyFun' (Sing * bgn) *)
$(P.return [])
data BS (bgr :: *) (bgq :: bgr) (bgp :: Sing * bgr) (bgo :: TyFun' (Sing bgr bgq) *)
$(P.return [])
data Eq (bgu :: *) (bgv :: bgu) (bgw :: bgu) :: * where
  Eq_refl ::
    forall (bgs :: *) (bgt :: bgs). (Sing * bgs) -> (Sing bgs bgt) -> Eq {- KIND -} bgs {- KIND -} bgt {- KIND -} bgt
$(P.return [])
type instance (@@) (BS bha bgz bgy) bgx = Eq bha bgz bgz
$(P.return [])
type instance (@@) (BQ bhd bhc) bhb = TyPi (Sing bhd bhc) (BS bhd bhc bhb)
$(P.return [])
data BP (bhg :: *) (bhf :: bhg) (bhe :: TyPi' (Sing * bhg) (BQ bhg bhf))
$(P.return [])
data BR (bhk :: *) (bhj :: bhk) (bhi :: Sing * bhk) (bhh :: TyPi' (Sing bhk bhj) (BS bhk bhj bhi))
$(P.return [])
type instance (@@@) (BP bhn bhm) bhl = BR bhn bhm bhl
$(P.return [])
type instance (@@@) (BR bhr bhq bhp) bho = 'Eq_refl bhp bho
$(P.return [])
data instance Sing (Eq bhx bhy bhz) bhw where
  SEq_refl ::
    forall (bhs :: *) (bht :: bhs) (bhu :: Sing * bhs) (bhv :: Sing bhs bht). (Sing * bhs) -> (Sing bhs bht) -> Sing'
    ('Eq_refl bhu bhv)
$(P.return [])
data BK (bia :: TyFun' * *)
$(P.return [])
data BM (bic :: *) (bib :: TyFun' bic *)
$(P.return [])
data BO (bif :: *) (bie :: bif) (bid :: TyFun' bif *)
$(P.return [])
type instance (@@) (BO bii bih) big = *
$(P.return [])
type instance (@@) (BM bik) bij = TyPi bik (BO bik bij)
$(P.return [])
type instance (@@) BK bil = TyPi bil (BM bil)
$(P.return [])
data BJ (bim :: TyPi' * BK)
$(P.return [])
data BL (bio :: *) (bin :: TyPi' bio (BM bio))
$(P.return [])
type instance (@@@) BJ bip = BL bip
$(P.return [])
data BN (bis :: *) (bir :: bis) (biq :: TyPi' bis (BO bis bir))
$(P.return [])
type instance (@@@) (BL biu) bit = BN biu bit
$(P.return [])
type instance (@@@) (BN bix biw) biv = Eq bix biw biv
$(P.return [])
data AD (biz :: *) (biy :: TyFun' biz *)
$(P.return [])
type instance (@@) (AD bjb) bja = *
$(P.return [])
data AQ (bje :: *) (bjd :: TyPi bje (AD bje)) (bjc :: TyFun' bje *)
$(P.return [])
type instance (@@) (AQ bjh bjg) bjf = *
$(P.return [])
data AY (bjo :: *) (bjn :: TyPi bjo (AD bjo)) (bjm :: TyPi bjo (AQ bjo bjn)) (bjl :: bjo) (bjk :: bjn @@@ bjl) (bjj :: bjm @@@ bjl) (bji :: TyFun' (Sing * bjo) *)
$(P.return [])
data BA (bjw :: *) (bjv :: TyPi bjw (AD bjw)) (bju :: TyPi bjw (AQ bjw bjv)) (bjt :: bjw) (bjs :: bjv @@@ bjt) (bjr :: bju @@@ bjt) (bjq :: Sing * bjw) (bjp :: TyFun' (Sing (TyPi bjw (AD bjw)) bjv) *)
$(P.return [])
data BC (bkf :: *) (bke :: TyPi bkf (AD bkf)) (bkd :: TyPi bkf (AQ bkf bke)) (bkc :: bkf) (bkb :: bke @@@ bkc) (bka :: bkd @@@ bkc) (bjz :: Sing * bkf) (bjy :: Sing (TyPi bkf (AD bkf)) bke) (bjx :: TyFun' (Sing (TyPi bkf (AQ bkf bke)) bkd) *)
$(P.return [])
data BE (bkp :: *) (bko :: TyPi bkp (AD bkp)) (bkn :: TyPi bkp (AQ bkp bko)) (bkm :: bkp) (bkl :: bko @@@ bkm) (bkk :: bkn @@@ bkm) (bkj :: Sing * bkp) (bki :: Sing (TyPi bkp (AD bkp)) bko) (bkh :: Sing (TyPi bkp (AQ bkp bko)) bkn) (bkg :: TyFun' (Sing bkp bkm) *)
$(P.return [])
data BG (bla :: *) (bkz :: TyPi bla (AD bla)) (bky :: TyPi bla (AQ bla bkz)) (bkx :: bla) (bkw :: bkz @@@ bkx) (bkv :: bky @@@ bkx) (bku :: Sing * bla) (bkt :: Sing (TyPi bla (AD bla)) bkz) (bks :: Sing (TyPi bla (AQ bla bkz)) bky) (bkr :: Sing bla bkx) (bkq :: TyFun' (Sing (bkz @@@ bkx) bkw) *)
$(P.return [])
data BI (blm :: *) (bll :: TyPi blm (AD blm)) (blk :: TyPi blm (AQ blm bll)) (blj :: blm) (bli :: bll @@@ blj) (blh :: blk @@@ blj) (blg :: Sing * blm) (blf :: Sing (TyPi blm (AD blm)) bll) (ble :: Sing (TyPi blm (AQ blm bll)) blk) (bld :: Sing blm blj) (blc :: Sing (bll @@@ blj) bli) (blb :: TyFun' (Sing (blk @@@ blj) blh) *)
$(P.return [])
data Ex2 (blt :: *) (blu :: TyPi blt (AD blt)) (blv :: TyPi blt (AQ blt blu)) :: * where
  Ex_intro2 ::
    forall (bln :: *) (blo :: TyPi bln (AD bln)) (blp :: TyPi bln (AQ bln blo)) (blq :: bln) (blr :: blo @@@ blq) (bls
    :: blp @@@ blq). (Sing * bln) -> (Sing (TyPi bln (AD bln)) blo) -> (Sing (TyPi bln (AQ bln blo)) blp) -> (Sing bln
    blq) -> (Sing (blo @@@ blq) blr) -> (Sing (blp @@@ blq) bls) -> Ex2 {- KIND -} bln {- KIND -} blo {- KIND -} blp
$(P.return [])
type instance (@@) (BI bmh bmg bmf bme bmd bmc bmb bma blz bly blx) blw = Ex2 bmh bmg bmf
$(P.return [])
type instance (@@) (BG bms bmr bmq bmp bmo bmn bmm bml bmk bmj) bmi = TyPi (Sing (bmq @@@ bmp) bmn) (BI bms bmr bmq bmp
  bmo bmn bmm bml bmk bmj bmi)
$(P.return [])
type instance (@@) (BE bnc bnb bna bmz bmy bmx bmw bmv bmu) bmt = TyPi (Sing (bnb @@@ bmz) bmy) (BG bnc bnb bna bmz bmy
  bmx bmw bmv bmu bmt)
$(P.return [])
type instance (@@) (BC bnl bnk bnj bni bnh bng bnf bne) bnd = TyPi (Sing bnl bni) (BE bnl bnk bnj bni bnh bng bnf bne
  bnd)
$(P.return [])
type instance (@@) (BA bnt bns bnr bnq bnp bno bnn) bnm = TyPi (Sing (TyPi bnt (AQ bnt bns)) bnr) (BC bnt bns bnr bnq
  bnp bno bnn bnm)
$(P.return [])
type instance (@@) (AY boa bnz bny bnx bnw bnv) bnu = TyPi (Sing (TyPi boa (AD boa)) bnz) (BA boa bnz bny bnx bnw bnv
  bnu)
$(P.return [])
data AX (boh :: *) (bog :: TyPi boh (AD boh)) (bof :: TyPi boh (AQ boh bog)) (boe :: boh) (bod :: bog @@@ boe) (boc :: bof @@@ boe) (bob :: TyPi' (Sing * boh) (AY boh bog bof boe bod boc))
$(P.return [])
data AZ (bop :: *) (boo :: TyPi bop (AD bop)) (bon :: TyPi bop (AQ bop boo)) (bom :: bop) (bol :: boo @@@ bom) (bok :: bon @@@ bom) (boj :: Sing * bop) (boi :: TyPi' (Sing (TyPi bop (AD bop)) boo) (BA bop boo bon bom bol bok boj))
$(P.return [])
type instance (@@@) (AX bow bov bou bot bos bor) boq = AZ bow bov bou bot bos bor boq
-- $(P.return [])
-- data BB (bpf :: *) (bpe :: TyPi bpf (AD bpf)) (bpd :: TyPi bpf (AQ bpf bpe)) (bpc :: bpf) (bpb :: bpe @@@ bpc) (bpa :: bpd @@@ bpc) (boz :: Sing * bpf) (boy :: Sing (TyPi bpf (AD bpf)) bpe) (box :: TyPi' (Sing (TyPi bpf (AQ bpf bpe)) bpd) (BC bpf bpe bpd bpc bpb bpa boz boy))
-- $(P.return [])
-- type instance (@@@) (AZ bpn bpm bpl bpk bpj bpi bph) bpg = BB bpn bpm bpl bpk bpj bpi bph bpg
-- $(P.return [])
-- data BD (bpx :: *) (bpw :: TyPi bpx (AD bpx)) (bpv :: TyPi bpx (AQ bpx bpw)) (bpu :: bpx) (bpt :: bpw @@@ bpu) (bps :: bpv @@@ bpu) (bpr :: Sing * bpx) (bpq :: Sing (TyPi bpx (AD bpx)) bpw) (bpp :: Sing (TyPi bpx (AQ bpx bpw)) bpv) (bpo :: TyPi' (Sing bpx bpu) (BE bpx bpw bpv bpu bpt bps bpr bpq bpp))
-- $(P.return [])
-- type instance (@@@) (BB bqg bqf bqe bqd bqc bqb bqa bpz) bpy = BD bqg bqf bqe bqd bqc bqb bqa bpz bpy
-- $(P.return [])
-- data BF (bqr :: *) (bqq :: TyPi bqr (AD bqr)) (bqp :: TyPi bqr (AQ bqr bqq)) (bqo :: bqr) (bqn :: bqq @@@ bqo) (bqm :: bqp @@@ bqo) (bql :: Sing * bqr) (bqk :: Sing (TyPi bqr (AD bqr)) bqq) (bqj :: Sing (TyPi bqr (AQ bqr bqq)) bqp) (bqi :: Sing bqr bqo) (bqh :: TyPi' (Sing (bqq @@@ bqo) bqn) (BG bqr bqq bqp bqo bqn bqm bql bqk bqj bqi))
-- $(P.return [])
-- type instance (@@@) (BD brb bra bqz bqy bqx bqw bqv bqu bqt) bqs = BF brb bra bqz bqy bqx bqw bqv bqu bqt bqs
-- $(P.return [])
-- data BH (brn :: *) (brm :: TyPi brn (AD brn)) (brl :: TyPi brn (AQ brn brm)) (brk :: brn) (brj :: brm @@@ brk) (bri :: brl @@@ brk) (brh :: Sing * brn) (brg :: Sing (TyPi brn (AD brn)) brm) (brf :: Sing (TyPi brn (AQ brn brm)) brl) (bre :: Sing brn brk) (brd :: Sing (brm @@@ brk) brj) (brc :: TyPi' (Sing (brl @@@ brk) bri) (BI brn brm brl brk brj bri brh brg brf bre brd))
-- $(P.return [])
-- type instance (@@@) (BF bry brx brw brv bru brt brs brr brq brp) bro = BH bry brx brw brv bru brt brs brr brq brp bro
-- $(P.return [])
-- type instance (@@@) (BH bsk bsj bsi bsh bsg bsf bse bsd bsc bsb bsa) brz = 'Ex_intro2 bse bsd bsc bsb bsa brz
-- $(P.return [])
-- data instance Sing (Ex2 bsy bsz bta) bsx where
--   SEx_intro2 ::
--     forall (bsl :: *) (bsm :: TyPi bsl (AD bsl)) (bsn :: TyPi bsl (AQ bsl bsm)) (bso :: bsl) (bsp :: bsm @@@ bso) (bsq
--     :: bsn @@@ bso) (bsr :: Sing * bsl) (bss :: Sing (TyPi bsl (AD bsl)) bsm) (bst :: Sing (TyPi bsl (AQ bsl bsm)) bsn)
--     (bsu :: Sing bsl bso) (bsv :: Sing (bsm @@@ bso) bsp) (bsw :: Sing (bsn @@@ bso) bsq). (Sing * bsl) -> (Sing (TyPi
--     bsl (AD bsl)) bsm) -> (Sing (TyPi bsl (AQ bsl bsm)) bsn) -> (Sing bsl bso) -> (Sing (bsm @@@ bso) bsp) -> (Sing
--     (bsn @@@ bso) bsq) -> Sing' ('Ex_intro2 bsr bss bst bsu bsv bsw)
-- $(P.return [])
-- data AS (btb :: TyFun' * *)
-- $(P.return [])
-- data AU (btd :: *) (btc :: TyFun' (TyPi btd (AD btd)) *)
-- $(P.return [])
-- data AW (btg :: *) (btf :: TyPi btg (AD btg)) (bte :: TyFun' (TyPi btg (AQ btg btf)) *)
-- $(P.return [])
-- type instance (@@) (AW btj bti) bth = *
-- $(P.return [])
-- type instance (@@) (AU btl) btk = TyPi (TyPi btl (AQ btl btk)) (AW btl btk)
-- $(P.return [])
-- type instance (@@) AS btm = TyPi (TyPi btm (AD btm)) (AU btm)
-- $(P.return [])
-- data AR (btn :: TyPi' * AS)
-- $(P.return [])
-- data AT (btp :: *) (bto :: TyPi' (TyPi btp (AD btp)) (AU btp))
-- $(P.return [])
-- type instance (@@@) AR btq = AT btq
-- $(P.return [])
-- data AV (btt :: *) (bts :: TyPi btt (AD btt)) (btr :: TyPi' (TyPi btt (AQ btt bts)) (AW btt bts))
-- $(P.return [])
-- type instance (@@@) (AT btv) btu = AV btv btu
-- $(P.return [])
-- type instance (@@@) (AV bty btx) btw = Ex2 bty btx btw
-- $(P.return [])
-- data AJ (bud :: *) (buc :: TyPi bud (AD bud)) (bub :: bud) (bua :: buc @@@ bub) (btz :: TyFun' (Sing * bud) *)
-- $(P.return [])
-- data AL (buj :: *) (bui :: TyPi buj (AD buj)) (buh :: buj) (bug :: bui @@@ buh) (buf :: Sing * buj) (bue :: TyFun' (Sing (TyPi buj (AD buj)) bui) *)
-- $(P.return [])
-- data AN (buq :: *) (bup :: TyPi buq (AD buq)) (buo :: buq) (bun :: bup @@@ buo) (bum :: Sing * buq) (bul :: Sing (TyPi buq (AD buq)) bup) (buk :: TyFun' (Sing buq buo) *)
-- $(P.return [])
-- data AP (buy :: *) (bux :: TyPi buy (AD buy)) (buw :: buy) (buv :: bux @@@ buw) (buu :: Sing * buy) (but :: Sing (TyPi buy (AD buy)) bux) (bus :: Sing buy buw) (bur :: TyFun' (Sing (bux @@@ buw) buv) *)
-- $(P.return [])
-- data Ex (bvd :: *) (bve :: TyPi bvd (AD bvd)) :: * where
--   Ex_intro ::
--     forall (buz :: *) (bva :: TyPi buz (AD buz)) (bvb :: buz) (bvc :: bva @@@ bvb). (Sing * buz) -> (Sing (TyPi buz (AD
--     buz)) bva) -> (Sing buz bvb) -> (Sing (bva @@@ bvb) bvc) -> Ex {- KIND -} buz {- KIND -} bva
-- $(P.return [])
-- type instance (@@) (AP bvm bvl bvk bvj bvi bvh bvg) bvf = Ex bvm bvl
-- $(P.return [])
-- type instance (@@) (AN bvt bvs bvr bvq bvp bvo) bvn = TyPi (Sing (bvs @@@ bvr) bvq) (AP bvt bvs bvr bvq bvp bvo bvn)
-- $(P.return [])
-- type instance (@@) (AL bvz bvy bvx bvw bvv) bvu = TyPi (Sing bvz bvx) (AN bvz bvy bvx bvw bvv bvu)
-- $(P.return [])
-- type instance (@@) (AJ bwe bwd bwc bwb) bwa = TyPi (Sing (TyPi bwe (AD bwe)) bwd) (AL bwe bwd bwc bwb bwa)
-- $(P.return [])
-- data AI (bwj :: *) (bwi :: TyPi bwj (AD bwj)) (bwh :: bwj) (bwg :: bwi @@@ bwh) (bwf :: TyPi' (Sing * bwj) (AJ bwj bwi bwh bwg))
-- $(P.return [])
-- data AK (bwp :: *) (bwo :: TyPi bwp (AD bwp)) (bwn :: bwp) (bwm :: bwo @@@ bwn) (bwl :: Sing * bwp) (bwk :: TyPi' (Sing (TyPi bwp (AD bwp)) bwo) (AL bwp bwo bwn bwm bwl))
-- $(P.return [])
-- type instance (@@@) (AI bwu bwt bws bwr) bwq = AK bwu bwt bws bwr bwq
-- $(P.return [])
-- data AM (bxb :: *) (bxa :: TyPi bxb (AD bxb)) (bwz :: bxb) (bwy :: bxa @@@ bwz) (bwx :: Sing * bxb) (bww :: Sing (TyPi bxb (AD bxb)) bxa) (bwv :: TyPi' (Sing bxb bwz) (AN bxb bxa bwz bwy bwx bww))
-- $(P.return [])
-- type instance (@@@) (AK bxh bxg bxf bxe bxd) bxc = AM bxh bxg bxf bxe bxd bxc
-- $(P.return [])
-- data AO (bxp :: *) (bxo :: TyPi bxp (AD bxp)) (bxn :: bxp) (bxm :: bxo @@@ bxn) (bxl :: Sing * bxp) (bxk :: Sing (TyPi bxp (AD bxp)) bxo) (bxj :: Sing bxp bxn) (bxi :: TyPi' (Sing (bxo @@@ bxn) bxm) (AP bxp bxo bxn bxm bxl bxk bxj))
-- $(P.return [])
-- type instance (@@@) (AM bxw bxv bxu bxt bxs bxr) bxq = AO bxw bxv bxu bxt bxs bxr bxq
-- $(P.return [])
-- type instance (@@@) (AO bye byd byc byb bya bxz bxy) bxx = 'Ex_intro bya bxz bxy bxx
-- $(P.return [])
-- data instance Sing (Ex byo byp) byn where
--   SEx_intro ::
--     forall (byf :: *) (byg :: TyPi byf (AD byf)) (byh :: byf) (byi :: byg @@@ byh) (byj :: Sing * byf) (byk :: Sing
--     (TyPi byf (AD byf)) byg) (byl :: Sing byf byh) (bym :: Sing (byg @@@ byh) byi). (Sing * byf) -> (Sing (TyPi byf (AD
--     byf)) byg) -> (Sing byf byh) -> (Sing (byg @@@ byh) byi) -> Sing' ('Ex_intro byj byk byl bym)
-- $(P.return [])
-- data AF (byq :: TyFun' * *)
-- $(P.return [])
-- data AH (bys :: *) (byr :: TyFun' (TyPi bys (AD bys)) *)
-- $(P.return [])
-- type instance (@@) (AH byu) byt = *
-- $(P.return [])
-- type instance (@@) AF byv = TyPi (TyPi byv (AD byv)) (AH byv)
-- $(P.return [])
-- data AE (byw :: TyPi' * AF)
-- $(P.return [])
-- data AG (byy :: *) (byx :: TyPi' (TyPi byy (AD byy)) (AH byy))
-- $(P.return [])
-- type instance (@@@) AE byz = AG byz
-- $(P.return [])
-- type instance (@@@) (AG bzb) bza = Ex bzb bza
-- $(P.return [])
-- data Y (bzf :: *) (bze :: *) (bzd :: bze) (bzc :: TyFun' (Sing * bzf) *)
-- $(P.return [])
-- data AA (bzk :: *) (bzj :: *) (bzi :: bzj) (bzh :: Sing * bzk) (bzg :: TyFun' (Sing * bzj) *)
-- $(P.return [])
-- data AC (bzq :: *) (bzp :: *) (bzo :: bzp) (bzn :: Sing * bzq) (bzm :: Sing * bzp) (bzl :: TyFun' (Sing bzp bzo) *)
-- $(P.return [])
-- data Or (bzx :: *) (bzy :: *) :: * where
--   Or_introl ::
--     forall (bzr :: *) (bzs :: *) (bzt :: bzr). (Sing * bzr) -> (Sing * bzs) -> (Sing bzr bzt) -> Or {- KIND -} bzr
--     {- KIND -} bzs
--   Or_intror ::
--     forall (bzu :: *) (bzv :: *) (bzw :: bzv). (Sing * bzu) -> (Sing * bzv) -> (Sing bzv bzw) -> Or {- KIND -} bzu
--     {- KIND -} bzv
-- $(P.return [])
-- type instance (@@) (AC cae cad cac cab caa) bzz = Or cae cad
-- $(P.return [])
-- type instance (@@) (AA caj cai cah cag) caf = TyPi (Sing cai cah) (AC caj cai cah cag caf)
-- $(P.return [])
-- type instance (@@) (Y can cam cal) cak = TyPi (Sing * cam) (AA can cam cal cak)
-- $(P.return [])
-- data X (car :: *) (caq :: *) (cap :: caq) (cao :: TyPi' (Sing * car) (Y car caq cap))
-- $(P.return [])
-- data Z (caw :: *) (cav :: *) (cau :: cav) (cat :: Sing * caw) (cas :: TyPi' (Sing * cav) (AA caw cav cau cat))
-- $(P.return [])
-- type instance (@@@) (X cba caz cay) cax = Z cba caz cay cax
-- $(P.return [])
-- data AB (cbg :: *) (cbf :: *) (cbe :: cbf) (cbd :: Sing * cbg) (cbc :: Sing * cbf) (cbb :: TyPi' (Sing cbf cbe) (AC cbg cbf cbe cbd cbc))
-- $(P.return [])
-- type instance (@@@) (Z cbl cbk cbj cbi) cbh = AB cbl cbk cbj cbi cbh
-- $(P.return [])
-- type instance (@@@) (AB cbr cbq cbp cbo cbn) cbm = 'Or_intror cbo cbn cbm
-- $(P.return [])
-- data S (cbv :: *) (cbu :: *) (cbt :: cbv) (cbs :: TyFun' (Sing * cbv) *)
-- $(P.return [])
-- data U (cca :: *) (cbz :: *) (cby :: cca) (cbx :: Sing * cca) (cbw :: TyFun' (Sing * cbz) *)
-- $(P.return [])
-- data W (ccg :: *) (ccf :: *) (cce :: ccg) (ccd :: Sing * ccg) (ccc :: Sing * ccf) (ccb :: TyFun' (Sing ccg cce) *)
-- $(P.return [])
-- type instance (@@) (W ccm ccl cck ccj cci) cch = Or ccm ccl
-- $(P.return [])
-- type instance (@@) (U ccr ccq ccp cco) ccn = TyPi (Sing ccr ccp) (W ccr ccq ccp cco ccn)
-- $(P.return [])
-- type instance (@@) (S ccv ccu cct) ccs = TyPi (Sing * ccu) (U ccv ccu cct ccs)
-- $(P.return [])
-- data R (ccz :: *) (ccy :: *) (ccx :: ccz) (ccw :: TyPi' (Sing * ccz) (S ccz ccy ccx))
-- $(P.return [])
-- data T (cde :: *) (cdd :: *) (cdc :: cde) (cdb :: Sing * cde) (cda :: TyPi' (Sing * cdd) (U cde cdd cdc cdb))
-- $(P.return [])
-- type instance (@@@) (R cdi cdh cdg) cdf = T cdi cdh cdg cdf
-- $(P.return [])
-- data V (cdo :: *) (cdn :: *) (cdm :: cdo) (cdl :: Sing * cdo) (cdk :: Sing * cdn) (cdj :: TyPi' (Sing cdo cdm) (W cdo cdn cdm cdl cdk))
-- $(P.return [])
-- type instance (@@@) (T cdt cds cdr cdq) cdp = V cdt cds cdr cdq cdp
-- $(P.return [])
-- type instance (@@@) (V cdz cdy cdx cdw cdv) cdu = 'Or_introl cdw cdv cdu
-- $(P.return [])
-- data instance Sing (Or cen ceo) cem where
--   SOr_introl ::
--     forall (cea :: *) (ceb :: *) (cec :: cea) (ced :: Sing * cea) (cee :: Sing * ceb) (cef :: Sing cea cec). (Sing *
--     cea) -> (Sing * ceb) -> (Sing cea cec) -> Sing' ('Or_introl ced cee cef)
--   SOr_intror ::
--     forall (ceg :: *) (ceh :: *) (cei :: ceh) (cej :: Sing * ceg) (cek :: Sing * ceh) (cel :: Sing ceh cei). (Sing *
--     ceg) -> (Sing * ceh) -> (Sing ceh cei) -> Sing' ('Or_intror cej cek cel)
-- $(P.return [])
-- data O (cep :: TyFun' * *)
-- $(P.return [])
-- data Q (cer :: *) (ceq :: TyFun' * *)
-- $(P.return [])
-- type instance (@@) (Q cet) ces = *
-- $(P.return [])
-- type instance (@@) O ceu = TyPi * (Q ceu)
-- $(P.return [])
-- data N (cev :: TyPi' * O)
-- $(P.return [])
-- data P (cex :: *) (cew :: TyPi' * (Q cex))
-- $(P.return [])
-- type instance (@@@) N cey = P cey
-- $(P.return [])
-- type instance (@@@) (P cfa) cez = Or cfa cez
-- $(P.return [])
-- data F (cff :: *) (cfe :: *) (cfd :: cff) (cfc :: cfe) (cfb :: TyFun' (Sing * cff) *)
-- $(P.return [])
-- data H (cfl :: *) (cfk :: *) (cfj :: cfl) (cfi :: cfk) (cfh :: Sing * cfl) (cfg :: TyFun' (Sing * cfk) *)
-- $(P.return [])
-- data K (cfs :: *) (cfr :: *) (cfq :: cfs) (cfp :: cfr) (cfo :: Sing * cfs) (cfn :: Sing * cfr) (cfm :: TyFun' (Sing cfs cfq) *)
-- $(P.return [])
-- data M (cga :: *) (cfz :: *) (cfy :: cga) (cfx :: cfz) (cfw :: Sing * cga) (cfv :: Sing * cfz) (cfu :: Sing cga cfy) (cft :: TyFun' (Sing cfz cfx) *)
-- $(P.return [])
-- data And (cgf :: *) (cgg :: *) :: * where
--   Conj ::
--     forall (cgb :: *) (cgc :: *) (cgd :: cgb) (cge :: cgc). (Sing * cgb) -> (Sing * cgc) -> (Sing cgb cgd) -> (Sing cgc
--     cge) -> And {- KIND -} cgb {- KIND -} cgc
-- $(P.return [])
-- type instance (@@) (M cgo cgn cgm cgl cgk cgj cgi) cgh = And cgo cgn
-- $(P.return [])
-- type instance (@@) (K cgv cgu cgt cgs cgr cgq) cgp = TyPi (Sing cgu cgs) (M cgv cgu cgt cgs cgr cgq cgp)
-- $(P.return [])
-- type instance (@@) (H chb cha cgz cgy cgx) cgw = TyPi (Sing chb cgz) (K chb cha cgz cgy cgx cgw)
-- $(P.return [])
-- type instance (@@) (F chg chf che chd) chc = TyPi (Sing * chf) (H chg chf che chd chc)
-- $(P.return [])
-- data E (chl :: *) (chk :: *) (chj :: chl) (chi :: chk) (chh :: TyPi' (Sing * chl) (F chl chk chj chi))
-- $(P.return [])
-- data G (chr :: *) (chq :: *) (chp :: chr) (cho :: chq) (chn :: Sing * chr) (chm :: TyPi' (Sing * chq) (H chr chq chp cho chn))
-- $(P.return [])
-- type instance (@@@) (E chw chv chu cht) chs = G chw chv chu cht chs
-- $(P.return [])
-- data J (cid :: *) (cic :: *) (cib :: cid) (cia :: cic) (chz :: Sing * cid) (chy :: Sing * cic) (chx :: TyPi' (Sing cid cib) (K cid cic cib cia chz chy))
-- $(P.return [])
-- type instance (@@@) (G cij cii cih cig cif) cie = J cij cii cih cig cif cie
-- $(P.return [])
-- data L (cir :: *) (ciq :: *) (cip :: cir) (cio :: ciq) (cin :: Sing * cir) (cim :: Sing * ciq) (cil :: Sing cir cip) (cik :: TyPi' (Sing ciq cio) (M cir ciq cip cio cin cim cil))
-- $(P.return [])
-- type instance (@@@) (J ciy cix ciw civ ciu cit) cis = L ciy cix ciw civ ciu cit cis
-- $(P.return [])
-- type instance (@@@) (L cjg cjf cje cjd cjc cjb cja) ciz = 'Conj cjc cjb cja ciz
-- $(P.return [])
-- data instance Sing (And cjq cjr) cjp where
--   SConj ::
--     forall (cjh :: *) (cji :: *) (cjj :: cjh) (cjk :: cji) (cjl :: Sing * cjh) (cjm :: Sing * cji) (cjn :: Sing cjh
--     cjj) (cjo :: Sing cji cjk). (Sing * cjh) -> (Sing * cji) -> (Sing cjh cjj) -> (Sing cji cjk) -> Sing' ('Conj cjl
--     cjm cjn cjo)
-- $(P.return [])
-- data B (cjs :: TyFun' * *)
-- $(P.return [])
-- data D (cju :: *) (cjt :: TyFun' * *)
-- $(P.return [])
-- type instance (@@) (D cjw) cjv = *
-- $(P.return [])
-- type instance (@@) B cjx = TyPi * (D cjx)
-- $(P.return [])
-- data A (cjy :: TyPi' * B)
-- $(P.return [])
-- data C (cka :: *) (cjz :: TyPi' * (D cka))
-- $(P.return [])
-- type instance (@@@) A ckb = C ckb
-- $(P.return [])
-- type instance (@@@) (C ckd) ckc = And ckd ckc
-- $(P.return [])
-- data False :: * where
  
-- $(P.return [])
-- data instance Sing False cke where
  
-- $(P.return [])
-- data True :: * where
--   I ::   True
-- $(P.return [])
-- data instance Sing True ckf where
--   SI ::   Sing' 'I
