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
data IL (a :: TyFun' Nat *)
$(P.return [])
data T (d :: Nat) :: * where
  F1 ::   forall (b :: Nat). (Sing Nat b) -> T ('S {- KIND -} b)
  FS ::   forall (c :: Nat). (Sing Nat c) -> (T {- KIND -} c) -> T ('S {- KIND -} c)
$(P.return [])
data IG (f :: Nat) (e :: TyFun' (T f) *)
$(P.return [])
data IF (i :: Nat) (h :: T i) (g :: TyFun' (T i) *)
$(P.return [])
data Eq (l :: *) (m :: l) (n :: l) :: * where
  Eq_refl ::   forall (j :: *) (k :: j). (Sing * j) -> (Sing j k) -> Eq {- KIND -} j {- KIND -} k {- KIND -} k
$(P.return [])
data IE (r :: Nat) (q :: T r) (p :: T r) (o :: TyFun' (Eq (T ('S r)) ('FS (ToSing r) q) ('FS (ToSing r) p)) *)
$(P.return [])
type instance (@@) (IE v u t) s = Eq (T v) u t
$(P.return [])
type instance (@@) (IF y x) w = TyPi (Eq (T ('S y)) ('FS (ToSing y) x) ('FS (ToSing y) w)) (IE y x w)
$(P.return [])
type instance (@@) (IG aa) z = TyPi (T aa) (IF aa z)
$(P.return [])
type instance (@@) IL ab = TyPi (T ab) (IG ab)
$(P.return [])
data IK (ac :: TyPi' Nat IL)
$(P.return [])
fS_inj :: Sing' {- KIND -} IK
fS_inj = SLambda (\ad -> SLambda (\ae -> SLambda (\af -> SLambda (\ag -> P.undefined))))

$(P.return [])
data IJ (ai :: Nat) (ah :: TyPi' (T ai) (IG ai))
$(P.return [])
type instance (@@@) IK aj = IJ aj
$(P.return [])
data II (am :: Nat) (al :: T am) (ak :: TyPi' (T am) (IF am al))
$(P.return [])
type instance (@@@) (IJ ao) an = II ao an
$(P.return [])
data IH (as :: Nat) (ar :: T as) (aq :: T as) (ap :: TyPi' (Eq (T ('S as)) ('FS (ToSing as) ar) ('FS (ToSing as) aq)) (IE as ar aq))
$(P.return [])
type instance (@@@) (II av au) at = IH av au at
$(P.return [])
type instance (@@@) (IH az ay ax) aw = UNKNOWN
$(P.return [])
data ID (ba :: TyFun' * *)
$(P.return [])
type instance (@@) ID bb = *
$(P.return [])
data IC (bc :: TyPi' * ID)
$(P.return [])
not :: Sing' {- KIND -} IC
not = SLambda (\bd -> SStar)

$(P.return [])
data IB (bf :: *) (be :: TyFun' bf *)
$(P.return [])
data False :: * where
  
$(P.return [])
type instance (@@) (IB bh) bg = False
$(P.return [])
type instance (@@@) IC bi = TyPi bi (IB bi)
$(P.return [])
data IA (bj :: TyFun' * *)
$(P.return [])
data HX (bl :: *) (bk :: TyFun' bl *)
$(P.return [])
type instance (@@) (HX bn) bm = bn
$(P.return [])
type instance (@@) IA bo = TyPi bo (HX bo)
$(P.return [])
data HZ (bp :: TyPi' * IA)
$(P.return [])
id :: Sing' {- KIND -} HZ
id = SLambda (\bq -> SLambda (\br -> br))

$(P.return [])
data HY (bt :: *) (bs :: TyPi' bt (HX bt))
$(P.return [])
type instance (@@@) HZ bu = HY bu
$(P.return [])
type instance (@@@) (HY bw) bv = bv
$(P.return [])
data HU (by :: UNKNOWN) (bx :: TyFun' (Sing Nat by) *)
$(P.return [])
data HW (cb :: UNKNOWN) (ca :: Sing Nat cb) (bz :: TyFun' (T cb) *)
$(P.return [])
type instance (@@) (HW ce cd) cc = T ('S ce)
$(P.return [])
type instance (@@) (HU cg) cf = TyPi (T cg) (HW cg cf)
$(P.return [])
data HT (ci :: UNKNOWN) (ch :: TyPi' (Sing Nat ci) (HU ci))
$(P.return [])
data HV (cl :: UNKNOWN) (ck :: Sing Nat cl) (cj :: TyPi' (T cl) (HW cl ck))
$(P.return [])
type instance (@@@) (HT cn) cm = HV cn cm
$(P.return [])
type instance (@@@) (HV cq cp) co = 'FS cq cp co
$(P.return [])
data HS (cs :: UNKNOWN) (cr :: TyFun' (Sing Nat cs) *)
$(P.return [])
type instance (@@) (HS cu) ct = T ('S cu)
$(P.return [])
data HR (cw :: UNKNOWN) (cv :: TyPi' (Sing Nat cw) (HS cw))
$(P.return [])
type instance (@@@) (HR cy) cx = 'F1 cy cx
$(P.return [])
data instance Sing (T df) de where
  SF1 ::   forall (cz :: Nat) (da :: Sing Nat cz). (Sing Nat cz) -> Sing' ('F1 da)
  SFS ::   forall (db :: Nat) (dc :: Sing Nat db) (dd :: T db). (Sing Nat db) -> (Sing (T db) dd) -> Sing' ('FS dc dd)
$(P.return [])
data HP (dg :: TyFun' Nat *)
$(P.return [])
type instance (@@) HP dh = *
$(P.return [])
data HO (di :: TyPi' Nat HP)
$(P.return [])
type instance (@@@) HO dj = T dj
$(P.return [])
data HK (dm :: UNKNOWN) (dl :: UNKNOWN) (dk :: TyFun' (Sing * dm) *)
$(P.return [])
data HM (dr :: UNKNOWN) (dq :: UNKNOWN) (dp :: Sing * dr) (dn :: TyFun' (Sing dr dq) *)
$(P.return [])
data Identity (du :: *) (dv :: du) (dw :: du) :: * where
  Identity_refl ::
    forall (ds :: *) (dt :: ds). (Sing * ds) -> (Sing ds dt) -> Identity {- KIND -} ds {- KIND -} dt {- KIND -} dt
$(P.return [])
type instance (@@) (HM ea dz dy) dx = Identity ea dz dz
$(P.return [])
type instance (@@) (HK ed ec) eb = TyPi (Sing ed ec) (HM ed ec eb)
$(P.return [])
data HJ (eg :: UNKNOWN) (ef :: UNKNOWN) (ee :: TyPi' (Sing * eg) (HK eg ef))
$(P.return [])
data HL (ek :: UNKNOWN) (ej :: UNKNOWN) (ei :: Sing * ek) (eh :: TyPi' (Sing ek ej) (HM ek ej ei))
$(P.return [])
type instance (@@@) (HJ en em) el = HL en em el
$(P.return [])
type instance (@@@) (HL er eq ep) eo = 'Identity_refl er eq ep eo
$(P.return [])
data instance Sing (Identity ex ey ez) ew where
  SIdentity_refl ::
    forall (es :: *) (et :: es) (eu :: Sing * es) (ev :: Sing es et). (Sing * es) -> (Sing es et) -> Sing'
    ('Identity_refl eu ev)
$(P.return [])
data HE (fa :: TyFun' * *)
$(P.return [])
data HG (fc :: *) (fb :: TyFun' fc *)
$(P.return [])
data HI (ff :: *) (fe :: ff) (fd :: TyFun' ff *)
$(P.return [])
type instance (@@) (HI fi fh) fg = *
$(P.return [])
type instance (@@) (HG fk) fj = TyPi fk (HI fk fj)
$(P.return [])
type instance (@@) HE fl = TyPi fl (HG fl)
$(P.return [])
data HD (fm :: TyPi' * HE)
$(P.return [])
data HF (fo :: *) (fn :: TyPi' fo (HG fo))
$(P.return [])
type instance (@@@) HD fp = HF fp
$(P.return [])
data HH (fs :: *) (fr :: fs) (fq :: TyPi' fs (HI fs fr))
$(P.return [])
type instance (@@@) (HF fu) ft = HH fu ft
$(P.return [])
type instance (@@@) (HH fx fw) fv = Identity fx fw fv
$(P.return [])
data GW (gc :: UNKNOWN) (gb :: UNKNOWN) (ga :: UNKNOWN) (fz :: UNKNOWN) (fy :: TyFun' (Sing * gc) *)
$(P.return [])
data GY (gi :: UNKNOWN) (gh :: UNKNOWN) (gg :: UNKNOWN) (gf :: UNKNOWN) (ge :: Sing * gi) (gd :: TyFun' (Sing * gh) *)
$(P.return [])
data HA (gp :: UNKNOWN) (go :: UNKNOWN) (gn :: UNKNOWN) (gm :: UNKNOWN) (gl :: Sing * gp) (gk :: Sing * go) (gj :: TyFun' (Sing * gn) *)
$(P.return [])
data HC (gx :: UNKNOWN) (gw :: UNKNOWN) (gv :: UNKNOWN) (gu :: UNKNOWN) (gt :: Sing * gx) (gs :: Sing * gw) (gr :: Sing * gv) (gq :: TyFun' (Sing gv gu) *)
$(P.return [])
data Comparison :: * where
  Eq ::   Comparison
  Lt ::   Comparison
  Gt ::   Comparison
$(P.return [])
data CompareSpecT (hk :: *) (hl :: *) (hm :: *) (hn :: Comparison) :: * where
  CompEqT ::
    forall (gy :: *) (gz :: *) (ha :: *) (hb :: gy). (Sing * gy) -> (Sing * gz) -> (Sing * ha) -> (Sing gy hb) ->
    CompareSpecT {- KIND -} gy {- KIND -} gz {- KIND -} ha 'Eq
  CompLtT ::
    forall (hc :: *) (hd :: *) (he :: *) (hf :: hd). (Sing * hc) -> (Sing * hd) -> (Sing * he) -> (Sing hd hf) ->
    CompareSpecT {- KIND -} hc {- KIND -} hd {- KIND -} he 'Lt
  CompGtT ::
    forall (hg :: *) (hh :: *) (hi :: *) (hj :: hi). (Sing * hg) -> (Sing * hh) -> (Sing * hi) -> (Sing hi hj) ->
    CompareSpecT {- KIND -} hg {- KIND -} hh {- KIND -} hi 'Gt
$(P.return [])
type instance (@@) (HC hv hu ht hs hr hq hp) ho = CompareSpecT hv hu ht 'Gt
$(P.return [])
type instance (@@) (HA ic ib ia hz hy hx) hw = TyPi (Sing ia hz) (HC ic ib ia hz hy hx hw)
$(P.return [])
type instance (@@) (GY ij ii ih ig ie) id = TyPi (Sing * ih) (HA ij ii ih ig ie id)
$(P.return [])
type instance (@@) (GW ip io im il) ik = TyPi (Sing * io) (GY ip io im il ik)
$(P.return [])
data GV (iu :: UNKNOWN) (it :: UNKNOWN) (is :: UNKNOWN) (ir :: UNKNOWN) (iq :: TyPi' (Sing * iu) (GW iu it is ir))
$(P.return [])
data GX (ja :: UNKNOWN) (iz :: UNKNOWN) (iy :: UNKNOWN) (ix :: UNKNOWN) (iw :: Sing * ja) (iv :: TyPi' (Sing * iz) (GY ja iz iy ix iw))
$(P.return [])
type instance (@@@) (GV jf je jd jc) jb = GX jf je jd jc jb
$(P.return [])
data GZ (jm :: UNKNOWN) (jl :: UNKNOWN) (jk :: UNKNOWN) (jj :: UNKNOWN) (ji :: Sing * jm) (jh :: Sing * jl) (jg :: TyPi' (Sing * jk) (HA jm jl jk jj ji jh))
$(P.return [])
type instance (@@@) (GX js jr jq jp jo) jn = GZ js jr jq jp jo jn
$(P.return [])
data HB (ka :: UNKNOWN) (jz :: UNKNOWN) (jy :: UNKNOWN) (jx :: UNKNOWN) (jw :: Sing * ka) (jv :: Sing * jz) (ju :: Sing * jy) (jt :: TyPi' (Sing jy jx) (HC ka jz jy jx jw jv ju))
$(P.return [])
type instance (@@@) (GZ kh kg kf ke kd kc) kb = HB kh kg kf ke kd kc kb
$(P.return [])
type instance (@@@) (HB kp ko kn km kl kk kj) ki = 'CompGtT kp ko kn km kl kk kj ki
$(P.return [])
data GO (ku :: UNKNOWN) (kt :: UNKNOWN) (ks :: UNKNOWN) (kr :: UNKNOWN) (kq :: TyFun' (Sing * ku) *)
$(P.return [])
data GQ (la :: UNKNOWN) (kz :: UNKNOWN) (ky :: UNKNOWN) (kx :: UNKNOWN) (kw :: Sing * la) (kv :: TyFun' (Sing * kz) *)
$(P.return [])
data GS (lh :: UNKNOWN) (lg :: UNKNOWN) (lf :: UNKNOWN) (le :: UNKNOWN) (ld :: Sing * lh) (lc :: Sing * lg) (lb :: TyFun' (Sing * lf) *)
$(P.return [])
data GU (lp :: UNKNOWN) (lo :: UNKNOWN) (ln :: UNKNOWN) (lm :: UNKNOWN) (ll :: Sing * lp) (lk :: Sing * lo) (lj :: Sing * ln) (li :: TyFun' (Sing lo lm) *)
$(P.return [])
type instance (@@) (GU lx lw lv lu lt ls lr) lq = CompareSpecT lx lw lv 'Lt
$(P.return [])
type instance (@@) (GS me md mc mb ma lz) ly = TyPi (Sing md mb) (GU me md mc mb ma lz ly)
$(P.return [])
type instance (@@) (GQ mk mj mi mh mg) mf = TyPi (Sing * mi) (GS mk mj mi mh mg mf)
$(P.return [])
type instance (@@) (GO mp mo mn mm) ml = TyPi (Sing * mo) (GQ mp mo mn mm ml)
$(P.return [])
data GN (mu :: UNKNOWN) (mt :: UNKNOWN) (ms :: UNKNOWN) (mr :: UNKNOWN) (mq :: TyPi' (Sing * mu) (GO mu mt ms mr))
$(P.return [])
data GP (na :: UNKNOWN) (mz :: UNKNOWN) (my :: UNKNOWN) (mx :: UNKNOWN) (mw :: Sing * na) (mv :: TyPi' (Sing * mz) (GQ na mz my mx mw))
$(P.return [])
type instance (@@@) (GN nf ne nd nc) nb = GP nf ne nd nc nb
$(P.return [])
data GR (nm :: UNKNOWN) (nl :: UNKNOWN) (nk :: UNKNOWN) (nj :: UNKNOWN) (ni :: Sing * nm) (nh :: Sing * nl) (ng :: TyPi' (Sing * nk) (GS nm nl nk nj ni nh))
$(P.return [])
type instance (@@@) (GP ns nr nq np no) nn = GR ns nr nq np no nn
$(P.return [])
data GT (oa :: UNKNOWN) (nz :: UNKNOWN) (ny :: UNKNOWN) (nx :: UNKNOWN) (nw :: Sing * oa) (nv :: Sing * nz) (nu :: Sing * ny) (nt :: TyPi' (Sing nz nx) (GU oa nz ny nx nw nv nu))
$(P.return [])
type instance (@@@) (GR oi oh og oe od oc) ob = GT oi oh og oe od oc ob
$(P.return [])
type instance (@@@) (GT oq op oo on om ol ok) oj = 'CompLtT oq op oo on om ol ok oj
$(P.return [])
data GG (ov :: UNKNOWN) (ou :: UNKNOWN) (ot :: UNKNOWN) (os :: UNKNOWN) (or :: TyFun' (Sing * ov) *)
$(P.return [])
data GI (pb :: UNKNOWN) (pa :: UNKNOWN) (oz :: UNKNOWN) (oy :: UNKNOWN) (ox :: Sing * pb) (ow :: TyFun' (Sing * pa) *)
$(P.return [])
data GK (pi :: UNKNOWN) (ph :: UNKNOWN) (pg :: UNKNOWN) (pf :: UNKNOWN) (pe :: Sing * pi) (pd :: Sing * ph) (pc :: TyFun' (Sing * pg) *)
$(P.return [])
data GM (pq :: UNKNOWN) (pp :: UNKNOWN) (po :: UNKNOWN) (pn :: UNKNOWN) (pm :: Sing * pq) (pl :: Sing * pp) (pk :: Sing * po) (pj :: TyFun' (Sing pq pn) *)
$(P.return [])
type instance (@@) (GM py px pw pv pu pt ps) pr = CompareSpecT py px pw 'Eq
$(P.return [])
type instance (@@) (GK qf qe qd qc qb qa) pz = TyPi (Sing qf qc) (GM qf qe qd qc qb qa pz)
$(P.return [])
type instance (@@) (GI ql qk qj qi qh) qg = TyPi (Sing * qj) (GK ql qk qj qi qh qg)
$(P.return [])
type instance (@@) (GG qq qp qo qn) qm = TyPi (Sing * qp) (GI qq qp qo qn qm)
$(P.return [])
data GF (qv :: UNKNOWN) (qu :: UNKNOWN) (qt :: UNKNOWN) (qs :: UNKNOWN) (qr :: TyPi' (Sing * qv) (GG qv qu qt qs))
$(P.return [])
data GH (rb :: UNKNOWN) (ra :: UNKNOWN) (qz :: UNKNOWN) (qy :: UNKNOWN) (qx :: Sing * rb) (qw :: TyPi' (Sing * ra) (GI rb ra qz qy qx))
$(P.return [])
type instance (@@@) (GF rg rf re rd) rc = GH rg rf re rd rc
$(P.return [])
data GJ (rn :: UNKNOWN) (rm :: UNKNOWN) (rl :: UNKNOWN) (rk :: UNKNOWN) (rj :: Sing * rn) (ri :: Sing * rm) (rh :: TyPi' (Sing * rl) (GK rn rm rl rk rj ri))
$(P.return [])
type instance (@@@) (GH rt rs rr rq rp) ro = GJ rt rs rr rq rp ro
$(P.return [])
data GL (sb :: UNKNOWN) (sa :: UNKNOWN) (rz :: UNKNOWN) (ry :: UNKNOWN) (rx :: Sing * sb) (rw :: Sing * sa) (rv :: Sing * rz) (ru :: TyPi' (Sing sb ry) (GM sb sa rz ry rx rw rv))
$(P.return [])
type instance (@@@) (GJ si sh sg sf se sd) sc = GL si sh sg sf se sd sc
$(P.return [])
type instance (@@@) (GL sq sp so sn sm sl sk) sj = 'CompEqT sq sp so sn sm sl sk sj
$(P.return [])
data instance Sing (CompareSpecT tq tr ts tt) tp where
  SCompEqT ::
    forall (sr :: *) (ss :: *) (st :: *) (su :: sr) (sv :: Sing * sr) (sw :: Sing * ss) (sx :: Sing * st) (sy :: Sing
    sr su). (Sing * sr) -> (Sing * ss) -> (Sing * st) -> (Sing sr su) -> Sing' ('CompEqT sv sw sx sy)
  SCompLtT ::
    forall (sz :: *) (ta :: *) (tb :: *) (tc :: ta) (td :: Sing * sz) (te :: Sing * ta) (tf :: Sing * tb) (tg :: Sing
    ta tc). (Sing * sz) -> (Sing * ta) -> (Sing * tb) -> (Sing ta tc) -> Sing' ('CompLtT td te tf tg)
  SCompGtT ::
    forall (th :: *) (ti :: *) (tj :: *) (tk :: tj) (tl :: Sing * th) (tm :: Sing * ti) (tn :: Sing * tj) (to :: Sing
    tj tk). (Sing * th) -> (Sing * ti) -> (Sing * tj) -> (Sing tj tk) -> Sing' ('CompGtT tl tm tn to)
$(P.return [])
data FY (tu :: TyFun' * *)
$(P.return [])
data GA (tw :: *) (tv :: TyFun' * *)
$(P.return [])
data GC (tz :: *) (ty :: *) (tx :: TyFun' * *)
$(P.return [])
data GE (ud :: *) (uc :: *) (ub :: *) (ua :: TyFun' Comparison *)
$(P.return [])
type instance (@@) (GE uh ug uf) ue = *
$(P.return [])
type instance (@@) (GC uk uj) ui = TyPi Comparison (GE uk uj ui)
$(P.return [])
type instance (@@) (GA um) ul = TyPi * (GC um ul)
$(P.return [])
type instance (@@) FY un = TyPi * (GA un)
$(P.return [])
data FX (uo :: TyPi' * FY)
$(P.return [])
data FZ (uq :: *) (up :: TyPi' * (GA uq))
$(P.return [])
type instance (@@@) FX ur = FZ ur
$(P.return [])
data GB (uu :: *) (ut :: *) (us :: TyPi' * (GC uu ut))
$(P.return [])
type instance (@@@) (FZ uw) uv = GB uw uv
$(P.return [])
data GD (va :: *) (uz :: *) (uy :: *) (ux :: TyPi' Comparison (GE va uz uy))
$(P.return [])
type instance (@@@) (GB vd vc) vb = GD vd vc vb
$(P.return [])
type instance (@@@) (GD vh vg vf) ve = CompareSpecT vh vg vf ve
$(P.return [])
data FQ (vm :: UNKNOWN) (vl :: UNKNOWN) (vk :: UNKNOWN) (vj :: UNKNOWN) (vi :: TyFun' (Sing * vm) *)
$(P.return [])
data FS (vs :: UNKNOWN) (vr :: UNKNOWN) (vq :: UNKNOWN) (vp :: UNKNOWN) (vo :: Sing * vs) (vn :: TyFun' (Sing * vr) *)
$(P.return [])
data FU (vz :: UNKNOWN) (vy :: UNKNOWN) (vx :: UNKNOWN) (vw :: UNKNOWN) (vv :: Sing * vz) (vu :: Sing * vy) (vt :: TyFun' (Sing * vx) *)
$(P.return [])
data FW (wh :: UNKNOWN) (wg :: UNKNOWN) (wf :: UNKNOWN) (we :: UNKNOWN) (wd :: Sing * wh) (wc :: Sing * wg) (wb :: Sing * wf) (wa :: TyFun' (Sing wf we) *)
$(P.return [])
data CompareSpec (wu :: *) (wv :: *) (ww :: *) (wx :: Comparison) :: * where
  CompEq ::
    forall (wi :: *) (wj :: *) (wk :: *) (wl :: wi). (Sing * wi) -> (Sing * wj) -> (Sing * wk) -> (Sing wi wl) ->
    CompareSpec {- KIND -} wi {- KIND -} wj {- KIND -} wk 'Eq
  CompLt ::
    forall (wm :: *) (wn :: *) (wo :: *) (wp :: wn). (Sing * wm) -> (Sing * wn) -> (Sing * wo) -> (Sing wn wp) ->
    CompareSpec {- KIND -} wm {- KIND -} wn {- KIND -} wo 'Lt
  CompGt ::
    forall (wq :: *) (wr :: *) (ws :: *) (wt :: ws). (Sing * wq) -> (Sing * wr) -> (Sing * ws) -> (Sing ws wt) ->
    CompareSpec {- KIND -} wq {- KIND -} wr {- KIND -} ws 'Gt
$(P.return [])
type instance (@@) (FW xf xe xd xc xb xa wz) wy = CompareSpec xf xe xd 'Gt
$(P.return [])
type instance (@@) (FU xm xl xk xj xi xh) xg = TyPi (Sing xk xj) (FW xm xl xk xj xi xh xg)
$(P.return [])
type instance (@@) (FS xs xr xq xp xo) xn = TyPi (Sing * xq) (FU xs xr xq xp xo xn)
$(P.return [])
type instance (@@) (FQ xx xw xv xu) xt = TyPi (Sing * xw) (FS xx xw xv xu xt)
$(P.return [])
data FP (yc :: UNKNOWN) (yb :: UNKNOWN) (ya :: UNKNOWN) (xz :: UNKNOWN) (xy :: TyPi' (Sing * yc) (FQ yc yb ya xz))
$(P.return [])
data FR (yi :: UNKNOWN) (yh :: UNKNOWN) (yg :: UNKNOWN) (yf :: UNKNOWN) (ye :: Sing * yi) (yd :: TyPi' (Sing * yh) (FS yi yh yg yf ye))
$(P.return [])
type instance (@@@) (FP yn ym yl yk) yj = FR yn ym yl yk yj
$(P.return [])
data FT (yu :: UNKNOWN) (yt :: UNKNOWN) (ys :: UNKNOWN) (yr :: UNKNOWN) (yq :: Sing * yu) (yp :: Sing * yt) (yo :: TyPi' (Sing * ys) (FU yu yt ys yr yq yp))
$(P.return [])
type instance (@@@) (FR za yz yy yx yw) yv = FT za yz yy yx yw yv
$(P.return [])
data FV (zi :: UNKNOWN) (zh :: UNKNOWN) (zg :: UNKNOWN) (zf :: UNKNOWN) (ze :: Sing * zi) (zd :: Sing * zh) (zc :: Sing * zg) (zb :: TyPi' (Sing zg zf) (FW zi zh zg zf ze zd zc))
$(P.return [])
type instance (@@@) (FT zp zo zn zm zl zk) zj = FV zp zo zn zm zl zk zj
$(P.return [])
type instance (@@@) (FV zx zw zv zu zt zs zr) zq = 'CompGt zx zw zv zu zt zs zr zq
$(P.return [])
data FI (aac :: UNKNOWN) (aab :: UNKNOWN) (aaa :: UNKNOWN) (zz :: UNKNOWN) (zy :: TyFun' (Sing * aac) *)
$(P.return [])
data FK (aai :: UNKNOWN) (aah :: UNKNOWN) (aag :: UNKNOWN) (aaf :: UNKNOWN) (aae :: Sing * aai) (aad :: TyFun' (Sing * aah) *)
$(P.return [])
data FM (aap :: UNKNOWN) (aao :: UNKNOWN) (aan :: UNKNOWN) (aam :: UNKNOWN) (aal :: Sing * aap) (aak :: Sing * aao) (aaj :: TyFun' (Sing * aan) *)
$(P.return [])
data FO (aax :: UNKNOWN) (aaw :: UNKNOWN) (aav :: UNKNOWN) (aau :: UNKNOWN) (aat :: Sing * aax) (aas :: Sing * aaw) (aar :: Sing * aav) (aaq :: TyFun' (Sing aaw aau) *)
$(P.return [])
type instance (@@) (FO abf abe abd abc abb aba aaz) aay = CompareSpec abf abe abd 'Lt
$(P.return [])
type instance (@@) (FM abm abl abk abj abi abh) abg = TyPi (Sing abl abj) (FO abm abl abk abj abi abh abg)
$(P.return [])
type instance (@@) (FK abs abr abq abp abo) abn = TyPi (Sing * abq) (FM abs abr abq abp abo abn)
$(P.return [])
type instance (@@) (FI abx abw abv abu) abt = TyPi (Sing * abw) (FK abx abw abv abu abt)
$(P.return [])
data FH (acc :: UNKNOWN) (acb :: UNKNOWN) (aca :: UNKNOWN) (abz :: UNKNOWN) (aby :: TyPi' (Sing * acc) (FI acc acb aca abz))
$(P.return [])
data FJ (aci :: UNKNOWN) (ach :: UNKNOWN) (acg :: UNKNOWN) (acf :: UNKNOWN) (ace :: Sing * aci) (acd :: TyPi' (Sing * ach) (FK aci ach acg acf ace))
$(P.return [])
type instance (@@@) (FH acn acm acl ack) acj = FJ acn acm acl ack acj
$(P.return [])
data FL (acu :: UNKNOWN) (act :: UNKNOWN) (acs :: UNKNOWN) (acr :: UNKNOWN) (acq :: Sing * acu) (acp :: Sing * act) (aco :: TyPi' (Sing * acs) (FM acu act acs acr acq acp))
$(P.return [])
type instance (@@@) (FJ ada acz acy acx acw) acv = FL ada acz acy acx acw acv
$(P.return [])
data FN (adi :: UNKNOWN) (adh :: UNKNOWN) (adg :: UNKNOWN) (adf :: UNKNOWN) (ade :: Sing * adi) (add :: Sing * adh) (adc :: Sing * adg) (adb :: TyPi' (Sing adh adf) (FO adi adh adg adf ade add adc))
$(P.return [])
type instance (@@@) (FL adp ado adn adm adl adk) adj = FN adp ado adn adm adl adk adj
$(P.return [])
type instance (@@@) (FN adx adw adv adu adt ads adr) adq = 'CompLt adx adw adv adu adt ads adr adq
$(P.return [])
data FA (aec :: UNKNOWN) (aeb :: UNKNOWN) (aea :: UNKNOWN) (adz :: UNKNOWN) (ady :: TyFun' (Sing * aec) *)
$(P.return [])
data FC (aei :: UNKNOWN) (aeh :: UNKNOWN) (aeg :: UNKNOWN) (aef :: UNKNOWN) (aee :: Sing * aei) (aed :: TyFun' (Sing * aeh) *)
$(P.return [])
data FE (aep :: UNKNOWN) (aeo :: UNKNOWN) (aen :: UNKNOWN) (aem :: UNKNOWN) (ael :: Sing * aep) (aek :: Sing * aeo) (aej :: TyFun' (Sing * aen) *)
$(P.return [])
data FG (aex :: UNKNOWN) (aew :: UNKNOWN) (aev :: UNKNOWN) (aeu :: UNKNOWN) (aet :: Sing * aex) (aes :: Sing * aew) (aer :: Sing * aev) (aeq :: TyFun' (Sing aex aeu) *)
$(P.return [])
type instance (@@) (FG aff afe afd afc afb afa aez) aey = CompareSpec aff afe afd 'Eq
$(P.return [])
type instance (@@) (FE afm afl afk afj afi afh) afg = TyPi (Sing afm afj) (FG afm afl afk afj afi afh afg)
$(P.return [])
type instance (@@) (FC afs afr afq afp afo) afn = TyPi (Sing * afq) (FE afs afr afq afp afo afn)
$(P.return [])
type instance (@@) (FA afx afw afv afu) aft = TyPi (Sing * afw) (FC afx afw afv afu aft)
$(P.return [])
data EZ (agc :: UNKNOWN) (agb :: UNKNOWN) (aga :: UNKNOWN) (afz :: UNKNOWN) (afy :: TyPi' (Sing * agc) (FA agc agb aga afz))
$(P.return [])
data FB (agi :: UNKNOWN) (agh :: UNKNOWN) (agg :: UNKNOWN) (agf :: UNKNOWN) (age :: Sing * agi) (agd :: TyPi' (Sing * agh) (FC agi agh agg agf age))
$(P.return [])
type instance (@@@) (EZ agn agm agl agk) agj = FB agn agm agl agk agj
$(P.return [])
data FD (agu :: UNKNOWN) (agt :: UNKNOWN) (ags :: UNKNOWN) (agr :: UNKNOWN) (agq :: Sing * agu) (agp :: Sing * agt) (ago :: TyPi' (Sing * ags) (FE agu agt ags agr agq agp))
$(P.return [])
type instance (@@@) (FB aha agz agy agx agw) agv = FD aha agz agy agx agw agv
$(P.return [])
data FF (ahi :: UNKNOWN) (ahh :: UNKNOWN) (ahg :: UNKNOWN) (ahf :: UNKNOWN) (ahe :: Sing * ahi) (ahd :: Sing * ahh) (ahc :: Sing * ahg) (ahb :: TyPi' (Sing ahi ahf) (FG ahi ahh ahg ahf ahe ahd ahc))
$(P.return [])
type instance (@@@) (FD ahp aho ahn ahm ahl ahk) ahj = FF ahp aho ahn ahm ahl ahk ahj
$(P.return [])
type instance (@@@) (FF ahx ahw ahv ahu aht ahs ahr) ahq = 'CompEq ahx ahw ahv ahu aht ahs ahr ahq
$(P.return [])
data instance Sing (CompareSpec aix aiy aiz aja) aiw where
  SCompEq ::
    forall (ahy :: *) (ahz :: *) (aia :: *) (aib :: ahy) (aic :: Sing * ahy) (aid :: Sing * ahz) (aie :: Sing * aia)
    (aif :: Sing ahy aib). (Sing * ahy) -> (Sing * ahz) -> (Sing * aia) -> (Sing ahy aib) -> Sing' ('CompEq aic aid aie
    aif)
  SCompLt ::
    forall (aig :: *) (aih :: *) (aii :: *) (aij :: aih) (aik :: Sing * aig) (ail :: Sing * aih) (aim :: Sing * aii)
    (ain :: Sing aih aij). (Sing * aig) -> (Sing * aih) -> (Sing * aii) -> (Sing aih aij) -> Sing' ('CompLt aik ail aim
    ain)
  SCompGt ::
    forall (aio :: *) (aip :: *) (aiq :: *) (air :: aiq) (ais :: Sing * aio) (ait :: Sing * aip) (aiu :: Sing * aiq)
    (aiv :: Sing aiq air). (Sing * aio) -> (Sing * aip) -> (Sing * aiq) -> (Sing aiq air) -> Sing' ('CompGt ais ait aiu
    aiv)
$(P.return [])
data ES (ajb :: TyFun' * *)
$(P.return [])
data EU (ajd :: *) (ajc :: TyFun' * *)
$(P.return [])
data EW (ajg :: *) (ajf :: *) (aje :: TyFun' * *)
$(P.return [])
data EY (ajk :: *) (ajj :: *) (aji :: *) (ajh :: TyFun' Comparison *)
$(P.return [])
type instance (@@) (EY ajo ajn ajm) ajl = *
$(P.return [])
type instance (@@) (EW ajr ajq) ajp = TyPi Comparison (EY ajr ajq ajp)
$(P.return [])
type instance (@@) (EU ajt) ajs = TyPi * (EW ajt ajs)
$(P.return [])
type instance (@@) ES aju = TyPi * (EU aju)
$(P.return [])
data ER (ajv :: TyPi' * ES)
$(P.return [])
data ET (ajx :: *) (ajw :: TyPi' * (EU ajx))
$(P.return [])
type instance (@@@) ER ajy = ET ajy
$(P.return [])
data EV (akb :: *) (aka :: *) (ajz :: TyPi' * (EW akb aka))
$(P.return [])
type instance (@@@) (ET akd) akc = EV akd akc
$(P.return [])
data EX (akh :: *) (akg :: *) (akf :: *) (ake :: TyPi' Comparison (EY akh akg akf))
$(P.return [])
type instance (@@@) (EV akk akj) aki = EX akk akj aki
$(P.return [])
type instance (@@@) (EX ako akn akm) akl = CompareSpec ako akn akm akl
$(P.return [])
data instance Sing Comparison akp where
  SEq ::   Sing' 'Eq
  SLt ::   Sing' 'Lt
  SGt ::   Sing' 'Gt
$(P.return [])
data EM (aks :: UNKNOWN) (akr :: UNKNOWN) (akq :: TyFun' (Sing * aks) *)
$(P.return [])
data EO (akw :: UNKNOWN) (akv :: UNKNOWN) (aku :: Sing * akw) (akt :: TyFun' (Sing akw akv) *)
$(P.return [])
data List (ala :: *) :: * where
  Nil ::   forall (akx :: *). (Sing * akx) -> List {- KIND -} akx
  Cons ::
    forall (aky :: *) (akz :: aky). (Sing * aky) -> (Sing aky akz) -> (List {- KIND -} aky) -> List {- KIND -} aky
$(P.return [])
data EQ (alf :: UNKNOWN) (ale :: UNKNOWN) (ald :: Sing * alf) (alc :: Sing alf ale) (alb :: TyFun' (List alf) *)
$(P.return [])
type instance (@@) (EQ alk alj ali alh) alg = List alk
$(P.return [])
type instance (@@) (EO alo aln alm) all = TyPi (List alo) (EQ alo aln alm all)
$(P.return [])
type instance (@@) (EM alr alq) alp = TyPi (Sing alr alq) (EO alr alq alp)
$(P.return [])
data EL (alu :: UNKNOWN) (alt :: UNKNOWN) (als :: TyPi' (Sing * alu) (EM alu alt))
$(P.return [])
data EN (aly :: UNKNOWN) (alx :: UNKNOWN) (alw :: Sing * aly) (alv :: TyPi' (Sing aly alx) (EO aly alx alw))
$(P.return [])
type instance (@@@) (EL amb ama) alz = EN amb ama alz
$(P.return [])
data EP (amg :: UNKNOWN) (amf :: UNKNOWN) (ame :: Sing * amg) (amd :: Sing amg amf) (amc :: TyPi' (List amg) (EQ amg amf ame amd))
$(P.return [])
type instance (@@@) (EN amk amj ami) amh = EP amk amj ami amh
$(P.return [])
type instance (@@@) (EP amp amo amn amm) aml = 'Cons amp amo amn amm aml
$(P.return [])
data EK (amr :: UNKNOWN) (amq :: TyFun' (Sing * amr) *)
$(P.return [])
type instance (@@) (EK amt) ams = List amt
$(P.return [])
data EJ (amv :: UNKNOWN) (amu :: TyPi' (Sing * amv) (EK amv))
$(P.return [])
type instance (@@@) (EJ amx) amw = 'Nil amx amw
$(P.return [])
data instance Sing (List ang) anf where
  SNil ::   forall (amy :: *) (amz :: Sing * amy). (Sing * amy) -> Sing' ('Nil amz)
  SCons ::
    forall (ana :: *) (anb :: ana) (anc :: Sing * ana) (and :: Sing ana anb) (ane :: List ana). (Sing * ana) -> (Sing
    ana anb) -> (Sing (List ana) ane) -> Sing' ('Cons anc and ane)
$(P.return [])
data EI (anh :: TyFun' * *)
$(P.return [])
type instance (@@) EI ani = *
$(P.return [])
data EH (anj :: TyPi' * EI)
$(P.return [])
type instance (@@@) EH ank = List ank
$(P.return [])
data EA (anp :: UNKNOWN) (ano :: UNKNOWN) (ann :: UNKNOWN) (anm :: UNKNOWN) (anl :: TyFun' (Sing * anp) *)
$(P.return [])
data EC (anv :: UNKNOWN) (anu :: UNKNOWN) (ant :: UNKNOWN) (ans :: UNKNOWN) (anr :: Sing * anv) (anq :: TyFun' (Sing * anu) *)
$(P.return [])
data EE (aoc :: UNKNOWN) (aob :: UNKNOWN) (aoa :: UNKNOWN) (anz :: UNKNOWN) (any :: Sing * aoc) (anx :: Sing * aob) (anw :: TyFun' (Sing aoc aoa) *)
$(P.return [])
data EG (aok :: UNKNOWN) (aoj :: UNKNOWN) (aoi :: UNKNOWN) (aoh :: UNKNOWN) (aog :: Sing * aok) (aof :: Sing * aoj) (aoe :: Sing aok aoi) (aod :: TyFun' (Sing aoj aoh) *)
$(P.return [])
data Prod (aop :: *) (aoq :: *) :: * where
  Pair ::
    forall (aol :: *) (aom :: *) (aon :: aol) (aoo :: aom). (Sing * aol) -> (Sing * aom) -> (Sing aol aon) -> (Sing aom
    aoo) -> Prod {- KIND -} aol {- KIND -} aom
$(P.return [])
type instance (@@) (EG aoy aox aow aov aou aot aos) aor = Prod aoy aox
$(P.return [])
type instance (@@) (EE apf ape apd apc apb apa) aoz = TyPi (Sing ape apc) (EG apf ape apd apc apb apa aoz)
$(P.return [])
type instance (@@) (EC apl apk apj api aph) apg = TyPi (Sing apl apj) (EE apl apk apj api aph apg)
$(P.return [])
type instance (@@) (EA apq app apo apn) apm = TyPi (Sing * app) (EC apq app apo apn apm)
$(P.return [])
data DZ (apv :: UNKNOWN) (apu :: UNKNOWN) (apt :: UNKNOWN) (aps :: UNKNOWN) (apr :: TyPi' (Sing * apv) (EA apv apu apt aps))
$(P.return [])
data EB (aqb :: UNKNOWN) (aqa :: UNKNOWN) (apz :: UNKNOWN) (apy :: UNKNOWN) (apx :: Sing * aqb) (apw :: TyPi' (Sing * aqa) (EC aqb aqa apz apy apx))
$(P.return [])
type instance (@@@) (DZ aqg aqf aqe aqd) aqc = EB aqg aqf aqe aqd aqc
$(P.return [])
data ED (aqn :: UNKNOWN) (aqm :: UNKNOWN) (aql :: UNKNOWN) (aqk :: UNKNOWN) (aqj :: Sing * aqn) (aqi :: Sing * aqm) (aqh :: TyPi' (Sing aqn aql) (EE aqn aqm aql aqk aqj aqi))
$(P.return [])
type instance (@@@) (EB aqt aqs aqr aqq aqp) aqo = ED aqt aqs aqr aqq aqp aqo
$(P.return [])
data EF (arb :: UNKNOWN) (ara :: UNKNOWN) (aqz :: UNKNOWN) (aqy :: UNKNOWN) (aqx :: Sing * arb) (aqw :: Sing * ara) (aqv :: Sing arb aqz) (aqu :: TyPi' (Sing ara aqy) (EG arb ara aqz aqy aqx aqw aqv))
$(P.return [])
type instance (@@@) (ED ari arh arg arf are ard) arc = EF ari arh arg arf are ard arc
$(P.return [])
type instance (@@@) (EF arq arp aro arn arm arl ark) arj = 'Pair arq arp aro arn arm arl ark arj
$(P.return [])
data instance Sing (Prod asa asb) arz where
  SPair ::
    forall (arr :: *) (ars :: *) (art :: arr) (aru :: ars) (arv :: Sing * arr) (arw :: Sing * ars) (arx :: Sing arr
    art) (ary :: Sing ars aru). (Sing * arr) -> (Sing * ars) -> (Sing arr art) -> (Sing ars aru) -> Sing' ('Pair arv
    arw arx ary)
$(P.return [])
data DW (asc :: TyFun' * *)
$(P.return [])
data DY (ase :: *) (asd :: TyFun' * *)
$(P.return [])
type instance (@@) (DY asg) asf = *
$(P.return [])
type instance (@@) DW ash = TyPi * (DY ash)
$(P.return [])
data DV (asi :: TyPi' * DW)
$(P.return [])
data DX (ask :: *) (asj :: TyPi' * (DY ask))
$(P.return [])
type instance (@@@) DV asl = DX asl
$(P.return [])
type instance (@@@) (DX asn) asm = Prod asn asm
$(P.return [])
data DQ (asr :: UNKNOWN) (asq :: UNKNOWN) (asp :: UNKNOWN) (aso :: TyFun' (Sing * asr) *)
$(P.return [])
data DS (asw :: UNKNOWN) (asv :: UNKNOWN) (asu :: UNKNOWN) (ast :: Sing * asw) (ass :: TyFun' (Sing * asv) *)
$(P.return [])
data DU (atc :: UNKNOWN) (atb :: UNKNOWN) (ata :: UNKNOWN) (asz :: Sing * atc) (asy :: Sing * atb) (asx :: TyFun' (Sing atb ata) *)
$(P.return [])
data Sum (atj :: *) (atk :: *) :: * where
  Inl ::
    forall (atd :: *) (ate :: *) (atf :: atd). (Sing * atd) -> (Sing * ate) -> (Sing atd atf) -> Sum {- KIND -} atd
    {- KIND -} ate
  Inr ::
    forall (atg :: *) (ath :: *) (ati :: ath). (Sing * atg) -> (Sing * ath) -> (Sing ath ati) -> Sum {- KIND -} atg
    {- KIND -} ath
$(P.return [])
type instance (@@) (DU atq atp ato atn atm) atl = Sum atq atp
$(P.return [])
type instance (@@) (DS atv atu att ats) atr = TyPi (Sing atu att) (DU atv atu att ats atr)
$(P.return [])
type instance (@@) (DQ atz aty atx) atw = TyPi (Sing * aty) (DS atz aty atx atw)
$(P.return [])
data DP (aud :: UNKNOWN) (auc :: UNKNOWN) (aub :: UNKNOWN) (aua :: TyPi' (Sing * aud) (DQ aud auc aub))
$(P.return [])
data DR (aui :: UNKNOWN) (auh :: UNKNOWN) (aug :: UNKNOWN) (auf :: Sing * aui) (aue :: TyPi' (Sing * auh) (DS aui auh aug auf))
$(P.return [])
type instance (@@@) (DP aum aul auk) auj = DR aum aul auk auj
$(P.return [])
data DT (aus :: UNKNOWN) (aur :: UNKNOWN) (auq :: UNKNOWN) (aup :: Sing * aus) (auo :: Sing * aur) (aun :: TyPi' (Sing aur auq) (DU aus aur auq aup auo))
$(P.return [])
type instance (@@@) (DR aux auw auv auu) aut = DT aux auw auv auu aut
$(P.return [])
type instance (@@@) (DT avd avc avb ava auz) auy = 'Inr avd avc avb ava auz auy
$(P.return [])
data DK (avh :: UNKNOWN) (avg :: UNKNOWN) (avf :: UNKNOWN) (ave :: TyFun' (Sing * avh) *)
$(P.return [])
data DM (avm :: UNKNOWN) (avl :: UNKNOWN) (avk :: UNKNOWN) (avj :: Sing * avm) (avi :: TyFun' (Sing * avl) *)
$(P.return [])
data DO (avs :: UNKNOWN) (avr :: UNKNOWN) (avq :: UNKNOWN) (avp :: Sing * avs) (avo :: Sing * avr) (avn :: TyFun' (Sing avs avq) *)
$(P.return [])
type instance (@@) (DO avy avx avw avv avu) avt = Sum avy avx
$(P.return [])
type instance (@@) (DM awd awc awb awa) avz = TyPi (Sing awd awb) (DO awd awc awb awa avz)
$(P.return [])
type instance (@@) (DK awh awg awf) awe = TyPi (Sing * awg) (DM awh awg awf awe)
$(P.return [])
data DJ (awl :: UNKNOWN) (awk :: UNKNOWN) (awj :: UNKNOWN) (awi :: TyPi' (Sing * awl) (DK awl awk awj))
$(P.return [])
data DL (awq :: UNKNOWN) (awp :: UNKNOWN) (awo :: UNKNOWN) (awn :: Sing * awq) (awm :: TyPi' (Sing * awp) (DM awq awp awo awn))
$(P.return [])
type instance (@@@) (DJ awu awt aws) awr = DL awu awt aws awr
$(P.return [])
data DN (axa :: UNKNOWN) (awz :: UNKNOWN) (awy :: UNKNOWN) (awx :: Sing * axa) (aww :: Sing * awz) (awv :: TyPi' (Sing axa awy) (DO axa awz awy awx aww))
$(P.return [])
type instance (@@@) (DL axf axe axd axc) axb = DN axf axe axd axc axb
$(P.return [])
type instance (@@@) (DN axl axk axj axi axh) axg = 'Inl axl axk axj axi axh axg
$(P.return [])
data instance Sing (Sum axz aya) axy where
  SInl ::
    forall (axm :: *) (axn :: *) (axo :: axm) (axp :: Sing * axm) (axq :: Sing * axn) (axr :: Sing axm axo). (Sing *
    axm) -> (Sing * axn) -> (Sing axm axo) -> Sing' ('Inl axp axq axr)
  SInr ::
    forall (axs :: *) (axt :: *) (axu :: axt) (axv :: Sing * axs) (axw :: Sing * axt) (axx :: Sing axt axu). (Sing *
    axs) -> (Sing * axt) -> (Sing axt axu) -> Sing' ('Inr axv axw axx)
$(P.return [])
data DG (ayb :: TyFun' * *)
$(P.return [])
data DI (ayd :: *) (ayc :: TyFun' * *)
$(P.return [])
type instance (@@) (DI ayf) aye = *
$(P.return [])
type instance (@@) DG ayg = TyPi * (DI ayg)
$(P.return [])
data DF (ayh :: TyPi' * DG)
$(P.return [])
data DH (ayj :: *) (ayi :: TyPi' * (DI ayj))
$(P.return [])
type instance (@@@) DF ayk = DH ayk
$(P.return [])
type instance (@@@) (DH aym) ayl = Sum aym ayl
$(P.return [])
data DE (ayo :: UNKNOWN) (ayn :: TyFun' (Sing * ayo) *)
$(P.return [])
data Option (ays :: *) :: * where
  Some ::   forall (ayp :: *) (ayq :: ayp). (Sing * ayp) -> (Sing ayp ayq) -> Option {- KIND -} ayp
  None ::   forall (ayr :: *). (Sing * ayr) -> Option {- KIND -} ayr
$(P.return [])
type instance (@@) (DE ayu) ayt = Option ayu
$(P.return [])
data DD (ayw :: UNKNOWN) (ayv :: TyPi' (Sing * ayw) (DE ayw))
$(P.return [])
type instance (@@@) (DD ayy) ayx = 'None ayy ayx
$(P.return [])
data DA (azb :: UNKNOWN) (aza :: UNKNOWN) (ayz :: TyFun' (Sing * azb) *)
$(P.return [])
data DC (azf :: UNKNOWN) (aze :: UNKNOWN) (azd :: Sing * azf) (azc :: TyFun' (Sing azf aze) *)
$(P.return [])
type instance (@@) (DC azj azi azh) azg = Option azj
$(P.return [])
type instance (@@) (DA azm azl) azk = TyPi (Sing azm azl) (DC azm azl azk)
$(P.return [])
data CZ (azp :: UNKNOWN) (azo :: UNKNOWN) (azn :: TyPi' (Sing * azp) (DA azp azo))
$(P.return [])
data DB (azt :: UNKNOWN) (azs :: UNKNOWN) (azr :: Sing * azt) (azq :: TyPi' (Sing azt azs) (DC azt azs azr))
$(P.return [])
type instance (@@@) (CZ azw azv) azu = DB azw azv azu
$(P.return [])
type instance (@@@) (DB baa azz azy) azx = 'Some baa azz azy azx
$(P.return [])
data instance Sing (Option bai) bah where
  SSome ::
    forall (bab :: *) (bac :: bab) (bad :: Sing * bab) (bae :: Sing bab bac). (Sing * bab) -> (Sing bab bac) -> Sing'
    ('Some bad bae)
  SNone ::   forall (baf :: *) (bag :: Sing * baf). (Sing * baf) -> Sing' ('None bag)
$(P.return [])
data CY (baj :: TyFun' * *)
$(P.return [])
type instance (@@) CY bak = *
$(P.return [])
data CX (bal :: TyPi' * CY)
$(P.return [])
type instance (@@@) CX bam = Option bam
$(P.return [])
data CW (ban :: TyFun' Nat *)
$(P.return [])
type instance (@@) CW bao = Nat
$(P.return [])
data CV (bap :: TyPi' Nat CW)
$(P.return [])
type instance (@@@) CV baq = 'S baq
$(P.return [])
data instance Sing Nat bas where
  SO ::   Sing' 'O
  SS ::   forall (bar :: Nat). (Sing Nat bar) -> Sing' ('S bar)
$(P.return [])
data CO (baw :: UNKNOWN) (bav :: UNKNOWN) (bau :: UNKNOWN) (bat :: TyFun' (Sing * baw) *)
$(P.return [])
data CQ (bbb :: UNKNOWN) (bba :: UNKNOWN) (baz :: UNKNOWN) (bay :: Sing * bbb) (bax :: TyFun' (Sing * bba) *)
$(P.return [])
data CS (bbh :: UNKNOWN) (bbg :: UNKNOWN) (bbf :: UNKNOWN) (bbe :: Sing * bbh) (bbd :: Sing * bbg) (bbc :: TyFun' (Sing bbg bbf) *)
$(P.return [])
data Bool :: * where
  True ::   Bool
  False ::   Bool
$(P.return [])
data BoolSpec (bbo :: *) (bbp :: *) (bbq :: Bool) :: * where
  BoolSpecT ::
    forall (bbi :: *) (bbj :: *) (bbk :: bbi). (Sing * bbi) -> (Sing * bbj) -> (Sing bbi bbk) -> BoolSpec
    {- KIND -} bbi {- KIND -} bbj 'True
  BoolSpecF ::
    forall (bbl :: *) (bbm :: *) (bbn :: bbm). (Sing * bbl) -> (Sing * bbm) -> (Sing bbm bbn) -> BoolSpec
    {- KIND -} bbl {- KIND -} bbm 'False
$(P.return [])
type instance (@@) (CS bbw bbv bbu bbt bbs) bbr = BoolSpec bbw bbv 'False
$(P.return [])
type instance (@@) (CQ bcb bca bbz bby) bbx = TyPi (Sing bca bbz) (CS bcb bca bbz bby bbx)
$(P.return [])
type instance (@@) (CO bcf bce bcd) bcc = TyPi (Sing * bce) (CQ bcf bce bcd bcc)
$(P.return [])
data CN (bcj :: UNKNOWN) (bci :: UNKNOWN) (bch :: UNKNOWN) (bcg :: TyPi' (Sing * bcj) (CO bcj bci bch))
$(P.return [])
data CP (bco :: UNKNOWN) (bcn :: UNKNOWN) (bcm :: UNKNOWN) (bcl :: Sing * bco) (bck :: TyPi' (Sing * bcn) (CQ bco bcn bcm bcl))
$(P.return [])
type instance (@@@) (CN bcs bcr bcq) bcp = CP bcs bcr bcq bcp
$(P.return [])
data CR (bcy :: UNKNOWN) (bcx :: UNKNOWN) (bcw :: UNKNOWN) (bcv :: Sing * bcy) (bcu :: Sing * bcx) (bct :: TyPi' (Sing bcx bcw) (CS bcy bcx bcw bcv bcu))
$(P.return [])
type instance (@@@) (CP bdd bdc bdb bda) bcz = CR bdd bdc bdb bda bcz
$(P.return [])
type instance (@@@) (CR bdj bdi bdh bdg bdf) bde = 'BoolSpecF bdj bdi bdh bdg bdf bde
$(P.return [])
data CI (bdn :: UNKNOWN) (bdm :: UNKNOWN) (bdl :: UNKNOWN) (bdk :: TyFun' (Sing * bdn) *)
$(P.return [])
data CK (bds :: UNKNOWN) (bdr :: UNKNOWN) (bdq :: UNKNOWN) (bdp :: Sing * bds) (bdo :: TyFun' (Sing * bdr) *)
$(P.return [])
data CM (bdy :: UNKNOWN) (bdx :: UNKNOWN) (bdw :: UNKNOWN) (bdv :: Sing * bdy) (bdu :: Sing * bdx) (bdt :: TyFun' (Sing bdy bdw) *)
$(P.return [])
type instance (@@) (CM bee bed bec beb bea) bdz = BoolSpec bee bed 'True
$(P.return [])
type instance (@@) (CK bej bei beh beg) bef = TyPi (Sing bej beh) (CM bej bei beh beg bef)
$(P.return [])
type instance (@@) (CI ben bem bel) bek = TyPi (Sing * bem) (CK ben bem bel bek)
$(P.return [])
data CH (ber :: UNKNOWN) (beq :: UNKNOWN) (bep :: UNKNOWN) (beo :: TyPi' (Sing * ber) (CI ber beq bep))
$(P.return [])
data CJ (bew :: UNKNOWN) (bev :: UNKNOWN) (beu :: UNKNOWN) (bet :: Sing * bew) (bes :: TyPi' (Sing * bev) (CK bew bev beu bet))
$(P.return [])
type instance (@@@) (CH bfa bez bey) bex = CJ bfa bez bey bex
$(P.return [])
data CL (bfg :: UNKNOWN) (bff :: UNKNOWN) (bfe :: UNKNOWN) (bfd :: Sing * bfg) (bfc :: Sing * bff) (bfb :: TyPi' (Sing bfg bfe) (CM bfg bff bfe bfd bfc))
$(P.return [])
type instance (@@@) (CJ bfl bfk bfj bfi) bfh = CL bfl bfk bfj bfi bfh
$(P.return [])
type instance (@@@) (CL bfr bfq bfp bfo bfn) bfm = 'BoolSpecT bfr bfq bfp bfo bfn bfm
$(P.return [])
data instance Sing (BoolSpec bgf bgg bgh) bge where
  SBoolSpecT ::
    forall (bfs :: *) (bft :: *) (bfu :: bfs) (bfv :: Sing * bfs) (bfw :: Sing * bft) (bfx :: Sing bfs bfu). (Sing *
    bfs) -> (Sing * bft) -> (Sing bfs bfu) -> Sing' ('BoolSpecT bfv bfw bfx)
  SBoolSpecF ::
    forall (bfy :: *) (bfz :: *) (bga :: bfz) (bgb :: Sing * bfy) (bgc :: Sing * bfz) (bgd :: Sing bfz bga). (Sing *
    bfy) -> (Sing * bfz) -> (Sing bfz bga) -> Sing' ('BoolSpecF bgb bgc bgd)
$(P.return [])
data CC (bgi :: TyFun' * *)
$(P.return [])
data CE (bgk :: *) (bgj :: TyFun' * *)
$(P.return [])
data CG (bgn :: *) (bgm :: *) (bgl :: TyFun' Bool *)
$(P.return [])
type instance (@@) (CG bgq bgp) bgo = *
$(P.return [])
type instance (@@) (CE bgs) bgr = TyPi Bool (CG bgs bgr)
$(P.return [])
type instance (@@) CC bgt = TyPi * (CE bgt)
$(P.return [])
data CB (bgu :: TyPi' * CC)
$(P.return [])
data CD (bgw :: *) (bgv :: TyPi' * (CE bgw))
$(P.return [])
type instance (@@@) CB bgx = CD bgx
$(P.return [])
data CF (bha :: *) (bgz :: *) (bgy :: TyPi' Bool (CG bha bgz))
$(P.return [])
type instance (@@@) (CD bhc) bhb = CF bhc bhb
$(P.return [])
type instance (@@@) (CF bhf bhe) bhd = BoolSpec bhf bhe bhd
$(P.return [])
data Eq_true (bhg :: Bool) :: * where
  Is_eq_true ::   Eq_true 'True
$(P.return [])
data instance Sing (Eq_true bhi) bhh where
  SIs_eq_true ::   Sing' 'Is_eq_true
$(P.return [])
data CA (bhj :: TyFun' Bool *)
$(P.return [])
type instance (@@) CA bhk = *
$(P.return [])
data BZ (bhl :: TyPi' Bool CA)
$(P.return [])
type instance (@@@) BZ bhm = Eq_true bhm
$(P.return [])
data instance Sing Bool bhn where
  STrue ::   Sing' 'True
  SFalse ::   Sing' 'False
$(P.return [])
data Unit :: * where
  Tt ::   Unit
$(P.return [])
data instance Sing Unit bho where
  STt ::   Sing' 'Tt
$(P.return [])
data Empty_set :: * where
  
$(P.return [])
data instance Sing Empty_set bhp where
  
$(P.return [])
data BW (bhs :: UNKNOWN) (bhr :: UNKNOWN) (bhq :: TyFun' (Sing * bhs) *)
$(P.return [])
data BY (bhw :: UNKNOWN) (bhv :: UNKNOWN) (bhu :: Sing * bhw) (bht :: TyFun' (Sing bhw bhv) *)
$(P.return [])
data Inhabited (bhz :: *) :: * where
  Inhabits ::   forall (bhx :: *) (bhy :: bhx). (Sing * bhx) -> (Sing bhx bhy) -> Inhabited {- KIND -} bhx
$(P.return [])
type instance (@@) (BY bid bic bib) bia = Inhabited bid
$(P.return [])
type instance (@@) (BW big bif) bie = TyPi (Sing big bif) (BY big bif bie)
$(P.return [])
data BV (bij :: UNKNOWN) (bii :: UNKNOWN) (bih :: TyPi' (Sing * bij) (BW bij bii))
$(P.return [])
data BX (bin :: UNKNOWN) (bim :: UNKNOWN) (bil :: Sing * bin) (bik :: TyPi' (Sing bin bim) (BY bin bim bil))
$(P.return [])
type instance (@@@) (BV biq bip) bio = BX biq bip bio
$(P.return [])
type instance (@@@) (BX biu bit bis) bir = 'Inhabits biu bit bis bir
$(P.return [])
data instance Sing (Inhabited bja) biz where
  SInhabits ::
    forall (biv :: *) (biw :: biv) (bix :: Sing * biv) (biy :: Sing biv biw). (Sing * biv) -> (Sing biv biw) -> Sing'
    ('Inhabits bix biy)
$(P.return [])
data BU (bjb :: TyFun' * *)
$(P.return [])
type instance (@@) BU bjc = *
$(P.return [])
data BT (bjd :: TyPi' * BU)
$(P.return [])
type instance (@@@) BT bje = Inhabited bje
$(P.return [])
data BQ (bjh :: UNKNOWN) (bjg :: UNKNOWN) (bjf :: TyFun' (Sing * bjh) *)
$(P.return [])
data BS (bjl :: UNKNOWN) (bjk :: UNKNOWN) (bjj :: Sing * bjl) (bji :: TyFun' (Sing bjl bjk) *)
$(P.return [])
type instance (@@) (BS bjp bjo bjn) bjm = Eq bjp bjo bjo
$(P.return [])
type instance (@@) (BQ bjs bjr) bjq = TyPi (Sing bjs bjr) (BS bjs bjr bjq)
$(P.return [])
data BP (bjv :: UNKNOWN) (bju :: UNKNOWN) (bjt :: TyPi' (Sing * bjv) (BQ bjv bju))
$(P.return [])
data BR (bjz :: UNKNOWN) (bjy :: UNKNOWN) (bjx :: Sing * bjz) (bjw :: TyPi' (Sing bjz bjy) (BS bjz bjy bjx))
$(P.return [])
type instance (@@@) (BP bkc bkb) bka = BR bkc bkb bka
$(P.return [])
type instance (@@@) (BR bkg bkf bke) bkd = 'Eq_refl bkg bkf bke bkd
$(P.return [])
data instance Sing (Eq bkm bkn bko) bkl where
  SEq_refl ::
    forall (bkh :: *) (bki :: bkh) (bkj :: Sing * bkh) (bkk :: Sing bkh bki). (Sing * bkh) -> (Sing bkh bki) -> Sing'
    ('Eq_refl bkj bkk)
$(P.return [])
data BK (bkp :: TyFun' * *)
$(P.return [])
data BM (bkr :: *) (bkq :: TyFun' bkr *)
$(P.return [])
data BO (bku :: *) (bkt :: bku) (bks :: TyFun' bku *)
$(P.return [])
type instance (@@) (BO bkx bkw) bkv = *
$(P.return [])
type instance (@@) (BM bkz) bky = TyPi bkz (BO bkz bky)
$(P.return [])
type instance (@@) BK bla = TyPi bla (BM bla)
$(P.return [])
data BJ (blb :: TyPi' * BK)
$(P.return [])
data BL (bld :: *) (blc :: TyPi' bld (BM bld))
$(P.return [])
type instance (@@@) BJ ble = BL ble
$(P.return [])
data BN (blh :: *) (blg :: blh) (blf :: TyPi' blh (BO blh blg))
$(P.return [])
type instance (@@@) (BL blj) bli = BN blj bli
$(P.return [])
type instance (@@@) (BN blm bll) blk = Eq blm bll blk
$(P.return [])
data AY (blt :: UNKNOWN) (bls :: UNKNOWN) (blr :: UNKNOWN) (blq :: UNKNOWN) (blp :: UNKNOWN) (blo :: UNKNOWN) (bln :: TyFun' (Sing * blt) *)
$(P.return [])
data AD (blv :: *) (blu :: TyFun' blv *)
$(P.return [])
type instance (@@) (AD blx) blw = *
$(P.return [])
data BA (bmf :: UNKNOWN) (bme :: UNKNOWN) (bmd :: UNKNOWN) (bmc :: UNKNOWN) (bmb :: UNKNOWN) (bma :: UNKNOWN) (blz :: Sing * bmf) (bly :: TyFun' (Sing (TyPi bmf (AD bmf)) bme) *)
$(P.return [])
data AQ (bmi :: *) (bmh :: TyPi bmi (AD bmi)) (bmg :: TyFun' bmi *)
$(P.return [])
type instance (@@) (AQ bml bmk) bmj = *
$(P.return [])
data BC (bmu :: UNKNOWN) (bmt :: UNKNOWN) (bms :: UNKNOWN) (bmr :: UNKNOWN) (bmq :: UNKNOWN) (bmp :: UNKNOWN) (bmo :: Sing * bmu) (bmn :: Sing (TyPi bmu (AD bmu)) bmt) (bmm :: TyFun' (Sing (TyPi bmu (AQ bmu bmt)) bms) *)
$(P.return [])
data BE (bne :: UNKNOWN) (bnd :: UNKNOWN) (bnc :: UNKNOWN) (bnb :: UNKNOWN) (bna :: UNKNOWN) (bmz :: UNKNOWN) (bmy :: Sing * bne) (bmx :: Sing (TyPi bne (AD bne)) bnd) (bmw :: Sing (TyPi bne (AQ bne bnd)) bnc) (bmv :: TyFun' (Sing bne bnb) *)
$(P.return [])
data BG (bnp :: UNKNOWN) (bno :: UNKNOWN) (bnn :: UNKNOWN) (bnm :: UNKNOWN) (bnl :: UNKNOWN) (bnk :: UNKNOWN) (bnj :: Sing * bnp) (bni :: Sing (TyPi bnp (AD bnp)) bno) (bnh :: Sing (TyPi bnp (AQ bnp bno)) bnn) (bng :: Sing bnp bnm) (bnf :: TyFun' (Sing (bno @@@ bnm) bnl) *)
$(P.return [])
data BI (bob :: UNKNOWN) (boa :: UNKNOWN) (bnz :: UNKNOWN) (bny :: UNKNOWN) (bnx :: UNKNOWN) (bnw :: UNKNOWN) (bnv :: Sing * bob) (bnu :: Sing (TyPi bob (AD bob)) boa) (bnt :: Sing (TyPi bob (AQ bob boa)) bnz) (bns :: Sing bob bny) (bnr :: Sing (boa @@@ bny) bnx) (bnq :: TyFun' (Sing (bnz @@@ bny) bnw) *)
$(P.return [])
data Ex2 (boi :: *) (boj :: TyPi boi (AD boi)) (bok :: TyPi boi (AQ boi boj)) :: * where
  Ex_intro2 ::
    forall (boc :: *) (bod :: TyPi boc (AD boc)) (boe :: TyPi boc (AQ boc bod)) (bof :: boc) (bog :: bod @@@ bof) (boh
    :: boe @@@ bof). (Sing * boc) -> (Sing (TyPi boc (AD boc)) bod) -> (Sing (TyPi boc (AQ boc bod)) boe) -> (Sing boc
    bof) -> (Sing (bod @@@ bof) bog) -> (Sing (boe @@@ bof) boh) -> Ex2 {- KIND -} boc {- KIND -} bod {- KIND -} boe
$(P.return [])
type instance (@@) (BI bow bov bou bot bos bor boq bop boo bon bom) bol = Ex2 bow bov bou
$(P.return [])
type instance (@@) (BG bph bpg bpf bpe bpd bpc bpb bpa boz boy) box = TyPi (Sing (bpf @@@ bpe) bpc) (BI bph bpg bpf bpe
  bpd bpc bpb bpa boz boy box)
$(P.return [])
type instance (@@) (BE bpr bpq bpp bpo bpn bpm bpl bpk bpj) bpi = TyPi (Sing (bpq @@@ bpo) bpn) (BG bpr bpq bpp bpo bpn
  bpm bpl bpk bpj bpi)
$(P.return [])
type instance (@@) (BC bqa bpz bpy bpx bpw bpv bpu bpt) bps = TyPi (Sing bqa bpx) (BE bqa bpz bpy bpx bpw bpv bpu bpt
  bps)
$(P.return [])
type instance (@@) (BA bqi bqh bqg bqf bqe bqd bqc) bqb = TyPi (Sing (TyPi bqi (AQ bqi bqh)) bqg) (BC bqi bqh bqg bqf
  bqe bqd bqc bqb)
$(P.return [])
type instance (@@) (AY bqp bqo bqn bqm bql bqk) bqj = TyPi (Sing (TyPi bqp (AD bqp)) bqo) (BA bqp bqo bqn bqm bql bqk
  bqj)
$(P.return [])
data AX (bqw :: UNKNOWN) (bqv :: UNKNOWN) (bqu :: UNKNOWN) (bqt :: UNKNOWN) (bqs :: UNKNOWN) (bqr :: UNKNOWN) (bqq :: TyPi' (Sing * bqw) (AY bqw bqv bqu bqt bqs bqr))
$(P.return [])
data AZ (bre :: UNKNOWN) (brd :: UNKNOWN) (brc :: UNKNOWN) (brb :: UNKNOWN) (bra :: UNKNOWN) (bqz :: UNKNOWN) (bqy :: Sing * bre) (bqx :: TyPi' (Sing (TyPi bre (AD bre)) brd) (BA bre brd brc brb bra bqz bqy))
$(P.return [])
type instance (@@@) (AX brl brk brj bri brh brg) brf = AZ brl brk brj bri brh brg brf
$(P.return [])
data BB (bru :: UNKNOWN) (brt :: UNKNOWN) (brs :: UNKNOWN) (brr :: UNKNOWN) (brq :: UNKNOWN) (brp :: UNKNOWN) (bro :: Sing * bru) (brn :: Sing (TyPi bru (AD bru)) brt) (brm :: TyPi' (Sing (TyPi bru (AQ bru brt)) brs) (BC bru brt brs brr brq brp bro brn))
$(P.return [])
type instance (@@@) (AZ bsc bsb bsa brz bry brx brw) brv = BB bsc bsb bsa brz bry brx brw brv
$(P.return [])
data BD (bsm :: UNKNOWN) (bsl :: UNKNOWN) (bsk :: UNKNOWN) (bsj :: UNKNOWN) (bsi :: UNKNOWN) (bsh :: UNKNOWN) (bsg :: Sing * bsm) (bsf :: Sing (TyPi bsm (AD bsm)) bsl) (bse :: Sing (TyPi bsm (AQ bsm bsl)) bsk) (bsd :: TyPi' (Sing bsm bsj) (BE bsm bsl bsk bsj bsi bsh bsg bsf bse))
$(P.return [])
type instance (@@@) (BB bsv bsu bst bss bsr bsq bsp bso) bsn = BD bsv bsu bst bss bsr bsq bsp bso bsn
$(P.return [])
data BF (btg :: UNKNOWN) (btf :: UNKNOWN) (bte :: UNKNOWN) (btd :: UNKNOWN) (btc :: UNKNOWN) (btb :: UNKNOWN) (bta :: Sing * btg) (bsz :: Sing (TyPi btg (AD btg)) btf) (bsy :: Sing (TyPi btg (AQ btg btf)) bte) (bsx :: Sing btg btd) (bsw :: TyPi' (Sing (btf @@@ btd) btc) (BG btg btf bte btd btc btb bta bsz bsy bsx))
$(P.return [])
type instance (@@@) (BD btq btp bto btn btm btl btk btj bti) bth = BF btq btp bto btn btm btl btk btj bti bth
$(P.return [])
data BH (buc :: UNKNOWN) (bub :: UNKNOWN) (bua :: UNKNOWN) (btz :: UNKNOWN) (bty :: UNKNOWN) (btx :: UNKNOWN) (btw :: Sing * buc) (btv :: Sing (TyPi buc (AD buc)) bub) (btu :: Sing (TyPi buc (AQ buc bub)) bua) (btt :: Sing buc btz) (bts :: Sing (bub @@@ btz) bty) (btr :: TyPi' (Sing (bua @@@ btz) btx) (BI buc bub bua btz bty btx btw btv btu btt bts))
$(P.return [])
type instance (@@@) (BF bun bum bul buk buj bui buh bug buf bue) bud = BH bun bum bul buk buj bui buh bug buf bue bud
$(P.return [])
type instance (@@@) (BH buz buy bux buw buv buu but bus bur buq bup) buo = 'Ex_intro2 buz buy bux buw buv buu but bus
  bur buq bup buo
$(P.return [])
data instance Sing (Ex2 bvn bvo bvp) bvm where
  SEx_intro2 ::
    forall (bva :: *) (bvb :: TyPi bva (AD bva)) (bvc :: TyPi bva (AQ bva bvb)) (bvd :: bva) (bve :: bvb @@@ bvd) (bvf
    :: bvc @@@ bvd) (bvg :: Sing * bva) (bvh :: Sing (TyPi bva (AD bva)) bvb) (bvi :: Sing (TyPi bva (AQ bva bvb)) bvc)
    (bvj :: Sing bva bvd) (bvk :: Sing (bvb @@@ bvd) bve) (bvl :: Sing (bvc @@@ bvd) bvf). (Sing * bva) -> (Sing (TyPi
    bva (AD bva)) bvb) -> (Sing (TyPi bva (AQ bva bvb)) bvc) -> (Sing bva bvd) -> (Sing (bvb @@@ bvd) bve) -> (Sing
    (bvc @@@ bvd) bvf) -> Sing' ('Ex_intro2 bvg bvh bvi bvj bvk bvl)
$(P.return [])
data AS (bvq :: TyFun' * *)
$(P.return [])
data AU (bvs :: *) (bvr :: TyFun' (TyPi bvs (AD bvs)) *)
$(P.return [])
data AW (bvv :: *) (bvu :: TyPi bvv (AD bvv)) (bvt :: TyFun' (TyPi bvv (AQ bvv bvu)) *)
$(P.return [])
type instance (@@) (AW bvy bvx) bvw = *
$(P.return [])
type instance (@@) (AU bwa) bvz = TyPi (TyPi bwa (AQ bwa bvz)) (AW bwa bvz)
$(P.return [])
type instance (@@) AS bwb = TyPi (TyPi bwb (AD bwb)) (AU bwb)
$(P.return [])
data AR (bwc :: TyPi' * AS)
$(P.return [])
data AT (bwe :: *) (bwd :: TyPi' (TyPi bwe (AD bwe)) (AU bwe))
$(P.return [])
type instance (@@@) AR bwf = AT bwf
$(P.return [])
data AV (bwi :: *) (bwh :: TyPi bwi (AD bwi)) (bwg :: TyPi' (TyPi bwi (AQ bwi bwh)) (AW bwi bwh))
$(P.return [])
type instance (@@@) (AT bwk) bwj = AV bwk bwj
$(P.return [])
type instance (@@@) (AV bwn bwm) bwl = Ex2 bwn bwm bwl
$(P.return [])
data AJ (bws :: UNKNOWN) (bwr :: UNKNOWN) (bwq :: UNKNOWN) (bwp :: UNKNOWN) (bwo :: TyFun' (Sing * bws) *)
$(P.return [])
data AL (bwy :: UNKNOWN) (bwx :: UNKNOWN) (bww :: UNKNOWN) (bwv :: UNKNOWN) (bwu :: Sing * bwy) (bwt :: TyFun' (Sing (TyPi bwy (AD bwy)) bwx) *)
$(P.return [])
data AN (bxf :: UNKNOWN) (bxe :: UNKNOWN) (bxd :: UNKNOWN) (bxc :: UNKNOWN) (bxb :: Sing * bxf) (bxa :: Sing (TyPi bxf (AD bxf)) bxe) (bwz :: TyFun' (Sing bxf bxd) *)
$(P.return [])
data AP (bxn :: UNKNOWN) (bxm :: UNKNOWN) (bxl :: UNKNOWN) (bxk :: UNKNOWN) (bxj :: Sing * bxn) (bxi :: Sing (TyPi bxn (AD bxn)) bxm) (bxh :: Sing bxn bxl) (bxg :: TyFun' (Sing (bxm @@@ bxl) bxk) *)
$(P.return [])
data Ex (bxs :: *) (bxt :: TyPi bxs (AD bxs)) :: * where
  Ex_intro ::
    forall (bxo :: *) (bxp :: TyPi bxo (AD bxo)) (bxq :: bxo) (bxr :: bxp @@@ bxq). (Sing * bxo) -> (Sing (TyPi bxo (AD
    bxo)) bxp) -> (Sing bxo bxq) -> (Sing (bxp @@@ bxq) bxr) -> Ex {- KIND -} bxo {- KIND -} bxp
$(P.return [])
type instance (@@) (AP byb bya bxz bxy bxx bxw bxv) bxu = Ex byb bya
$(P.return [])
type instance (@@) (AN byi byh byg byf bye byd) byc = TyPi (Sing (byh @@@ byg) byf) (AP byi byh byg byf bye byd byc)
$(P.return [])
type instance (@@) (AL byo byn bym byl byk) byj = TyPi (Sing byo bym) (AN byo byn bym byl byk byj)
$(P.return [])
type instance (@@) (AJ byt bys byr byq) byp = TyPi (Sing (TyPi byt (AD byt)) bys) (AL byt bys byr byq byp)
$(P.return [])
data AI (byy :: UNKNOWN) (byx :: UNKNOWN) (byw :: UNKNOWN) (byv :: UNKNOWN) (byu :: TyPi' (Sing * byy) (AJ byy byx byw byv))
$(P.return [])
data AK (bze :: UNKNOWN) (bzd :: UNKNOWN) (bzc :: UNKNOWN) (bzb :: UNKNOWN) (bza :: Sing * bze) (byz :: TyPi' (Sing (TyPi bze (AD bze)) bzd) (AL bze bzd bzc bzb bza))
$(P.return [])
type instance (@@@) (AI bzj bzi bzh bzg) bzf = AK bzj bzi bzh bzg bzf
$(P.return [])
data AM (bzq :: UNKNOWN) (bzp :: UNKNOWN) (bzo :: UNKNOWN) (bzn :: UNKNOWN) (bzm :: Sing * bzq) (bzl :: Sing (TyPi bzq (AD bzq)) bzp) (bzk :: TyPi' (Sing bzq bzo) (AN bzq bzp bzo bzn bzm bzl))
$(P.return [])
type instance (@@@) (AK bzw bzv bzu bzt bzs) bzr = AM bzw bzv bzu bzt bzs bzr
$(P.return [])
data AO (cae :: UNKNOWN) (cad :: UNKNOWN) (cac :: UNKNOWN) (cab :: UNKNOWN) (caa :: Sing * cae) (bzz :: Sing (TyPi cae (AD cae)) cad) (bzy :: Sing cae cac) (bzx :: TyPi' (Sing (cad @@@ cac) cab) (AP cae cad cac cab caa bzz bzy))
$(P.return [])
type instance (@@@) (AM cal cak caj cai cah cag) caf = AO cal cak caj cai cah cag caf
$(P.return [])
type instance (@@@) (AO cat cas car caq cap cao can) cam = 'Ex_intro cat cas car caq cap cao can cam
$(P.return [])
data instance Sing (Ex cbd cbe) cbc where
  SEx_intro ::
    forall (cau :: *) (cav :: TyPi cau (AD cau)) (caw :: cau) (cax :: cav @@@ caw) (cay :: Sing * cau) (caz :: Sing
    (TyPi cau (AD cau)) cav) (cba :: Sing cau caw) (cbb :: Sing (cav @@@ caw) cax). (Sing * cau) -> (Sing (TyPi cau (AD
    cau)) cav) -> (Sing cau caw) -> (Sing (cav @@@ caw) cax) -> Sing' ('Ex_intro cay caz cba cbb)
$(P.return [])
data AF (cbf :: TyFun' * *)
$(P.return [])
data AH (cbh :: *) (cbg :: TyFun' (TyPi cbh (AD cbh)) *)
$(P.return [])
type instance (@@) (AH cbj) cbi = *
$(P.return [])
type instance (@@) AF cbk = TyPi (TyPi cbk (AD cbk)) (AH cbk)
$(P.return [])
data AE (cbl :: TyPi' * AF)
$(P.return [])
data AG (cbn :: *) (cbm :: TyPi' (TyPi cbn (AD cbn)) (AH cbn))
$(P.return [])
type instance (@@@) AE cbo = AG cbo
$(P.return [])
type instance (@@@) (AG cbq) cbp = Ex cbq cbp
$(P.return [])
data Y (cbu :: UNKNOWN) (cbt :: UNKNOWN) (cbs :: UNKNOWN) (cbr :: TyFun' (Sing * cbu) *)
$(P.return [])
data AA (cbz :: UNKNOWN) (cby :: UNKNOWN) (cbx :: UNKNOWN) (cbw :: Sing * cbz) (cbv :: TyFun' (Sing * cby) *)
$(P.return [])
data AC (ccf :: UNKNOWN) (cce :: UNKNOWN) (ccd :: UNKNOWN) (ccc :: Sing * ccf) (ccb :: Sing * cce) (cca :: TyFun' (Sing cce ccd) *)
$(P.return [])
data Or (ccm :: *) (ccn :: *) :: * where
  Or_introl ::
    forall (ccg :: *) (cch :: *) (cci :: ccg). (Sing * ccg) -> (Sing * cch) -> (Sing ccg cci) -> Or {- KIND -} ccg
    {- KIND -} cch
  Or_intror ::
    forall (ccj :: *) (cck :: *) (ccl :: cck). (Sing * ccj) -> (Sing * cck) -> (Sing cck ccl) -> Or {- KIND -} ccj
    {- KIND -} cck
$(P.return [])
type instance (@@) (AC cct ccs ccr ccq ccp) cco = Or cct ccs
$(P.return [])
type instance (@@) (AA ccy ccx ccw ccv) ccu = TyPi (Sing ccx ccw) (AC ccy ccx ccw ccv ccu)
$(P.return [])
type instance (@@) (Y cdc cdb cda) ccz = TyPi (Sing * cdb) (AA cdc cdb cda ccz)
$(P.return [])
data X (cdg :: UNKNOWN) (cdf :: UNKNOWN) (cde :: UNKNOWN) (cdd :: TyPi' (Sing * cdg) (Y cdg cdf cde))
$(P.return [])
data Z (cdl :: UNKNOWN) (cdk :: UNKNOWN) (cdj :: UNKNOWN) (cdi :: Sing * cdl) (cdh :: TyPi' (Sing * cdk) (AA cdl cdk cdj cdi))
$(P.return [])
type instance (@@@) (X cdp cdo cdn) cdm = Z cdp cdo cdn cdm
$(P.return [])
data AB (cdv :: UNKNOWN) (cdu :: UNKNOWN) (cdt :: UNKNOWN) (cds :: Sing * cdv) (cdr :: Sing * cdu) (cdq :: TyPi' (Sing cdu cdt) (AC cdv cdu cdt cds cdr))
$(P.return [])
type instance (@@@) (Z cea cdz cdy cdx) cdw = AB cea cdz cdy cdx cdw
$(P.return [])
type instance (@@@) (AB ceg cef cee ced cec) ceb = 'Or_intror ceg cef cee ced cec ceb
$(P.return [])
data S (cek :: UNKNOWN) (cej :: UNKNOWN) (cei :: UNKNOWN) (ceh :: TyFun' (Sing * cek) *)
$(P.return [])
data U (cep :: UNKNOWN) (ceo :: UNKNOWN) (cen :: UNKNOWN) (cem :: Sing * cep) (cel :: TyFun' (Sing * ceo) *)
$(P.return [])
data W (cev :: UNKNOWN) (ceu :: UNKNOWN) (cet :: UNKNOWN) (ces :: Sing * cev) (cer :: Sing * ceu) (ceq :: TyFun' (Sing cev cet) *)
$(P.return [])
type instance (@@) (W cfb cfa cez cey cex) cew = Or cfb cfa
$(P.return [])
type instance (@@) (U cfg cff cfe cfd) cfc = TyPi (Sing cfg cfe) (W cfg cff cfe cfd cfc)
$(P.return [])
type instance (@@) (S cfk cfj cfi) cfh = TyPi (Sing * cfj) (U cfk cfj cfi cfh)
$(P.return [])
data R (cfo :: UNKNOWN) (cfn :: UNKNOWN) (cfm :: UNKNOWN) (cfl :: TyPi' (Sing * cfo) (S cfo cfn cfm))
$(P.return [])
data T (cft :: UNKNOWN) (cfs :: UNKNOWN) (cfr :: UNKNOWN) (cfq :: Sing * cft) (cfp :: TyPi' (Sing * cfs) (U cft cfs cfr cfq))
$(P.return [])
type instance (@@@) (R cfx cfw cfv) cfu = T cfx cfw cfv cfu
$(P.return [])
data V (cgd :: UNKNOWN) (cgc :: UNKNOWN) (cgb :: UNKNOWN) (cga :: Sing * cgd) (cfz :: Sing * cgc) (cfy :: TyPi' (Sing cgd cgb) (W cgd cgc cgb cga cfz))
$(P.return [])
type instance (@@@) (T cgi cgh cgg cgf) cge = V cgi cgh cgg cgf cge
$(P.return [])
type instance (@@@) (V cgo cgn cgm cgl cgk) cgj = 'Or_introl cgo cgn cgm cgl cgk cgj
$(P.return [])
data instance Sing (Or chc chd) chb where
  SOr_introl ::
    forall (cgp :: *) (cgq :: *) (cgr :: cgp) (cgs :: Sing * cgp) (cgt :: Sing * cgq) (cgu :: Sing cgp cgr). (Sing *
    cgp) -> (Sing * cgq) -> (Sing cgp cgr) -> Sing' ('Or_introl cgs cgt cgu)
  SOr_intror ::
    forall (cgv :: *) (cgw :: *) (cgx :: cgw) (cgy :: Sing * cgv) (cgz :: Sing * cgw) (cha :: Sing cgw cgx). (Sing *
    cgv) -> (Sing * cgw) -> (Sing cgw cgx) -> Sing' ('Or_intror cgy cgz cha)
$(P.return [])
data O (che :: TyFun' * *)
$(P.return [])
data Q (chg :: *) (chf :: TyFun' * *)
$(P.return [])
type instance (@@) (Q chi) chh = *
$(P.return [])
type instance (@@) O chj = TyPi * (Q chj)
$(P.return [])
data N (chk :: TyPi' * O)
$(P.return [])
data P (chm :: *) (chl :: TyPi' * (Q chm))
$(P.return [])
type instance (@@@) N chn = P chn
$(P.return [])
type instance (@@@) (P chp) cho = Or chp cho
$(P.return [])
data F (chu :: UNKNOWN) (cht :: UNKNOWN) (chs :: UNKNOWN) (chr :: UNKNOWN) (chq :: TyFun' (Sing * chu) *)
$(P.return [])
data H (cia :: UNKNOWN) (chz :: UNKNOWN) (chy :: UNKNOWN) (chx :: UNKNOWN) (chw :: Sing * cia) (chv :: TyFun' (Sing * chz) *)
$(P.return [])
data K (cih :: UNKNOWN) (cig :: UNKNOWN) (cif :: UNKNOWN) (cie :: UNKNOWN) (cid :: Sing * cih) (cic :: Sing * cig) (cib :: TyFun' (Sing cih cif) *)
$(P.return [])
data M (cip :: UNKNOWN) (cio :: UNKNOWN) (cin :: UNKNOWN) (cim :: UNKNOWN) (cil :: Sing * cip) (cik :: Sing * cio) (cij :: Sing cip cin) (cii :: TyFun' (Sing cio cim) *)
$(P.return [])
data And (ciu :: *) (civ :: *) :: * where
  Conj ::
    forall (ciq :: *) (cir :: *) (cis :: ciq) (cit :: cir). (Sing * ciq) -> (Sing * cir) -> (Sing ciq cis) -> (Sing cir
    cit) -> And {- KIND -} ciq {- KIND -} cir
$(P.return [])
type instance (@@) (M cjd cjc cjb cja ciz ciy cix) ciw = And cjd cjc
$(P.return [])
type instance (@@) (K cjk cjj cji cjh cjg cjf) cje = TyPi (Sing cjj cjh) (M cjk cjj cji cjh cjg cjf cje)
$(P.return [])
type instance (@@) (H cjq cjp cjo cjn cjm) cjl = TyPi (Sing cjq cjo) (K cjq cjp cjo cjn cjm cjl)
$(P.return [])
type instance (@@) (F cjv cju cjt cjs) cjr = TyPi (Sing * cju) (H cjv cju cjt cjs cjr)
$(P.return [])
data E (cka :: UNKNOWN) (cjz :: UNKNOWN) (cjy :: UNKNOWN) (cjx :: UNKNOWN) (cjw :: TyPi' (Sing * cka) (F cka cjz cjy cjx))
$(P.return [])
data G (ckg :: UNKNOWN) (ckf :: UNKNOWN) (cke :: UNKNOWN) (ckd :: UNKNOWN) (ckc :: Sing * ckg) (ckb :: TyPi' (Sing * ckf) (H ckg ckf cke ckd ckc))
$(P.return [])
type instance (@@@) (E ckl ckk ckj cki) ckh = G ckl ckk ckj cki ckh
$(P.return [])
data J (cks :: UNKNOWN) (ckr :: UNKNOWN) (ckq :: UNKNOWN) (ckp :: UNKNOWN) (cko :: Sing * cks) (ckn :: Sing * ckr) (ckm :: TyPi' (Sing cks ckq) (K cks ckr ckq ckp cko ckn))
$(P.return [])
type instance (@@@) (G cky ckx ckw ckv cku) ckt = J cky ckx ckw ckv cku ckt
$(P.return [])
data L (clg :: UNKNOWN) (clf :: UNKNOWN) (cle :: UNKNOWN) (cld :: UNKNOWN) (clc :: Sing * clg) (clb :: Sing * clf) (cla :: Sing clg cle) (ckz :: TyPi' (Sing clf cld) (M clg clf cle cld clc clb cla))
$(P.return [])
type instance (@@@) (J cln clm cll clk clj cli) clh = L cln clm cll clk clj cli clh
$(P.return [])
type instance (@@@) (L clv clu clt cls clr clq clp) clo = 'Conj clv clu clt cls clr clq clp clo
$(P.return [])
data instance Sing (And cmf cmg) cme where
  SConj ::
    forall (clw :: *) (clx :: *) (cly :: clw) (clz :: clx) (cma :: Sing * clw) (cmb :: Sing * clx) (cmc :: Sing clw
    cly) (cmd :: Sing clx clz). (Sing * clw) -> (Sing * clx) -> (Sing clw cly) -> (Sing clx clz) -> Sing' ('Conj cma
    cmb cmc cmd)
$(P.return [])
data B (cmh :: TyFun' * *)
$(P.return [])
data D (cmj :: *) (cmi :: TyFun' * *)
$(P.return [])
type instance (@@) (D cml) cmk = *
$(P.return [])
type instance (@@) B cmm = TyPi * (D cmm)
$(P.return [])
data A (cmn :: TyPi' * B)
$(P.return [])
data C (cmp :: *) (cmo :: TyPi' * (D cmp))
$(P.return [])
type instance (@@@) A cmq = C cmq
$(P.return [])
type instance (@@@) (C cms) cmr = And cms cmr
$(P.return [])
data instance Sing False cmt where
  
$(P.return [])
data True :: * where
  I ::   True
$(P.return [])
data instance Sing True cmu where
  SI ::   Sing' 'I
