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
data T (c :: Nat) :: * where
  F1 ::   forall (a :: Nat). Sing Nat a -> T ('S a)
  FS ::   forall (b :: Nat). Sing Nat b -> T b -> T ('S b)
$(P.return [])
data Eq (f :: *) (g :: f) (h :: f) :: * where
  Eq_refl ::   forall (d :: *) (e :: d). Sing * d -> Sing d e -> Eq d e e
$(P.return [])
data instance Sing (Eq l m n) k where
  SEq_refl ::   forall (i :: *) (j :: i). Sing * i -> Sing i j -> Sing' ('Eq_refl (ToSing i) (ToSing j))
$(P.return [])
data Y (r :: Nat) (q :: T r) (p :: T r) (o :: TyFun' (Eq (T ('S r)) ('FS (ToSing r) q) ('FS (ToSing r) p)) *)
$(P.return [])
type instance (@@) (Y v u t) s = Eq (T v) u t
$(P.return [])
data AY (z :: Nat) (y :: T z) (x :: T z) (w :: TyPi' (Eq (T ('S z)) ('FS (ToSing z) y) ('FS (ToSing z) x)) (Y z y x))
$(P.return [])
data Z (ac :: Nat) (ab :: T ac) (aa :: TyFun' (T ac) *)
$(P.return [])
type instance (@@) (Z af ae) ad = TyPi (Eq (T ('S af)) ('FS (ToSing af) ae) ('FS (ToSing af) ad)) (Y af ae ad)
$(P.return [])
data AZ (ai :: Nat) (ah :: T ai) (ag :: TyPi' (T ai) (Z ai ah))
$(P.return [])
data AA (ak :: Nat) (aj :: TyFun' (T ak) *)
$(P.return [])
type instance (@@) (AA am) al = TyPi (T am) (Z am al)
$(P.return [])
data BA (ao :: Nat) (an :: TyPi' (T ao) (AA ao))
$(P.return [])
data BC (ap :: TyFun' Nat *)
$(P.return [])
type instance (@@) BC aq = TyPi (T aq) (AA aq)
$(P.return [])
data BB (ar :: TyPi' Nat BC)
$(P.return [])
fS_inj :: Sing' BB
fS_inj = let { as :: Sing' BB; as = SLambda (\(au :: Sing Nat at) -> let { av :: Sing' (BA at); av = SLambda (\(ax ::
  Sing (T at) aw) -> let { ay :: Sing' (AZ at aw); ay = SLambda (\(ba :: Sing (T at) az) -> let { bb :: Sing' (AY at aw
  az); bb = SLambda (\(bd :: Sing (Eq (T ('S at)) ('FS (ToSing at) aw) ('FS (ToSing at) az)) bc) -> case bd of {
  SEq_refl bf be -> SEq_refl P.undefined ax `unSLambda` be `unSLambda` bf })} in bb)} in ay)} in av)} in as

$(P.return [])
type instance (@@@) BB bg = BA bg
$(P.return [])
type instance (@@@) (BA bi) bh = AZ bi bh
$(P.return [])
type instance (@@@) (AZ bl bk) bj = AY bl bk bj
$(P.return [])
data AW (bq :: Nat) (bp :: T bq) (bo :: T bq) (bn :: Eq (T ('S bq)) ('FS (ToSing bq) bp) ('FS (ToSing bq) bo)) (bm :: TyFun' (T ('S bq)) *)
$(P.return [])
data AB (bw :: Nat) (bv :: T bw) (bu :: T bw) (bt :: Eq (T ('S bw)) ('FS (ToSing bw) bv) ('FS (ToSing bw) bu)) (bs :: T ('S bw)) (br :: TyFun' (Eq (T ('S bw)) ('FS (ToSing bw) bv) bs) *)
$(P.return [])
type instance (@@) (AB cc cb ca bz by) bx = *
$(P.return [])
type instance (@@) (AW ch cg cf ce) cd = TyPi (Eq (T ('S ch)) ('FS (ToSing ch) cg) cd) (AB ch cg cf ce cd)
$(P.return [])
data AV (cm :: Nat) (cl :: T cm) (ck :: T cm) (cj :: Eq (T ('S cm)) ('FS (ToSing cm) cl) ('FS (ToSing cm) ck)) (ci :: TyPi' (T ('S cm)) (AW cm cl ck cj))
$(P.return [])
data AU (cs :: Nat) (cr :: T cs) (cq :: T cs) (cp :: Eq (T ('S cs)) ('FS (ToSing cs) cr) ('FS (ToSing cs) cq)) (co :: T ('S cs)) (cn :: TyPi' (Eq (T ('S cs)) ('FS (ToSing cs) cr) co) (AB cs cr cq cp co))
$(P.return [])
type instance (@@@) (AV cx cw cv cu) ct = AU cx cw cv cu ct
$(P.return [])
type family AX (di :: Nat) (dh :: T di) (dg :: T di) (df :: Eq (T ('S di)) ('FS (ToSing di) dh) ('FS (ToSing di) dg)) (de :: Eq (T ('S di)) ('FS (ToSing di) dh) ('FS (ToSing di) dg))  :: AV di dh dg df @@@ de where
   AX da db dc dd ('Eq_refl cy cz) = 'Eq_refl (ToSing (T dd)) (ToSing dc) @@@ cy @@@ cz
$(P.return [])
type instance (@@@) (AY dm dl dk) dj = AX dm dl dk dj dj
$(P.return [])
data AK (du :: Nat) (dt :: T du) (ds :: T du) (dr :: Eq (T ('S du)) ('FS (ToSing du) dt) ('FS (ToSing du) ds)) (dq :: T ('S du)) (dp :: Eq (T ('S du)) ('FS (ToSing du) dt) dq) (dn :: TyFun' Nat *)
$(P.return [])
data AC (ec :: Nat) (eb :: T ec) (ea :: T ec) (dz :: Eq (T ('S ec)) ('FS (ToSing ec) eb) ('FS (ToSing ec) ea)) (dy :: T ('S ec)) (dx :: Eq (T ('S ec)) ('FS (ToSing ec) eb) dy) (dw :: Nat) (dv :: TyFun' (T dw) *)
$(P.return [])
type instance (@@) (AC ek ej ei eh eg ef ee) ed = *
$(P.return [])
type instance (@@) (AK er eq ep eo en em) el = TyPi (T el) (AC er eq ep eo en em el)
$(P.return [])
data AJ (ey :: Nat) (ex :: T ey) (ew :: T ey) (ev :: Eq (T ('S ey)) ('FS (ToSing ey) ex) ('FS (ToSing ey) ew)) (eu :: T ('S ey)) (et :: Eq (T ('S ey)) ('FS (ToSing ey) ex) eu) (es :: TyPi' Nat (AK ey ex ew ev eu et))
$(P.return [])
data AM (ff :: Nat) (fe :: T ff) (fd :: T ff) (fc :: Eq (T ('S ff)) ('FS (ToSing ff) fe) ('FS (ToSing ff) fd)) (fb :: T ('S ff)) (fa :: Eq (T ('S ff)) ('FS (ToSing ff) fe) fb) (ez :: TyPi' Nat (AK ff fe fd fc fb fa))
$(P.return [])
data AS (fm :: Nat) (fl :: T fm) (fk :: T fm) (fj :: Eq (T ('S fm)) ('FS (ToSing fm) fl) ('FS (ToSing fm) fk)) (fi :: T ('S fm)) (fh :: Eq (T ('S fm)) ('FS (ToSing fm) fl) fi) (fg :: TyFun' Nat *)
$(P.return [])
data AO (fu :: Nat) (ft :: T fu) (fs :: T fu) (fr :: Eq (T ('S fu)) ('FS (ToSing fu) ft) ('FS (ToSing fu) fs)) (fq :: T ('S fu)) (fp :: Eq (T ('S fu)) ('FS (ToSing fu) ft) fq) (fo :: Nat) (fn :: TyFun' (T fo) *)
$(P.return [])
data AN (gd :: Nat) (gc :: T gd) (gb :: T gd) (ga :: Eq (T ('S gd)) ('FS (ToSing gd) gc) ('FS (ToSing gd) gb)) (fz :: T ('S gd)) (fy :: Eq (T ('S gd)) ('FS (ToSing gd) gc) fz) (fx :: Nat) (fw :: T fx) (fv :: TyFun' (T fx) *)
$(P.return [])
type instance (@@) (AN gm gl gk gj gi gh gg gf) ge = *
$(P.return [])
type instance (@@) (AO gu gt gs gr gq gp go) gn = TyPi (T go) (AN gu gt gs gr gq gp go gn)
$(P.return [])
type instance (@@) (AS hb ha gz gy gx gw) gv = TyPi (T gv) (AO hb ha gz gy gx gw gv)
$(P.return [])
data AR (hi :: Nat) (hh :: T hi) (hg :: T hi) (hf :: Eq (T ('S hi)) ('FS (ToSing hi) hh) ('FS (ToSing hi) hg)) (he :: T ('S hi)) (hd :: Eq (T ('S hi)) ('FS (ToSing hi) hh) he) (hc :: TyPi' Nat (AS hi hh hg hf he hd))
$(P.return [])
data AI (hq :: Nat) (hp :: T hq) (ho :: T hq) (hn :: Eq (T ('S hq)) ('FS (ToSing hq) hp) ('FS (ToSing hq) ho)) (hm :: T ('S hq)) (hl :: Eq (T ('S hq)) ('FS (ToSing hq) hp) hm) (hk :: Nat) (hj :: TyPi' (T hk) (AC hq hp ho hn hm hl hk))
$(P.return [])
type instance (@@@) (AJ hx hw hv hu ht hs) hr = AI hx hw hv hu ht hs hr
$(P.return [])
data AL (ig :: Nat) (ie :: T ig) (id :: T ig) (ic :: Eq (T ('S ig)) ('FS (ToSing ig) ie) ('FS (ToSing ig) id)) (ib :: T ('S ig)) (ia :: Eq (T ('S ig)) ('FS (ToSing ig) ie) ib) (hz :: Nat) (hy :: TyPi' (T hz) (AC ig ie id ic ib ia hz))
$(P.return [])
type instance (@@@) (AM io im il ik ij ii) ih = AL io im il ik ij ii ih
$(P.return [])
data AQ (iw :: Nat) (iv :: T iw) (iu :: T iw) (it :: Eq (T ('S iw)) ('FS (ToSing iw) iv) ('FS (ToSing iw) iu)) (is :: T ('S iw)) (ir :: Eq (T ('S iw)) ('FS (ToSing iw) iv) is) (iq :: Nat) (ip :: TyPi' (T iq) (AO iw iv iu it is ir iq))
$(P.return [])
type instance (@@@) (AR jd jc jb ja iz iy) ix = AQ jd jc jb ja iz iy ix
$(P.return [])
type family AT (jz :: Nat) (jy :: T jz) (jx :: T jz) (jw :: Eq (T ('S jz)) ('FS (ToSing jz) jy) ('FS (ToSing jz) jx)) (jv :: T ('S jz)) (ju :: Eq (T ('S jz)) ('FS (ToSing jz) jy) jv) (jt :: T ('S jz))  :: AJ jz jy jx jw jv ju @@@ jt where
   AT jf jg jh ji jj jk ('F1 je) = AM jk jj ji jh jg jf @@@ je
   AT jn jo jp jq jr js ('FS jl jm) = AR js jr jq jp jo jn @@@ jl @@@ jm
$(P.return [])
type instance (@@@) (AU kf ke kd kc kb) ka = AT kf ke kd kc kb ka kb @@@ ke
$(P.return [])
data AP (ko :: Nat) (kn :: T ko) (km :: T ko) (kl :: Eq (T ('S ko)) ('FS (ToSing ko) kn) ('FS (ToSing ko) km)) (kk :: T ('S ko)) (kj :: Eq (T ('S ko)) ('FS (ToSing ko) kn) kk) (ki :: Nat) (kh :: T ki) (kg :: TyPi' (T ki) (AN ko kn km kl kk kj ki kh))
$(P.return [])
type instance (@@@) (AQ kw kv ku kt ks kr kq) kp = AP kw kv ku kt ks kr kq kp
$(P.return [])
type instance (@@@) (AP lf le ld lc lb la kz ky) kx = Eq (T kz) kx ky
$(P.return [])
data True :: * where
  I ::   forall. True
$(P.return [])
type instance (@@@) (AL ln lm ll lk lj li lh) lg = True
$(P.return [])
data AE (lw :: Nat) (lv :: T lw) (lu :: T lw) (lt :: Eq (T ('S lw)) ('FS (ToSing lw) lv) ('FS (ToSing lw) lu)) (ls :: T ('S lw)) (lr :: Eq (T ('S lw)) ('FS (ToSing lw) lv) ls) (lq :: Nat) (lp :: T lq) (lo :: TyFun' Nat *)
$(P.return [])
type instance (@@) (AE mf me md mc mb ma lz ly) lx = *
$(P.return [])
data AD (mo :: Nat) (mn :: T mo) (mm :: T mo) (ml :: Eq (T ('S mo)) ('FS (ToSing mo) mn) ('FS (ToSing mo) mm)) (mk :: T ('S mo)) (mj :: Eq (T ('S mo)) ('FS (ToSing mo) mn) mk) (mi :: Nat) (mh :: T mi) (mg :: TyPi' Nat (AE mo mn mm ml mk mj mi mh))
$(P.return [])
data AG (mx :: Nat) (mw :: T mx) (mv :: T mx) (mu :: Eq (T ('S mx)) ('FS (ToSing mx) mw) ('FS (ToSing mx) mv)) (mt :: T ('S mx)) (ms :: Eq (T ('S mx)) ('FS (ToSing mx) mw) mt) (mr :: Nat) (mq :: T mr) (mp :: TyPi' Nat (AE mx mw mv mu mt ms mr mq))
$(P.return [])
type instance (@@@) (AD ng nf ne nd nc nb na mz) my = *
$(P.return [])
data AF (nq :: Nat) (np :: T nq) (no :: T nq) (nn :: Eq (T ('S nq)) ('FS (ToSing nq) np) ('FS (ToSing nq) no)) (nm :: T ('S nq)) (nl :: Eq (T ('S nq)) ('FS (ToSing nq) np) nm) (nk :: Nat) (nj :: T nk) (ni :: Nat) (nh :: TyFun' (T ni) *)
$(P.return [])
type instance (@@) (AF oa nz ny nx nw nv nu nt ns) nr = *
$(P.return [])
type instance (@@@) (AG ok oj oi oh og oe od oc) ob = TyPi (T ob) (AF ok oj oi oh og oe od oc ob)
$(P.return [])
type family AH (pk :: Nat) (pj :: T pk) (pi :: T pk) (ph :: Eq (T ('S pk)) ('FS (ToSing pk) pj) ('FS (ToSing pk) pi)) (pg :: T ('S pk)) (pf :: Eq (T ('S pk)) ('FS (ToSing pk) pj) pg) (pe :: Nat) (pd :: T pe) (pc :: Nat)  :: AD pk pj pi ph pg pf pe pd @@@ pc where
   AH ol om on oo op oq or os 'O = *
   AH ou ov ow ox oy oz pa pb ('S ot) = AG pb pa oz oy ox ow ov ou @@@ ot
$(P.return [])
type instance (@@@) (AI ps pr pq pp po pn pm) pl = AH ps pr pq pp po pn pm pl pm
$(P.return [])
data False :: * where
  
$(P.return [])
data instance Sing False pt where
  
$(P.return [])
data instance Sing True pu where
  SI ::   forall. Sing' 'I
$(P.return [])
data U (px :: *) (pw :: px) (pv :: TyFun' (Sing * px) *)
$(P.return [])
data W (qb :: *) (qa :: qb) (pz :: Sing * qb) (py :: TyFun' (Sing qb qa) *)
$(P.return [])
type instance (@@) (W qf qe qd) qc = Eq qf qe qe
$(P.return [])
type instance (@@) (U qi qh) qg = TyPi (Sing qi qh) (W qi qh qg)
$(P.return [])
data R (ql :: *) (qk :: ql) (qj :: TyPi' (Sing * ql) (U ql qk))
$(P.return [])
data V (qp :: *) (qo :: qp) (qn :: Sing * qp) (qm :: TyPi' (Sing qp qo) (W qp qo qn))
$(P.return [])
type instance (@@@) (R qs qr) qq = V qs qr qq
$(P.return [])
type instance (@@@) (V qw qv qu) qt = 'Eq_refl qu qt
$(P.return [])
data L (qx :: TyFun' * *)
$(P.return [])
data N (qz :: *) (qy :: TyFun' qz *)
$(P.return [])
data Q (rc :: *) (rb :: rc) (ra :: TyFun' rc *)
$(P.return [])
type instance (@@) (Q rf re) rd = *
$(P.return [])
type instance (@@) (N rh) rg = TyPi rh (Q rh rg)
$(P.return [])
type instance (@@) L ri = TyPi ri (N ri)
$(P.return [])
data K (rj :: TyPi' * L)
$(P.return [])
data M (rl :: *) (rk :: TyPi' rl (N rl))
$(P.return [])
type instance (@@@) K rm = M rm
$(P.return [])
data P (rp :: *) (ro :: rp) (rn :: TyPi' rp (Q rp ro))
$(P.return [])
type instance (@@@) (M rr) rq = P rr rq
$(P.return [])
type instance (@@@) (P ru rt) rs = Eq ru rt rs
$(P.return [])
data H (rw :: Nat) (rv :: TyFun' (Sing Nat rw) *)
$(P.return [])
data J (rz :: Nat) (ry :: Sing Nat rz) (rx :: TyFun' (T rz) *)
$(P.return [])
type instance (@@) (J sc sb) sa = T ('S sc)
$(P.return [])
type instance (@@) (H se) sd = TyPi (T se) (J se sd)
$(P.return [])
data G (sg :: Nat) (sf :: TyPi' (Sing Nat sg) (H sg))
$(P.return [])
data I (sj :: Nat) (si :: Sing Nat sj) (sh :: TyPi' (T sj) (J sj si))
$(P.return [])
type instance (@@@) (G sl) sk = I sl sk
$(P.return [])
type instance (@@@) (I so sn) sm = 'FS sn sm
$(P.return [])
data F (sq :: Nat) (sp :: TyFun' (Sing Nat sq) *)
$(P.return [])
type instance (@@) (F ss) sr = T ('S ss)
$(P.return [])
data E (su :: Nat) (st :: TyPi' (Sing Nat su) (F su))
$(P.return [])
type instance (@@@) (E sw) sv = 'F1 sv
$(P.return [])
data instance Sing (T tb) ta where
  SF1 ::   forall (sx :: Nat). Sing Nat sx -> Sing' ('F1 (ToSing sx))
  SFS ::   forall (sy :: Nat) (sz :: T sy). Sing Nat sy -> Sing (T sy) sz -> Sing' ('FS (ToSing sy) sz)
$(P.return [])
data D (tc :: TyFun' Nat *)
$(P.return [])
type instance (@@) D td = *
$(P.return [])
data C (te :: TyPi' Nat D)
$(P.return [])
type instance (@@@) C tf = T tf
$(P.return [])
data B (tg :: TyFun' Nat *)
$(P.return [])
type instance (@@) B th = Nat
$(P.return [])
data A (ti :: TyPi' Nat B)
$(P.return [])
type instance (@@@) A tj = 'S tj
$(P.return [])
data instance Sing Nat tl where
  SO ::   forall. Sing' 'O
  SS ::   forall (tk :: Nat). Sing Nat tk -> Sing' ('S tk)
