module Extraction where

import Prelude

import Data.Maybe
import Data.Nat
import Data.Type.Equality

import Telescope
import qualified Coq as C
import qualified HS as H

import Data.Map (Map)
import qualified Data.Map as M
import qualified Data.Set as S

import Data.Bitraversable

import Control.Monad.Writer
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except

import Control.Lens hiding (scribe)

import Debug.Trace

--------------------------------------------------------------------------------

newtype ExtractM n a = ExtractM { unExtractM ::
                                      ExceptT ()
                                      (WriterT ( H.Definitions (H.AName n)
                                               , Map (n, Int) ([Int], Types n Z)
                                               , Map (n, Int, Int) (Types n Z)
                                               )
                                       (ReaderT ( Map (n, Int) ([Int], Types n Z)
                                                , Map (n, Int, Int) (Types n Z)
                                                )
                                        (State ()))) a }
                     deriving ( Functor, Applicative, Monad
                              , MonadError ()
                              , MonadWriter ( H.Definitions (H.AName n)
                                            , Map (n, Int) ([Int], Types n Z)
                                            , Map (n, Int, Int) (Types n Z)
                                            )
                              , MonadReader ( Map (n, Int) ([Int], Types n Z)
                                            , Map (n, Int, Int) (Types n Z)
                                            )
                              )

scribe :: (MonadWriter s m, Monoid s) => ASetter s s a a -> a -> m ()
scribe l b = tell (set l b mempty)
{-# INLINE scribe #-}

extendCtxBy :: Vec b (H.Type n a) -> H.Env n a -> H.Env n (Plus b a)
extendCtxBy VNil         c = c
extendCtxBy (VCons a as) c = case plusSRight (snOfVec as) (H.snOfEnv c) of
  Refl -> extendCtxBy (fmap (H.mapType id FS) as) (H.EnvCons a c)

type Types n a = (H.Type (H.AName n) a, H.Type (H.AName n) a)

mkPi :: (Show n, Ord n) => H.Env (H.AName n) a -> H.Type (H.AName n) a -> H.Type (H.AName n) (S a) -> ExtractM n (H.Type (H.AName n) a)
mkPi c a' b' = do
  let sn = H.snOfEnv c
  case ( H.dEnv c (H.appC H.Pair (H.cType sn a') (H.liftC (H.cType (SS sn) b')))
       ) of
    ( H.D s1 (H.Pair c1 (H.Pair a1 (H.L b1)))) -> do
      let nPi  = H.AName (H.NPi c1 a1 b1)
      pure ( H.TPi a' (foldr (\v t -> H.TCApp t (H.TVar v)) (H.TConst nPi) (H.snList s1))
           )

mkLam :: (Show n, Ord n) => H.Env (H.AName n) a -> H.Type (H.AName n) a -> Types n (S a) -> ExtractM n (Types n a)
mkLam c a' (bTy, b') = do
  let sn = H.snOfEnv c
  case ( H.dEnv c (H.appC H.Pair (H.cType sn a') (H.liftC (H.cType (SS sn) bTy)))
       , H.dEnv c (H.appC H.Pair (H.cType sn a') (H.liftC (H.cType (SS sn) b')))
       ) of
    ( H.D s1 (H.Pair c1 (H.Pair a1 (H.L b1))), H.D s2 (H.Pair c2 (H.Pair a2 (H.L b2)))) -> do
      let nPi  = H.AName (H.NPi c1 a1 b1)
          nLam = H.AName (H.NLam c2 a2 nPi b2)
      pure ( H.TPi a' (foldr (\v t -> H.TCApp t (H.TVar v)) (H.TConst nPi) (H.snList s1))
           , foldr (\v t -> H.TCApp t (H.TVar v)) (H.TConst nLam) (H.snList s2)
           )

extractTerm :: (Show n, Ord n) => H.Env (H.AName n) a -> C.Expr n a -> ExtractM n (H.Type (H.AName n) a, H.Type (H.AName n) a)
extractTerm c (C.EVar x)   = pure (H.envLookup x c, H.TVar x)
extractTerm c (C.EConst x) = pure (error "CONST")
extractTerm c (C.EInd x i) = view _1 <&> M.lookup (x, i)
                             <&> fromJust
                             <&> snd
                             <&> bimap H.TLift H.TLift
extractTerm c (C.ECons x i j) = view _2 <&> M.lookup (x, i, j-1)
                                <&> fromJust
                                <&> bimap H.TLift H.TLift
extractTerm c C.EType      = pure (H.TType, H.TType)
extractTerm c (C.EApp a b d) = do
  (aTy, a') <- extractTerm c a
  (bTy, b') <- extractTerm c b
  (dTy, d') <- extractTerm c d
  pure (d', H.TApp a' b')
extractTerm c (C.EPi a b) = do
  (aTy, a') <- extractTerm c a
  (bTy, b') <- extractTerm (H.EnvCons a' c) b
  (H.TType,) <$> mkPi c a' b'
extractTerm c (C.EAbs a b) = do
  (aTy, a') <- extractTerm c a
  (bTy, b') <- extractTerm (H.EnvCons a' c) b
  mkLam c a' (bTy, b')
extractTerm c (C.EFix a b) = do
  aTys <- forM a $ fmap snd . extractTerm c . fst
  let c' = extendCtxBy aTys c
  bTys <- forM a $ fmap snd . extractTerm c' . snd
  let sn = H.snOfEnv c
      sn' = H.snOfEnv c'
      sa = snOfVec a
  case H.dEnv c (H.cVec (H.snOfEnv c) (H.appC H.Pair
                                       <$> (fmap (H.cType sn) aTys)
                                       <*> (fmap (H.liftBC sn sa . H.cType sn') bTys))) of
    (H.D s (H.Pair c (H.Compose d))) -> do
      let nFix1 = H.AName . H.NFix1 c (fmap (\(H.Pair a (H.LB b)) -> (a, b)) d)
          nFix2 = H.AName . H.NFix2 c (fmap (\(H.Pair a (H.LB b)) -> (a, b)) d)
          nFix  = H.AName (H.NFix c ((\n (H.Pair a (H.LB b)) -> (nFix1 n, nFix2 n, a, b)) <$> allFins sa <*> d) b)
      pure ( fromJust (aTys ^? ix b)
           , foldr (\v t -> H.TCApp t (H.TVar v)) (H.TConst nFix) (H.snList s)
           )
extractTerm c (C.ECase cons scrut retType appRetType branchs) = do
  let sn = H.snOfEnv c
  ars <- ExtractM (lift $ lift $ view _1 <&> M.lookup cons)
         <&> fromJust
         <&> fst
  let ars = [0,1] -- ...
  branchs' <- zipWith3
               (\ar i e -> do
                   case esnOfInt ar of
                     ESN m ->
                       let snm = plus m sn in
                         H.Case (H.AName (H.NICons (fst cons) (snd cons) i)) m
                         (foldl H.TApp (H.mapType id (liftFinBy m) e) (H.TVar <$> takeVec sn m (allFins snm)))
               ) ars [0..] <$> mapM (fmap snd . extractTerm c) branchs
  (scrutTy, scrut') <- extractTerm c scrut
  (retTypeTy, retType') <- extractTerm c retType
  (appRetTypeTy, appRetType') <- extractTerm c appRetType
  case H.dEnv c (H.appC H.Pair (H.appC H.Pair (H.cType sn scrutTy) (H.cType sn retType')) (H.cList sn (fmap (H.cCase sn) branchs'))) of
       (H.D s1 (H.Pair c1 (H.Pair (H.Pair bTy1 d1) (H.Compose e1)))) -> do
         let nCase = H.AName (H.NCase c1 bTy1 (H.mapType id FS d1 `H.TApp` H.TVar FZ) e1)
         pure ( appRetType'
              , H.TCApp (foldr (\v t -> H.TCApp t (H.TVar v)) (H.TConst nCase) (H.snList s1)) scrut'
              )

extractSignature :: (Show n, Ord n) => H.Env (H.AName n) a -> Signature (C.Expr n) a -> ExtractM n (Signature (H.Type (H.AName n)) a)
extractSignature c (TEmpty a)  = TEmpty . view _2 <$> extractTerm c a
extractSignature c (TNext a b) = do
  (_, aTy) <- extractTerm c a
  TNext aTy <$> extractSignature (H.EnvCons aTy c) b

extractApplication :: (Show n, Ord n) => H.Env (H.AName n) a -> Application (C.Expr n) a -> ExtractM n (Application (H.Type (H.AName n)) a)
extractApplication c (Application a b) = Application <$> (fmap (view _2) (extractTerm c a)) <*> mapM (fmap (view _2) . extractTerm c) b

extractConstructor :: (Show n, Ord n) => H.Env (H.AName n) a -> Constructor (C.Expr n) a -> ExtractM n (Constructor (H.Type (H.AName n)) a)
extractConstructor c (TEmpty a)  = TEmpty <$> extractApplication c a
extractConstructor c (TNext a b) = do
  (_, aTy) <- extractTerm c a
  TNext aTy <$> extractConstructor (H.EnvCons aTy c) b

mkTelescopeLam :: (Show n, Ord n) => H.Env (H.AName n) a -> (forall b. H.Env (H.AName n) b -> g b -> ExtractM n (Types n b)) ->
                  Telescope (H.Type (H.AName n)) g a -> ExtractM n (Types n a)
mkTelescopeLam c f (TEmpty a)  = f c a
mkTelescopeLam c f (TNext a b) = do
  (bTy, b') <- mkTelescopeLam (H.EnvCons a c) f b
  mkLam c a (bTy, b')

extractDefinition :: (Show n, Ord n) => C.Definition n -> ExtractM n ()
extractDefinition (C.ConstantDefinition n a) = do
  (aTy', aTy) <- extractTerm H.EnvNil a
  scribe _1 . pure $ H.ConstDef (H.AName (H.NConst n)) aTy
extractDefinition (C.InductiveDefinition n m ar cons) = do
  s <- extractSignature H.EnvNil ar
  let si = H.AName (H.NInd n m)
  s' <- mkTelescopeLam H.EnvNil (\e _ -> pure (H.TType, foldl H.TCApp (H.TConst si) (fmap H.TVar (allFins (H.snOfEnv e))))) s
  scribe _2 (M.singleton (n, m) (telescopeLength . snd <$> cons, s'))
  cs <- forM (zip [0..] cons) $ \(i, (a, b)) -> do
    let ci = H.AName (H.NICons n m i)
        csi = H.AName (H.NISCons n m i)
    c <- extractConstructor H.EnvNil b
    c' <- mkTelescopeLam H.EnvNil (\e (Application d ds) -> pure ( foldl H.TCApp d ds
                                                                 , foldl H.TPApp (H.TConst ci) (fmap H.TVar (allFins (H.snOfEnv e)))
                                                                 )) c
    scribe _3 (M.singleton (n, m, i) c')
    pure ((ci, csi), c)
  scribe _1 [H.IndDef si s cs]

extract :: (Show n, Ord n) => [C.Definition n] -> Either () (H.Definitions (H.AName n))
extract ds = do
  let ((x, (m, r1, r2)), _) = mapM extractDefinition ds
                              & unExtractM
                              & runExceptT
                              & runWriterT
                              & (runReaderT ?? (r1, r2))
                              & (runState ?? ())
  const m <$> x
