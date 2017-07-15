{-# LANGUAGE OverloadedStrings #-}
module Emit where

import qualified HS as H

import Telescope

import Language.Haskell.Exts.Simple.Syntax

import Data.Nat
import Data.String
import Data.Maybe
import Data.Foldable
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

import Data.Bitraversable
import Control.Lens
import Control.Monad.Reader

import Debug.Trace

--------------------------------------------------------------------------------

instance IsString ModuleName where
  fromString = ModuleName
instance IsString Name where
  fromString = Ident
instance IsString QName where
  fromString = UnQual . Ident
instance IsString Type where
  fromString = TyVar . Ident
instance IsString TyVarBind where
  fromString = UnkindedVar . Ident
instance IsString DeclHead where
  fromString = DHead . Ident

infixr 8 ==>
(==>) :: Type -> Type  -> Type
(==>) = TyFun

infixl 9 $$, @@, @@@
($$) :: Type -> Type -> Type
($$) = TyApp

(@@) :: Type -> Type -> Type
(@@) a b = TyInfix a (UnQual (Symbol "@@")) b

(@@@) :: Type -> Type -> Type
(@@@) a b = TyInfix a (UnQual (Symbol "@@@")) b

star :: Type
star = TyCon (Qual "K" "Type")

tyFun :: Type -> Type
tyFun a = "TyFun" $$ a ==> star

tyPi :: Type -> Type -> Type
tyPi a b = "TyPi" $$ a $$ b ==> star

proxy :: Kind -> Type
proxy p = TyKind "'P" ("P" $$ p)

smallVariables :: [String]
smallVariables = [1..] >>= flip replicateM ['a'..'z']

extendCtx :: Reader ([String], Vec (S a) String) x -> Reader ([String], Vec a String) (String, x)
extendCtx m = (,) <$> (head <$> view _1) <*> withReader (\(x:xs, v) -> (xs, VCons x v)) m

extendCtx' :: SN n -> Reader ([String], Vec n String) x -> Reader ([String], Vec Z String) (Vec n String, x)
extendCtx' SZ     m = (VNil,) <$> m
extendCtx' (SS n) m = do
  (a, (b, c)) <- extendCtx' n (extendCtx m)
  pure (VCons b a, c)

extendCtx'' :: SN n -> Reader ([String], Vec (Plus n m) String) x -> Reader ([String], Vec m String) (Vec n String, x)
extendCtx'' SZ     m = (VNil,) <$> m
extendCtx'' (SS n) m = do
  (a, (b, c)) <- extendCtx'' n (extendCtx m)
  pure (VCons b a, c)

runEmit = flip runReader (smallVariables, VNil)

emit :: [(String, H.Name String String)] -> H.Definitions String -> Module
emit nm ds = Module (Just (ModuleHead "OUT" Nothing Nothing))
             [LanguagePragma ["TypeInType", "RankNTypes", "TypeFamilies", "TypeOperators", "GADTs", "UndecidableInstances"]]
             [ ImportDecl "Prelude" False False False Nothing Nothing (Just (ImportSpecList False []))
             , ImportDecl "Data.Kind" True False False Nothing (Just "K") Nothing
             ]
             ([ DataFamDecl Nothing ("Sing" `DHApp` (KindedVar "k" star)) (Just (KindSig ("k" ==> star)))
              , TypeDecl ("Sing'" `DHApp` (KindedVar "x" "k")) ("Sing" $$ "k" $$ "x")
              , DataDecl DataType Nothing ("P" `DHApp` (KindedVar "x" "k")) [QualConDecl Nothing Nothing (ConDecl "P" [])] Nothing
              , GDataDecl DataType Nothing "TyFun" (Just (star ==> star)) [] Nothing
              , TypeFamDecl (DHead (Symbol "@@") `DHApp` (KindedVar "f" (tyFun "a")) `DHApp` (KindedVar "x" "a")) (Just (KindSig star)) Nothing
              , GDataDecl DataType Nothing ("TyPi" `DHApp` (KindedVar "a" star)) (Just (tyFun "a" ==> star)) [] Nothing
              , TypeFamDecl (DHead (Symbol "@@@") `DHApp` (KindedVar "f" (tyPi "a" "b")) `DHApp` (KindedVar "x" "a")) (Just (KindSig ("b" @@ "x"))) Nothing
              , GDataInsDecl DataType ("Sing" $$ (tyPi "a" "b") $$ "x") Nothing
--  SLambda :: (forall t . Sing k1 t -> Sing (k2 @@ t) (f @@@ t)) -> Sing (TyPi k1 k2 -> K.Type) f
                [GadtDecl "SLambda" Nothing
                 (TyForall (Just ["t"]) Nothing
                  ("Sing" $$ "k1" $$ "t" ==> "Sing" $$ ("k2" @@ "t") $$ ("f" @@@ "t")) ==> "Sing" $$ (tyPi "k1" "k2") $$ "f")
                ] Nothing
              ] ++ (ds >>= emitDefinition) ++ (nm >>= uncurry emitName)
             )

emitName :: String -> H.Name String String -> [Decl]
emitName n (H.NPi sn t v)     = emitPi n (H.vecOfEnv sn) t v
emitName n (H.NLam sn t p v)  = emitLambda n (H.vecOfEnv sn) t p v
emitName n (H.NFix sn a b)    = emitFix n (H.vecOfEnv sn) a b
emitName n (H.NFix1 _ _ _)    = []
emitName n (H.NFix2 _ _ _)    = []
emitName n (H.NCase sn a b c) = emitCase n (H.vecOfEnv sn) a b c
emitName n (H.NConst _)       = []
emitName n (H.NInd _ _)       = []
emitName n (H.NICons _ _ _)   = []
emitName n (H.NISCons _ _ _)  = []

emitCase :: String -> Vec n (H.Type String n) -> H.Type String n -> H.Type String (S n) -> [H.Case String n] -> [Decl]
emitCase n ctx a b c =
  let (vs, r) = runEmit $ extendCtx' (snOfVec ctx) $ do
        ctx' <- mapM emitType ctx
        let cBndrs = reverse $ toList ((\x a -> KindedVar (fromString x) a) <$> vs <*> ctx')
        let appVs vs a = foldl ($$) a (fmap fromString vs)
        a      <- emitType a
        (x, b) <- extendCtx (emitType b)
        c' <- forM c $ \case
          H.Case x y z -> do
            (as, b) <- extendCtx'' y (emitType z)
            pure $ TypeEqn (foldl ($$) (fromString n) (fromString <$> reverseVec vs) $$ foldl ($$) (fromString x) (proxy . fromString <$> as)) b
        pure [ ClosedTypeFamDecl
               (foldl DHApp (fromString n) (cBndrs ++ [KindedVar (fromString x) a]))
               (Just (KindSig b))
               Nothing
               c'
             ]
  in trace ("emitCase\n" ++ show r) r

emitPi :: String -> Vec n (H.Type String n) -> H.Type String n -> H.Type String (S n) -> [Decl]
emitPi n ctx t s =
  let (vs, r) = runEmit $ extendCtx' (snOfVec ctx) $ do
        c' <- mapM emitType ctx
        a <- emitType t
        (x, b) <- extendCtx (emitType s)
        pure [ GDataDecl DataType Nothing
               (foldl DHApp (fromString n) (toList $ (\x a -> KindedVar (fromString x) a) <$> vs <*> c'))
               (Just (tyFun a)) [] Nothing
             , TypeInsDecl
               (foldl ($$) (fromString n) (fromString <$> vs) @@ fromString x)
               b
             ]
  in trace ("emitPi\n" ++ show (n,ctx,t,s) ++ "\n" ++ show r) r

emitLambda :: String -> Vec n (H.Type String n) -> H.Type String n -> String -> H.Type String (S n) -> [Decl]
emitLambda n ctx t p s =
  let (vs, r) = runEmit $ extendCtx' (snOfVec ctx) $ do
        c' <- mapM emitType ctx
        a <- emitType t
        (x, b) <- extendCtx (emitType s)
        pure $ traceShow ("XXXXXXXXXXXXXXXXXXXXXXXXX",vs,x)
          [ GDataDecl DataType Nothing
               (foldl DHApp (fromString n) (reverse $ toList $ (\x a -> KindedVar (fromString x) a) <$> vs <*>  c'))
               (Just (tyPi a (foldl ($$) (fromString p) [{- TODO: check this -}]))) [] Nothing
             , TypeInsDecl
               (foldl ($$) (fromString n) (fromString <$> reverseVec vs) @@@ fromString x)
               b
             ]
  in trace ("emitLam\n" ++ show r) r

emitFix :: String -> Vec n (H.Type String n) -> Vec m (String, String, H.Type String n, H.Type String (Plus m n)) -> Fin m -> [Decl]
emitFix n ctx v b =
  let (vs, r) = runEmit $ extendCtx' (snOfVec ctx) $ do
        c' <- mapM emitType ctx
        let cBndrs = toList ((\x a -> KindedVar (fromString x) a) <$> vs <*> c')
        let appVs vs a = foldl ($$) a (fmap fromString vs)
        ts <- forM v (emitType . view _3)
        rs <- iforM v $ \i (a, b, _, d) -> do
          (vs2, dTy) <- extendCtx'' (snOfVec v) (emitType d)
          pure [ ClosedTypeFamDecl (foldl DHApp (fromString a) cBndrs)
                 (Just (KindSig (lookupVec ts i)))
                 Nothing
                 [ TypeEqn (appVs vs (fromString a))
                   (foldl ($$) (appVs vs (fromString b)) (fmap (appVs vs . fromString . view _1) v))
                 ]
               , ClosedTypeFamDecl (foldl DHApp (fromString b) (cBndrs ++ toList ((\x a -> KindedVar (fromString x) a) <$> vs2 <*> ts)))
                 (Just (KindSig (lookupVec ts i)))
                 Nothing
                 [ TypeEqn (appVs vs2 (appVs vs (fromString b))) dTy
                 ]
               ]
        pure ( TypeDecl (foldl DHApp (fromString n) cBndrs) (foldl ($$) (fromString (lookupVec v b ^. _1)) (fmap fromString vs))
               : concat rs)
  in r

emitDefinition :: H.Definition String -> [Decl]
emitDefinition (H.ConstDef n t) =
  [TypeDecl (fromString n) (runEmit (emitType t))]
emitDefinition (H.IndDef n s c) =
  let (tvs, k) = runEmit (emitSignature s)
      (c1, c2) = unzip (fmap (uncurry (emitConstructor n')) c)
      n'       = n ++ "'"
  in
  [ TypeFamDecl  (fromString n) (Just (KindSig (foldl (==>) k (snd <$> tvs)))) Nothing
  , TypeInsDecl  (fromString n) (fromString n')
  , GDataDecl    DataType Nothing (foldl DHApp (fromString n') (fmap (uncurry KindedVar) tvs)) (Just k) c1 Nothing
  , GDataInsDecl DataType ("Sing" $$ (foldl (\a (x, _) -> a $$ TyVar x) (fromString n') tvs) $$ "b_") (Just star) c2 Nothing
  ]

emitConstructor :: String -> (String, String) -> Constructor (H.Type String) Z -> (GadtDecl, GadtDecl)
emitConstructor m (n, sn) c =
  let (vs, k) = runEmit (emitConstructor' c)
  in ( GadtDecl (fromString n) Nothing
       (TyForall (Just (fmap (uncurry KindedVar) vs)) Nothing
        (foldr (\(x, _) t -> "P" $$ TyVar x ==> t) k vs))
     , GadtDecl (fromString sn) Nothing
       (TyForall (Just (fmap (uncurry KindedVar) vs)) Nothing
        (foldr (\(x, _) t -> "Sing'" $$ TyVar x ==> t) ("Sing'" $$ (foldl (\a (x, _) -> a $$ (TyKind "'P" ("P" $$ TyVar x))) (fromString n) vs)) vs))
     )
  where emitConstructor' :: Constructor (H.Type String) a -> Reader ([String], Vec a String) ([(Name, Type)], Type)
        emitConstructor' (TEmpty (Application a as)) = do
          -- a'  <- emitType a
          let a' = fromString m
          as' <- mapM emitType as
          pure ([], foldl ($$) a' as')
        emitConstructor' (TNext a b) = do
          a' <- emitType a
          (x, b') <- extendCtx (emitConstructor' b)
          pure (b' & _1 %~ ((fromString x, a'):))

emitSignature :: Signature (H.Type String) a -> Reader ([String], Vec a String) ([(Name, Type)], Type)
emitSignature (TEmpty a)  = ([],) <$> emitType a
emitSignature (TNext a b) = do
  a' <- emitType a
  (x, b') <- extendCtx (emitSignature b)
  pure (b' & _1 %~ ((fromString x, a'):))

emitType :: H.Type String a -> Reader ([String], Vec a String) Type
emitType (H.TVar a)    = fromString <$> view (_2.ix a)
emitType (H.TConst a)  = pure (fromString a)
emitType (H.TPi a b)   = tyPi <$> emitType a <*> emitType b
emitType (H.TPApp a b) = ($$) <$> emitType a <*> (proxy <$> emitType b)
emitType (H.TCApp a b) = ($$) <$> emitType a <*> emitType b
emitType (H.TApp a b)  = (@@@) <$> emitType a <*> emitType b
emitType H.TType       = pure star
emitType (H.TLift a)   = emitType (H.mapType id undefined a)
emitType H.TUNKNOWN    = pure "UNKNOWN"
