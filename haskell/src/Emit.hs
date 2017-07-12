{-# LANGUAGE OverloadedStrings #-}
module Emit where

import qualified HS as H

import Telescope

import Language.Haskell.Exts.Syntax
import Language.Haskell.Exts.SrcLoc

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

infixr 8 ==>
(==>) :: Kind -> Kind  -> Kind
(==>) = TyFun

infixl 9 $$, @@, @@@
($$) :: Kind -> Kind -> Kind
($$) = TyApp

(@@) :: Kind -> Kind -> Kind
(@@) a b = TyInfix a (UnQual (Symbol "@@")) b

(@@@) :: Kind -> Kind -> Kind
(@@@) a b = TyInfix a (UnQual (Symbol "@@@")) b

star :: Kind
star = TyCon (Qual "K" "Type")

tyFun :: Kind -> Kind
tyFun a = "TyFun" $$ a ==> star

tyPi :: Kind -> Kind -> Kind
tyPi a b = "TyPi" $$ a $$ b ==> star

proxy :: Kind -> Kind
proxy p = TyKind "P" ("P" $$ p)

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
emit nm ds = Module noLoc "OUT"
             [LanguagePragma noLoc ["TypeInType", "RankNTypes", "TypeFamilies", "TypeOperators", "GADTs", "UndecidableInstances"]]
             Nothing Nothing
             [ ImportDecl noLoc "Prelude" False False False Nothing Nothing (Just (False, []))
             , ImportDecl noLoc "Data.Kind" True False False Nothing (Just "K") Nothing
             ]
             ([ DataFamDecl noLoc [] "Sing" [KindedVar "k" star] (Just ("k" ==> star))
              , TypeDecl noLoc "Sing'" [KindedVar "x" "k"] ("Sing" $$ "k" $$ "x")
              , DataDecl noLoc DataType [] "P" [KindedVar "x" "k"] [QualConDecl noLoc [] [] (ConDecl "P" [])] []
              , GDataDecl noLoc DataType [] "TyFun" [] (Just (star ==> star)) [] []
              , TypeFamDecl noLoc (Symbol "@@") [KindedVar "f" (tyFun "a"), KindedVar "x" "a"] (Just star)
              , GDataDecl noLoc DataType [] "TyPi" [KindedVar "a" star] (Just (tyFun "a" ==> star)) [] []
              , TypeFamDecl noLoc (Symbol "@@@") [KindedVar "f" (tyPi "a" "b"), KindedVar "x" "a"] (Just ("b" @@ "x"))
              , GDataInsDecl noLoc DataType ("Sing" $$ (tyPi "a" "b") $$ "x") Nothing
                [GadtDecl noLoc "SLambda" []
                 (TyForall (Just ["t"]) []
                  ("Sing" $$ "k1" $$ "t" ==> "Sing" $$ ("k2" @@ "t") $$ ("f" @@@ "t")) ==> "Sing" $$ (tyPi "k1" "k2") $$ "f")
                ] []
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
        let cBndrs = toList ((\x a -> KindedVar (fromString x) a) <$> vs <*> ctx')
        let appVs vs a = foldl ($$) a (fmap fromString vs)
        a      <- emitType a
        (x, b) <- extendCtx (emitType b)
        c' <- forM c $ \case
          H.Case x y z -> do
            (as, b) <- extendCtx'' y (emitType z)
            pure $ TypeEqn (foldl ($$) (fromString n) (fromString <$> vs) $$ foldl ($$) (fromString x) (proxy . fromString <$> as)) b
        pure [ ClosedTypeFamDecl noLoc (fromString n)
               (cBndrs ++ [KindedVar (fromString x) a])
               (Just b)
               c'
             ]
  in r

emitPi :: String -> Vec n (H.Type String n) -> H.Type String n -> H.Type String (S n) -> [Decl]
emitPi n ctx t s =
  let (vs, r) = runEmit $ extendCtx' (snOfVec ctx) $ do
        c' <- mapM emitType ctx
        a <- emitType t
        (x, b) <- extendCtx (emitType s)
        pure [ GDataDecl noLoc DataType [] (fromString n)
               (toList $ (\x a -> KindedVar (fromString x) a) <$> vs <*> c')
               (Just (tyFun a)) [] []
             , TypeInsDecl noLoc
               (foldl ($$) (fromString n) (fromString <$> vs) @@ fromString x)
               b
             ]
  in r

emitLambda :: String -> Vec n (H.Type String n) -> H.Type String n -> String -> H.Type String (S n) -> [Decl]
emitLambda n ctx t p s =
  let (vs, r) = runEmit $ extendCtx' (snOfVec ctx) $ do
        c' <- mapM emitType ctx
        a <- emitType t
        (x, b) <- extendCtx (emitType s)
        pure [ GDataDecl noLoc DataType [] (fromString n)
               (toList $ (\x a -> KindedVar (fromString x) a) <$> vs <*> c')
               (Just (tyPi a (foldl ($$) (fromString p) (fromString <$> vs)))) [] []
             , TypeInsDecl noLoc
               (foldl ($$) (fromString n) (fromString <$> vs) @@@ fromString x)
               b
             ]
  in r

emitFix :: String -> Vec n (H.Type String n) -> Vec m (String, String, H.Type String n, H.Type String (Plus m n)) -> Fin m -> [Decl]
emitFix n ctx v b =
  let (vs, r) = runEmit $ extendCtx' (snOfVec ctx) $ do
        c' <- mapM emitType ctx
        let cBndrs = toList ((\x a -> KindedVar (fromString x) a) <$> vs <*> c')
        let appVs vs a = foldl ($$) a (fmap fromString vs)
        ts <- forM v (emitType . view _3)
        rs <- iforM v $ \i (a, b, _, d) -> do
          (vs2, dTy) <- extendCtx'' (snOfVec v) (emitType d)
          pure [ ClosedTypeFamDecl noLoc (fromString a) cBndrs
                 (Just (lookupVec ts i))
                 [ TypeEqn (appVs vs (fromString a))
                   (foldl ($$) (appVs vs (fromString b)) (fmap (appVs vs . fromString . view _1) v))
                 ]
               , ClosedTypeFamDecl noLoc (fromString b) (cBndrs ++ toList ((\x a -> KindedVar (fromString x) a) <$> vs2 <*> ts))
                 (Just (lookupVec ts i))
                 [ TypeEqn (appVs vs2 (appVs vs (fromString b))) dTy
                 ]
               ]
        pure ( TypeDecl noLoc (fromString n) cBndrs (foldl ($$) (fromString (lookupVec v b ^. _1)) (fmap fromString vs))
               : concat rs)
  in r

emitDefinition :: H.Definition String -> [Decl]
emitDefinition (H.ConstDef n t) =
  [TypeDecl noLoc (fromString n) [] (runEmit (emitType t))]
emitDefinition (H.IndDef n s c) =
  let (tvs, k) = runEmit (emitSignature s)
      (c1, c2) = unzip (fmap (uncurry (emitConstructor n')) c)
      n'       = n ++ "'"
  in
  [ TypeFamDecl  noLoc (fromString n) [] (Just (foldl (==>) k (snd <$> tvs)))
  , TypeInsDecl  noLoc (fromString n) (fromString n')
  , GDataDecl    noLoc DataType [] (fromString n') (fmap (uncurry KindedVar) tvs) (Just k) c1 []
  , GDataInsDecl noLoc DataType ("Sing" $$ (foldl (\a (x, _) -> a $$ TyVar x) (fromString n') tvs) $$ "b_") (Just star) c2 []
  ]

emitConstructor :: String -> (String, String) -> Constructor (H.Type String) Z -> (GadtDecl, GadtDecl)
emitConstructor m (n, sn) c =
  let (vs, k) = runEmit (emitConstructor' c)
  in ( GadtDecl noLoc (fromString n) []
       (TyForall (Just (fmap (uncurry KindedVar) vs)) []
        (foldr (\(x, _) t -> "P" $$ TyVar x ==> t) k vs))
     , GadtDecl noLoc (fromString sn) []
       (TyForall (Just (fmap (uncurry KindedVar) vs)) []
        (foldr (\(x, _) t -> "Sing'" $$ TyVar x ==> t) ("Sing'" $$ (foldl (\a (x, _) -> a $$ (TyKind "'P" ("P" $$ TyVar x))) (fromString n) vs)) vs))
     )
  where emitConstructor' :: Constructor (H.Type String) a -> Reader ([String], Vec a String) ([(Name, Kind)], Kind)
        emitConstructor' (TEmpty (Application a as)) = do
          -- a'  <- emitType a
          let a' = fromString m
          as' <- mapM emitType as
          pure ([], foldl ($$) a' as')
        emitConstructor' (TNext a b) = do
          a' <- emitType a
          (x, b') <- extendCtx (emitConstructor' b)
          pure (b' & _1 %~ ((fromString x, a'):))

emitSignature :: Signature (H.Type String) a -> Reader ([String], Vec a String) ([(Name, Kind)], Kind)
emitSignature (TEmpty a)  = ([],) <$> emitType a
emitSignature (TNext a b) = do
  a' <- emitType a
  (x, b') <- extendCtx (emitSignature b)
  pure (b' & _1 %~ ((fromString x, a'):))

emitType :: H.Type String a -> Reader ([String], Vec a String) Type
emitType (H.TVar a)    = fromString <$> view (_2.ix a)
emitType (H.TConst a)  = pure (fromString a)
emitType (H.TPi a b)   = tyPi <$> emitType a <*> emitType b
emitType (H.TCApp a b) = ($$) <$> emitType a <*> emitType b
emitType (H.TApp a b)  = (@@@) <$> emitType a <*> emitType b
emitType H.TType       = pure star
emitType (H.TLift a)   = emitType (H.mapType id undefined a)
emitType H.TUNKNOWN    = pure "UNKNOWN"
