module Coq.Parse where

import Coq
import Telescope

import Data.Bifunctor
import Data.Bitraversable
import Data.Nat
import Data.Sexp
import Text.Read
import Data.ByteString (ByteString)
import qualified Data.ByteString as B
import Control.Monad.Except
import Control.Lens
import Debug.Trace

newtype ParseM a = ParseM { unParseM :: Except () a }
                   deriving (Functor, Applicative, Monad, MonadError ())

parseInt :: String -> ParseM Int
parseInt a = maybe (throwError undefined) pure (readMaybe a)

parseVar :: SN a -> Int -> ParseM (Fin a)
parseVar SZ     _ = throwError undefined
parseVar (SS n) 1 = pure FZ
parseVar (SS n) m = FS <$> parseVar n (m - 1)

parseExpr :: SN a -> Sexp -> ParseM (Expr String a)
parseExpr c (Atom "Type")                       = pure EType
parseExpr c (Sexp [Atom "App", a, b, d])        = EApp <$> parseExpr c a <*> parseExpr c b <*> parseExpr c d
parseExpr c (Sexp [Atom "Prod", a, b])          = EPi <$> parseExpr c a <*> parseExpr (SS c) b
parseExpr c (Sexp [Atom "Lambda", a, b])        = EAbs <$> parseExpr c a <*> parseExpr (SS c) b
parseExpr c (Sexp [Atom "Var", Atom a])         = EVar <$> (parseVar c =<< parseInt a)
parseExpr c (Sexp [Atom "Ind", Atom a, Atom b]) = EInd a <$> parseInt b
parseExpr c (Sexp [Atom "Construct", Atom a, Atom b, Atom b']) =
  ECons a <$> parseInt b <*> parseInt b'
parseExpr c (Sexp [Atom "Const", Atom a])       = pure (EConst a)
parseExpr c (Sexp [Atom "Fix", Sexp a, Atom b]) = case vecOfList a of
  EVec as -> do
    let sm  = snOfVec as
        snm = plus sm c
    bs  <- traverse (\(Sexp [a, b]) -> (,) <$> parseExpr c a <*> parseExpr snm b) as
    b' <- parseVar sm . (+ 1) =<< parseInt b
    pure (EFix bs b')
parseExpr c (Sexp [Atom "Case", Sexp [Atom a, Atom a'], b, c', d, Sexp e]) =
  ECase <$> ((a,) <$> parseInt a') <*> parseExpr c b <*> parseExpr c c' <*> parseExpr c d <*> mapM (parseExpr c) e
parseExpr c a                                   = throwError (error (show a))

parseSignature :: SN a -> [Sexp] -> Sexp -> ParseM (Signature (Expr String) a)
parseSignature c []     b = TEmpty <$> parseExpr c b
parseSignature c (a:as) b = TNext <$> parseExpr c a <*> parseSignature (SS c) as b

parseConstructor :: Sexp -> ParseM (String, Constructor (Expr String) 'Z)
parseConstructor (Sexp [Atom a, Sexp [Sexp c1, Sexp [c2, Sexp c3]]]) = (a,) <$> parseConstructor' SZ c1 c2 c3
  where parseConstructor' :: SN a -> [Sexp] -> Sexp -> [Sexp] -> ParseM (Constructor (Expr String) a)
        parseConstructor' c []     c2 c3 = TEmpty <$> (Application <$> parseExpr c c2 <*> mapM (parseExpr c) c3)
        parseConstructor' c (a:as) c2 c3 = TNext <$> parseExpr c a <*> parseConstructor' (SS c) as c2 c3
parseConstructor a = throwError (error (show a))

parseInductive :: String -> Int -> Sexp -> ParseM (Definition String)
parseInductive i j (Sexp [Atom a, Atom "Inductive", Sexp [Sexp s1, s2], Sexp cons]) =
  InductiveDefinition i j <$> parseSignature SZ s1 s2 <*> mapM parseConstructor cons
parseInductive i j s = throwError (error (show s))

parseDefinition :: Sexp -> ParseM [Definition String]
parseDefinition (Sexp [Atom "Constant", Atom a, b])       = pure . ConstantDefinition a <$> parseExpr SZ b
parseDefinition (Sexp [Atom "Inductive", Atom a, Sexp b]) = zipWithM (parseInductive a) [0..] b
parseDefinition s = throwError (error (show s))

parseDefinitions :: Sexp -> ParseM [Definition String]
parseDefinitions (Sexp a) = concat <$> (parseDefinition `mapM` a)
parseDefinitions _ = throwError undefined

parseCoq :: ByteString -> Either () [Definition String]
parseCoq b = parseSexp b & \case
  Left _  -> Left ()
  Right s -> parseDefinitions s
             & unParseM
             & runExcept
