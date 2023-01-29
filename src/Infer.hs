{-|
Hindley-Milner algorithm, 90% plagiarized from https://github.com/wh5a/Algorithm-W-Step-By-Step
-}
{-# LANGUAGE OverloadedStrings, TupleSections #-}
module Infer(
    infer,
    myParse,
    myEnv,
    generalizeWithABC,
    renderScheme,
    main,
) where
import qualified Data.Set as S
import qualified Data.Map as M
import Data.List ( foldl', intercalate, nub )
import Control.Monad.Trans.State (  State, evalState )
import Control.Applicative ( Alternative((<|>), many) )
import qualified Data.Attoparsec.ByteString.Char8 as A
import Data.Attoparsec.ByteString.Char8(Parser)
import qualified Data.ByteString.Char8 as B
import Control.Monad (foldM)
import Control.Monad.Trans.Maybe (MaybeT (runMaybeT))
import Control.Monad.State.Class (MonadState(..))
import Data.Function ((&))
import Data.Maybe (fromMaybe)

data Exp = EVar String
         | EApp Exp [Exp]
         | EAbs [String] Exp
         | ELet String Exp Exp
         deriving (Eq, Ord, Show)

data Type = TVar String
          | TFun [Type] Type
          | TApp String [Type]
          deriving (Eq, Ord, Show)

data Scheme = Scheme [String] Type

class Types a where
    ftv :: a -> S.Set String
    apply :: Subst -> a -> a

instance Types Type where
    ftv (TVar n) = S.singleton n
    ftv (TFun t1 t2) = ftv t1 `S.union` ftv t2
    ftv (TApp _c ts) = S.unions (map ftv ts)

    apply (Subst m) t@(TVar n) = M.lookup n m
                         & fromMaybe t
    apply s (TFun t1 t2) = TFun (apply s t1) (apply s t2)
    apply s (TApp c ts) = TApp c (map (apply s) ts)

instance Types Scheme where
    ftv (Scheme vars t) = ftv t `S.difference` S.fromList vars
    apply (Subst m) (Scheme vars t) = Scheme vars (apply (Subst $ foldr M.delete m vars) t)

instance Types a => Types [a] where
    ftv = S.unions . map ftv
    apply s = map (apply s)
    
newtype Subst = Subst (M.Map String Type)

instance Semigroup Subst where
    s1@(Subst m1) <> (Subst m2) = Subst (M.union (M.map (apply s1) m2) m1)
instance Monoid Subst where
    mempty = Subst M.empty

newtype TypeEnv = TypeEnv (M.Map String Scheme)

remove :: TypeEnv -> String -> TypeEnv
remove (TypeEnv env) var = TypeEnv (M.delete var env)

instance Types TypeEnv where
    ftv (TypeEnv env) = ftv (M.elems env)
    apply s (TypeEnv env) = TypeEnv (M.map (apply s) env)

generalize :: TypeEnv -> Type -> Scheme
generalize env t = Scheme vars t where
    vars = S.toList (ftv t `S.difference` ftv env)

newtype TIState = TIState Int

type TI a = MaybeT (State TIState) a

newTyVar :: String -> TI Type
newTyVar prefix = do
        (TIState i) <- get
        put (TIState (i+1))
        return (TVar (prefix ++ show i))

instantiate :: Scheme -> TI Type
instantiate (Scheme vars t) = do
        nvars <- mapM (\v -> (v,) <$> newTyVar "a") vars
        let s = Subst $ M.fromList nvars
        return $! apply s t

mgu :: Type -> Type -> Maybe Subst
mgu (TVar u) t = varBind u t
mgu t (TVar u) = varBind u t
mgu (TFun l r) (TFun l' r') | length l == length l' = let
    f sub (t1, t2) = do
        s1 <- mgu (apply sub t1) (apply sub t2)
        return $ s1 <> sub
    in foldM f mempty $ zip (r:l) (r':l')
mgu (TApp c1 ts1) (TApp c2 ts2) | c1 == c2 && length ts1 == length ts2 = let
    f sub (t1, t2) = do
        s1 <- mgu (apply sub t1) (apply sub t2)
        return $ s1 <> sub
    in foldM f mempty $ zip ts1 ts2
mgu _ _ = fail "Do not unify: t1 t2"

varBind :: String -> Type -> Maybe Subst
varBind u t | t == TVar u = return mempty
            | u `S.member` ftv t = fail "infinite type"
            | otherwise = return $ Subst (M.singleton u t)

ti :: TypeEnv -> Exp -> TI (Subst, Type)
ti (TypeEnv env) (EVar n) = case M.lookup n env of
                                Nothing -> fail "variable not bound"
                                Just sigma -> do
                                    t <- instantiate sigma
                                    return (mempty, t)
ti env (EAbs ns e) = do
        tvs <- mapM (\_ -> newTyVar "a") ns -- these are the parameter types in lambda
        let TypeEnv env' = foldl' remove env ns
            env'' = TypeEnv (env' `M.union` M.fromList (zip ns [ Scheme [] tv | tv <- tvs ]))
        (s1, t1) <- ti env'' e
        return (s1, TFun (apply s1 tvs) t1)
ti env (EApp ef eargs) = let
    go [] = return (mempty, [])
    go (e:es) = do
        (s1, ts) <- go es
        (s2, t) <- ti (apply s1 env) e
        return (s2 <> s1, t : apply s2 ts)
    in do (s1, ts) <- go eargs
          (s2, t1) <- ti (apply s1 env) ef
          tv <- newTyVar "a" -- type of the return value
          Just s3 <- return $ mgu t1 (TFun (apply s2 ts) tv)
          return (s3 <> s2 <> s1, apply s3 tv)
ti env (ELet x e1 e2) = do
        (s1, t1) <- ti env e1
        let TypeEnv env' = remove env x
            t' = generalize (apply s1 env) t1
            env'' = TypeEnv (M.insert x t' $ M.map (apply s1) env')
        (s2, t2) <- ti env'' e2
        return (s2 <> s1, t2)

infer :: TypeEnv -> Exp -> Maybe Type
infer env e = 
    evalState (runMaybeT $ ti env e) (TIState 0)
    & fmap snd
              

myEnv :: TypeEnv
myEnv = let a = TVar "a"
            b = TVar "b"
            tList t = TApp "list" [t]
            tInt = TApp "int" []
            tBool = TApp "bool" []
            tPair t1 t2 = TApp "pair" [t1,t2]
        in TypeEnv $ M.fromList [
      ("head", Scheme ["a"] (TFun [tList a] a))
    , ("tail", Scheme ["a"] (TFun [tList a] (tList a)))
    , ("nil", Scheme ["a"] (tList a))
    , ("cons", Scheme ["a"] (TFun [a, tList a] (tList a)))
    , ("cons_curry", Scheme ["a"] (TFun [a] (TFun [tList a] (tList a))))
    , ("map", Scheme ["a","b"] (TFun [TFun [a] b, tList a] (tList b)))
    , ("map_curry", Scheme ["a", "b"] (TFun [TFun [a] b] (TFun [tList a] (tList b))))
    , ("one", Scheme [] tInt)
    , ("zero", Scheme [] tInt)
    , ("succ", Scheme [] (TFun [tInt] tInt))
    , ("plus", Scheme [] (TFun [tInt, tInt] tInt))
    , ("eq", Scheme ["a"] (TFun [a, a] tBool))
    , ("eq_curry", Scheme ["a"] (TFun [a] (TFun [a] tBool)))
    , ("not", Scheme [] (TFun [tBool] tBool))
    , ("true", Scheme [] tBool)
    , ("false", Scheme [] tBool)
    , ("pair", Scheme ["a", "b"] (TFun [a, b] (tPair a b)))
    , ("pair_curry", Scheme ["a", "b"] (TFun [a] (TFun [b] (tPair a b))))
    , ("first", Scheme ["a", "b"] (TFun [tPair a b] a))
    , ("second", Scheme ["a", "b"] (TFun [tPair a b] b))
    , ("id", Scheme ["a"] (TFun [a] a))
    , ("const", Scheme ["a", "b"] (TFun [a] (TFun [b] a)))
    , ("apply", Scheme ["a", "b"] (TFun [TFun [a] b, a] b))
    , ("apply_curry", Scheme ["a", "b"] (TFun [TFun [a] b] (TFun [a] b)))
    , ("choose", Scheme ["a"] (TFun [a, a] a))
    , ("choose_curry", Scheme ["a"] (TFun [a] (TFun [a] a)))
  ]

parseExpr :: Parser Exp
parseExpr = parseLet <|> parseFun <|> parseSimple where
    parseLet = do
        _ <- A.string "let "
        var <- parseId
        _ <- A.string " = "
        e1 <- parseExpr
        _ <- A.string " in "
        e2 <- parseExpr
        return (ELet var e1 e2)
    parseId :: Parser String
    parseId = B.unpack <$> A.takeWhile1 (A.inClass "_a-zA-Z0-9")
    parseFun = do
        _ <- A.string "fun "
        alist <- parseId `A.sepBy` A.char ' '
        _ <- A.string " -> "
        e <- parseExpr
        return (EAbs alist e)
    parseFactor = (A.char '(' *> parseExpr <* A.char ')')
                 <|> (EVar <$> parseId)
    parseSimple = do
        f <- parseFactor
        calls <- many (A.char '(' *> (parseExpr `A.sepBy` A.string ", ") <* A.char ')')
        return $ foldl EApp f calls

isSimple :: Type -> Bool
isSimple (TFun _ _) = False
isSimple _ = True

generalizeWithABC :: Type -> Scheme
generalizeWithABC t = let
    fvord :: Type -> [String]
    fvord (TVar n) = [n]
    fvord (TFun ts t2) = nub (concatMap fvord (ts ++ [t2]))
    fvord (TApp _c ts) = nub (concatMap fvord ts)
    vars = nub $ fvord t
    repl :: Subst
    repl = Subst $ M.fromList $ zip vars [ TVar [c] | c <- ['a'..'z'] ]
    typ = apply repl t
    nvars = nub $ fvord typ
    in Scheme nvars typ

renderType :: Type -> String
renderType (TVar n) = n
renderType (TFun [t1] t2) | isSimple t1 = renderType t1 ++ " -> " ++ renderType t2
renderType (TFun ts t1) = "(" ++ intercalate ", " (map renderType ts) ++ ") -> " ++ renderType t1
renderType (TApp c []) = c
renderType (TApp c ts) = c ++ "[" ++ intercalate ", " (map renderType ts) ++ "]"

renderScheme :: Scheme -> String
renderScheme (Scheme vars t) = let
    foral = case vars of
                [] -> ""
                _ -> "forall[" ++ unwords vars ++ "] "
    in foral ++ renderType t

myParse :: B.ByteString -> Either String Exp
myParse = A.parseOnly (parseExpr <* A.endOfInput)

main :: IO ()
main = do
    line <- B.getLine
    Right e <- return $ myParse line
    Just typ <- return $ infer myEnv e
    putStrLn $ renderScheme $ generalizeWithABC typ
