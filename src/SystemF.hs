module SystemF (TV, N, Typ (..), Exp (..), TContext, Context, checkType, checkExpr) where

import Data.Map qualified as M
import Data.Set qualified as S

type TV = String

data Typ
  = TVar TV
  | TArr Typ Typ
  | TAll TV Typ
  deriving (Eq)

instance Show Typ where
  show :: Typ -> String
  show (TVar t) = t
  show (TArr t1 t2) = "(" ++ show t1 ++ ") → " ++ show t2
  show (TAll t tau) = "∀(" ++ t ++"." ++ show tau ++ ")"


type N = String

data Exp
  = EVar N
  | EAbs Typ N Exp
  | EApp Exp Exp
  | ETAbs TV Exp
  | ETApp Typ Exp
  deriving (Show)

-- Δ = set of statements "τ is a type"
type TContext = S.Set TV

-- Γ = set of statements "e : τ"
type Context = M.Map N Typ

checkType :: TContext -> Typ -> Either String ()
checkType delta (TVar t) = if S.member t delta then return () else Left ("Type variable not in scope: " ++ t)
checkType delta (TArr t1 t2) = do
  checkType delta t1
  checkType delta t2
checkType delta (TAll t tau) = checkType (S.insert t delta) tau

grd :: Bool -> String -> Either String ()
grd b errmsg = if b then Right () else Left errmsg

checkExpr :: TContext -> Context -> Exp -> Either String Typ
checkExpr _ gamma (EVar x) = case M.lookup x gamma of
  Just t -> return t
  Nothing -> Left ("Variable not in scope: " ++ x)
checkExpr delta gamma (EAbs t1 x e) = do
  checkType delta t1
  t2 <- checkExpr delta (M.insert x t1 gamma) e
  return (TArr t1 t2)
checkExpr delta gamma (EApp e1 e2) = do
  tarr <- checkExpr delta gamma e1
  case tarr of
    TArr t2' t -> do
      t2 <- checkExpr delta gamma e2
      grd (t2 == t2') "Application types don't match"
      return t
    _ -> Left "Application of non-function type"
checkExpr delta gamma (ETAbs t e) = do
  tau <- checkExpr (S.insert t delta) gamma e
  return (TAll t tau)
checkExpr delta gamma (ETApp tau e) = do
  checkType delta tau
  tall <- checkExpr delta gamma e
  case tall of
    TAll t tau' -> do
      return (substType t tau tau')
    _ -> Left "Type application to non-generic type"

substType :: TV -> Typ -> Typ -> Typ
substType t tau' (TVar t') = if t == t' then tau' else TVar t'
substType t tau' (TArr t1 t2) = TArr (substType t tau' t1) (substType t tau' t2)
substType t tau' (TAll tt tau) = if t == tt then TAll tt tau else TAll tt (substType t tau' tau)

unit :: Exp
unit = ETAbs "r" (EAbs (TVar "r") "x" (EVar "x"))

nat :: Typ
nat = TAll "t" (TArr (TVar "t") (TArr (TArr (TVar "t") (TVar "t")) (TVar "t")))