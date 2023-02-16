{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module SystemF (TV, N, Typ (..), Exp (..), TContext, Context, checkType, checkExpr, runMM, MM) where

import Control.Monad.Trans.Except (ExceptT (ExceptT), runExceptT)
import Data.Map qualified as M
import Data.Set qualified as S
import GHC.Generics (Generic)
import Unbound.Generics.LocallyNameless

type TV = Name Typ

data Typ
  = TVar TV
  | TArr Typ Typ
  | TAll (Bind TV Typ)
  deriving (Generic)

instance Show Typ where
  show (TVar t) = show t
  show (TArr t1 t2) = "(" ++ show t1 ++ ") → " ++ show t2
  show (TAll bnd) = "∀( " ++ show bnd ++ " . )"

type N = Name Exp

data Exp
  = EVar N
  | EAbs Typ (Bind N Exp)
  | EApp Exp Exp
  | ETAbs (Bind TV Exp)
  | ETApp Typ Exp
  deriving (Show, Generic)

-- Δ = set of statements "τ is a type"
type TContext = S.Set TV

-- Γ = set of statements "e : τ"
type Context = M.Map N Typ

instance Subst Typ Typ where
  isvar (TVar t) = Just (SubstName t)
  isvar _ = Nothing

instance Alpha Exp

instance Alpha Typ

type MM a = (ExceptT String) FreshM a

runMM :: MM a -> Either String a
runMM = runFreshM . runExceptT

checkType :: TContext -> Typ -> MM ()
checkType delta (TVar t) =
  if S.member t delta
    then return ()
    else fale ("Type variable not in scope: " ++ show t)
checkType delta (TArr t1 t2) = do
  checkType delta t1
  checkType delta t2
checkType delta (TAll bnd) = do
  (t, tau) <- unbind bnd
  checkType (S.insert t delta) tau

fale :: String -> MM a
fale s = ExceptT $ pure $ Left s

grd :: Bool -> String -> MM ()
grd b errmsg = if b then pure () else fale errmsg

checkExpr :: TContext -> Context -> Exp -> MM Typ
checkExpr _ gamma (EVar x) = case M.lookup x gamma of
  Just t -> return t
  Nothing -> fale ("Variable not in scope: " ++ show x)
checkExpr delta gamma (EAbs t1 bnd) = do
  (x, e) <- unbind bnd
  checkType delta t1
  t2 <- checkExpr delta (M.insert x t1 gamma) e
  return (TArr t1 t2)
checkExpr delta gamma (EApp e1 e2) = do
  tarr <- checkExpr delta gamma e1
  case tarr of
    TArr t2' t -> do
      t2 <- checkExpr delta gamma e2
      grd (aeq t2 t2') "Application types don't match"
      return t
    _ -> fale "Application of non-function type"
checkExpr delta gamma (ETAbs bnd) = do
  (t, e) <- unbind bnd
  tau <- checkExpr (S.insert t delta) gamma e
  return (TAll $ bind t tau)
checkExpr delta gamma (ETApp tau e) = do
  checkType delta tau
  tall <- checkExpr delta gamma e
  case tall of
    TAll bnd -> do
      (t, tau') <- unbind bnd
      return (subst t tau tau')
    _ -> fale "Type application to non-generic type"

unit :: Exp
unit = ETAbs $ bind r (EAbs (TVar r) $ bind x (EVar x))
  where
    r = s2n "r"
    x = s2n "x"

nat :: Typ
nat = TAll $ bind t (TArr (TVar t) (TArr (TArr (TVar t) (TVar t)) (TVar t)))
  where
    t = s2n "t"

zero :: Exp
zero =
  let z = s2n "z"
      s = s2n "s"
      t = s2n "t"
   in ETAbs $ bind t $ EAbs (TVar t) $ bind z $ EAbs (TArr (TVar t) (TVar t)) $ bind s $ EVar z
