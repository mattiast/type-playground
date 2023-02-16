{-|
Type checking for language PCF, described in chapter 19 of PFPL
-}
{-# LANGUAGE MultiParamTypeClasses, DeriveGeneric #-}
module PCF where

import Data.Map (Map)
import qualified Data.Map as M
import Unbound.Generics.LocallyNameless
import Control.Monad.Trans.Maybe (MaybeT (..))
import GHC.Generics (Generic)

type N = Name Exp

data T = TNat | TArr T T
  deriving (Eq, Ord, Show, Generic)

type Context = Map N T

eo :: Context
eo = M.empty

data Exp
  = EVar N
  | EIntZ
  | EIntS Exp
  | EIfZ Exp (Bind N Exp) Exp
  | EAbs T (Bind N Exp)
  | EApp Exp Exp
  | EFix T (Bind N Exp)
  deriving (Show, Generic)

instance Alpha T
instance Alpha Exp

instance Subst Exp T
instance Subst Exp Exp where
  isvar (EVar x) = Just (SubstName x)
  isvar _ = Nothing

-- Statics

type MM a = MaybeT FreshM a
runMM :: MM a -> Maybe a
runMM = runFreshM . runMaybeT

tc :: Context -> Exp -> MM T
tc g (EVar x) = MaybeT $ pure $ M.lookup x g
tc _ EIntZ = pure TNat
tc g (EIntS e) = do
  TNat <- tc g e
  return TNat
tc g (EIfZ e0 bnd1 e) = do
  (x,e1) <- unbind bnd1
  TNat <- tc g e
  t0 <- tc g e0
  t1 <- tc (M.insert x TNat g) e1
  True <- return (t0 == t1)
  return t0
tc g (EAbs t1 bnd) = do
  (x,e) <- unbind bnd
  t2 <- tc (M.insert x t1 g) e
  return (TArr t1 t2)
tc g (EApp e1 e2) = do
  t2 <- tc g e2
  TArr t2' t1 <- tc g e1
  True <- return (t2 == t2')
  return t1
tc g (EFix t bnd) = do
  (x,e) <- unbind bnd
  t' <- tc (M.insert x t g) e
  True <- return (t == t')
  return t

-- Examples

plus :: Exp
plus = EFix (TArr TNat (TArr TNat TNat)) $ bind f (
  EAbs TNat $ bind x (
    EAbs TNat $ bind y (
      EIfZ (EVar x) (bind y $ EIntS (EApp (EApp (EVar f) (EVar x)) (EVar y))) (EVar y)
    )
  ))
  where
    f = s2n "f"
    x = s2n "x"
    y = s2n "y"

z :: Exp
z = EIntZ

s :: Exp -> Exp
s = EIntS

five :: Exp
five = EApp (EApp plus (s$s z)) (s$s$s z)

-- Dynamics (lazy semantics)

val :: Exp -> Bool
val e = case e of
  EIntZ -> True
  EIntS _ -> True
  EAbs {} -> True
  _ -> False

step :: Exp -> MM Exp
step (EIfZ e0 _ EIntZ) = pure e0
step (EIfZ _ bnd1 (EIntS e)) = do
  (x, e1) <- unbind bnd1
  pure (subst x e e1)
step (EIfZ e0 st e) = do
  e' <- step e
  return (EIfZ e0 st e')
step (EApp (EAbs _ bnd) e2) = do
  (x, e) <- unbind bnd
  pure (subst x e2 e)
step (EApp e1 e2) = do
  e1' <- step e1
  return (EApp e1' e2)
step e@(EFix _ bnd) = do
  (x,e1) <- unbind bnd
  pure (subst x e e1)
step _ = fail "hjoo"

eval :: Exp -> FreshM Exp
eval e = do
  e' <- runMaybeT (step e)
  case e' of
    Nothing -> return e
    Just e'' -> eval e''
