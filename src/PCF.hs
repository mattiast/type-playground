module PCF where

import Data.Map (Map)
import Data.Map qualified as M

type N = String

data T = TNat | TArr T T
  deriving (Eq, Ord, Show)

type Context = Map N T

data Exp
  = EVar N
  | EIntZ
  | EIntS Exp
  | EIfZ Exp (N, Exp) Exp
  | EAbs N T Exp
  | EApp Exp Exp
  | EFix T N Exp
  deriving (Show)

-- Statics

tc :: Context -> Exp -> Maybe T
tc g (EVar x) = M.lookup x g
tc _ EIntZ = pure TNat
tc g (EIntS e) = do
  TNat <- tc g e
  return TNat
tc g (EIfZ e0 (x, e1) e) = do
  TNat <- tc g e
  t0 <- tc g e0
  t1 <- tc (M.insert x TNat g) e1
  True <- return (t0 == t1)
  return t0
tc g (EAbs x t1 e) = do
  t2 <- tc (M.insert x t1 g) e
  return (TArr t1 t2)
tc g (EApp e1 e2) = do
  t2 <- tc g e2
  TArr t2' t1 <- tc g e1
  True <- return (t2 == t2')
  return t1
tc g (EFix t x e) = do
  t' <- tc (M.insert x t g) e
  True <- return (t == t')
  return t

plus :: Exp
plus = EFix (TArr TNat (TArr TNat TNat)) "f"
    (EAbs "x" TNat (EAbs "y" TNat
        (EIfZ (EVar "x") ("y", EIntS (EApp (EApp (EVar "f") (EVar "x")) (EVar "y"))) (EVar "y"))))

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

subst :: N -> Exp -> Exp -> Exp
subst x e1 e = case e of
  EVar y -> if x == y then e1 else e
  EIntZ -> e
  EIntS ee -> EIntS (subst x e1 ee)
  EIfZ e0 (y, ee1) ee -> EIfZ (subst x e1 e0) (y, if x == y then ee1 else subst x e1 ee1) (subst x e1 ee)
  EAbs y t ee -> if x == y then e else EAbs y t (subst x e1 ee)
  EApp ee1 ee2 -> EApp (subst x e1 ee1) (subst x e1 ee2)
  EFix t y ee -> if x == y then e else EFix t y (subst x e1 ee)

step :: Exp -> Maybe Exp
step (EIfZ e0 _ EIntZ) = Just e0
step (EIfZ _ (x, e1) (EIntS e)) = Just (subst x e e1)
step (EIfZ e0 st e) = do
  e' <- step e
  return (EIfZ e0 st e')
step (EApp (EAbs x _ e) e2) = Just (subst x e2 e)
step (EApp e1 e2) = do
  e1' <- step e1
  return (EApp e1' e2)
step e@(EFix _ x e1) = Just (subst x e e1)
step _ = Nothing

eval :: Exp -> Exp
eval e = case step e of
  Nothing -> e
  Just e' -> eval e'
