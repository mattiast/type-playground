-- |
-- Type checking for "Modernized Algol" language, described in chapter 34 of PFPL
module MA where

import Data.Map (Map)
import Data.Map qualified as M
import Data.Set (Set)
import Data.Set qualified as S

type N = String

data T = TNat | TArr T T | TCmd
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
  | ECmd Cmd
  deriving (Show)

type AName = String

type Signature = Set AName

data Cmd
  = CRet Exp
  | CBnd Exp N Cmd
  | CDcl Exp AName Cmd
  | CGet AName
  | CSet AName Exp
  deriving (Show)

-- Statics

tcExpr :: Context -> Signature -> Exp -> Maybe T
tcExpr g _ (EVar x) = M.lookup x g
tcExpr _ _ EIntZ = pure TNat
tcExpr g s (EIntS e) = do
  TNat <- tcExpr g s e
  return TNat
tcExpr g s (EIfZ e0 (x, e1) e) = do
  TNat <- tcExpr g s e
  t0 <- tcExpr g s e0
  t1 <- tcExpr (M.insert x TNat g) s e1
  True <- return (t0 == t1)
  return t0
tcExpr g s (EAbs x t1 e) = do
  t2 <- tcExpr (M.insert x t1 g) s e
  return (TArr t1 t2)
tcExpr g s (EApp e1 e2) = do
  t2 <- tcExpr g s e2
  TArr t2' t1 <- tcExpr g s e1
  True <- return (t2 == t2')
  return t1
tcExpr g s (EFix t x e) = do
  t' <- tcExpr (M.insert x t g) s e
  True <- return (t == t')
  return t
tcExpr g s (ECmd c) = do
  () <- tcCmd g s c
  return TCmd

tcCmd :: Context -> Signature -> Cmd -> Maybe ()
tcCmd g s (CRet e) = do
  TNat <- tcExpr g s e
  return ()
tcCmd g s (CBnd e x m) = do
  TCmd <- tcExpr g s e
  () <- tcCmd (M.insert x TNat g) s m
  return ()
tcCmd g s (CDcl e a m) = do
  TNat <- tcExpr g s e
  () <- tcCmd g (S.insert a s) m
  return ()
tcCmd _ s (CGet a) = do
  True <- return $ S.member a s
  return ()
tcCmd g s (CSet a e) = do
  True <- return $ S.member a s
  TNat <- tcExpr g s e
  return ()

-- Dynamics (eager semantics)

val :: Exp -> Bool
val e = case e of
  EIntZ -> True
  EIntS e' -> val e'
  EAbs {} -> True
  ECmd _ -> True
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
  ECmd c -> ECmd (substCmd x e1 c)

substCmd :: N -> Exp -> Cmd -> Cmd
substCmd x e1 (CRet e) = CRet (subst x e1 e)
substCmd x e1 c@(CBnd e y m) = if x == y then c else CBnd (subst x e1 e) y (substCmd x e1 m)
substCmd x e1 (CDcl e a m) = CDcl (subst x e1 e) a (substCmd x e1 m)
substCmd _ _ c@(CGet _) = c
substCmd x e1 (CSet a e) = CSet a (subst x e1 e)

step :: Exp -> Maybe Exp
step e | val e = Nothing
step (EIfZ e0 _ EIntZ) = Just e0
step (EIfZ _ (x, e1) (EIntS e)) = Just (subst x e e1)
step (EIfZ e0 st e) = do
  e' <- step e
  return (EIfZ e0 st e')
step (EApp e1@(EAbs x _ e) e2) =
  if val e2
    then Just (subst x e2 e)
    else EApp e1 <$> step e2
step (EApp e1 e2) = do
  e1' <- step e1
  return (EApp e1' e2)
step e@(EFix _ x e1) = Just (subst x e e1)
step (EIntS e) = do
  e' <- step e
  return (EIntS e')
step _ = Nothing

eval :: Exp -> Exp
eval e = case step e of
  Nothing -> e
  Just e' -> eval e'

type Memory = Map AName Exp

type State = (Memory, Cmd)

stepS :: State -> Maybe State
stepS (_, CRet e) | val e = Nothing
stepS (mu, CRet e) = do
  e' <- step e
  return (mu, CRet e')
stepS (mu, CBnd e x m) | not (val e) = do
  e' <- step e
  return (mu, CBnd e' x m)
stepS (mu, CBnd (ECmd (CRet e)) x m) | val e = Just (mu, substCmd x e m)
stepS (mu, CBnd (ECmd m1) x m2) = do
  (mu', m1') <- stepS (mu, m1)
  return (mu', CBnd (ECmd m1') x m2)
stepS (mu, CGet a) = Just (mu, CRet (mu M.! a))
stepS (mu, CSet a e) | val e = Just (M.insert a e mu, CRet e)
stepS (mu, CSet a e) = do
  e' <- step e
  return (mu, CSet a e')
stepS (mu, CDcl e a m) | not (val e) = do
  e' <- step e
  return (mu, CDcl e' a m)
stepS (mu, CDcl _ _ (CRet e')) | val e' = Just (mu, CRet e')
stepS (mu, CDcl e a m) = do
  (mu', m') <- stepS (M.insert a e mu, m)
  return (M.delete a mu', CDcl e a m')

-- Example

plus :: Exp
plus =
  EFix (TArr TNat (TArr TNat TNat)) "f"
    ( EAbs "x" TNat
        ( EAbs "y" TNat
            (EIfZ (EVar "x") ("y", EIntS (EApp (EApp (EVar "f") (EVar "x")) (EVar "y"))) (EVar "y"))
        )
    )

z :: Exp
z = EIntZ

sc :: Exp -> Exp
sc = EIntS

five :: Exp
five = EApp (EApp plus (sc $ sc z)) (sc $ sc $ sc z)
