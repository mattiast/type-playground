{-|
Type checking for "Modernized Algol" language, described in chapter 34 of PFPL
-}
module MA where

import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S

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
