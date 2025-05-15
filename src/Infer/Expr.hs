module Infer.Expr where

import Data.Function ((&))
import Data.Map qualified as M
import Data.Maybe (fromMaybe)
import Data.Set qualified as S

data Exp
  = EVar String
  | EApp Exp [Exp]
  | EAbs [String] Exp
  | ELet String Exp Exp
  deriving (Eq, Ord, Show)

data Type
  = TVar String
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

  apply (Subst m) t@(TVar n) =
    M.lookup n m
      & fromMaybe t
  apply s (TFun t1 t2) = TFun (apply s t1) (apply s t2)
  apply s (TApp c ts) = TApp c (map (apply s) ts)

instance Types Scheme where
  ftv (Scheme vars t) = ftv t `S.difference` S.fromList vars
  apply (Subst m) (Scheme vars t) = Scheme vars (apply (Subst $ foldr M.delete m vars) t)

instance (Types a) => Types [a] where
  ftv = S.unions . map ftv
  apply s = map (apply s)

newtype Subst = Subst (M.Map String Type)

instance Semigroup Subst where
  s1@(Subst m1) <> (Subst m2) = Subst (M.union (M.map (apply s1) m2) m1)

instance Monoid Subst where
  mempty = Subst M.empty
