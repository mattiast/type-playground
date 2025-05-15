{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Infer.TIMonad where

import Control.Monad (foldM)
import Control.Monad.State.Class (MonadState (..))
import Control.Monad.Trans.Maybe (MaybeT)
import Control.Monad.Trans.State (State)
import Data.Map qualified as M
import Data.Set qualified as S
import Infer.Expr

newtype TIState = TIState Int

type TI a = MaybeT (State TIState) a

newTyVar :: String -> TI Type
newTyVar prefix = do
  (TIState i) <- get
  put (TIState (i + 1))
  return (TVar (prefix ++ show i))

instantiate :: Scheme -> TI Type
instantiate (Scheme vars t) = do
  nvars <- mapM (\v -> (v,) <$> newTyVar "a") vars
  let s = Subst $ M.fromList nvars
  return $! apply s t

mgu :: Type -> Type -> Maybe Subst
mgu (TVar u) t = varBind u t
mgu t (TVar u) = varBind u t
mgu (TFun l r) (TFun l' r')
  | length l == length l' =
      let f sub (t1, t2) = do
            s1 <- mgu (apply sub t1) (apply sub t2)
            return $ s1 <> sub
       in foldM f mempty $ zip (r : l) (r' : l')
mgu (TApp c1 ts1) (TApp c2 ts2)
  | c1 == c2 && length ts1 == length ts2 =
      let f sub (t1, t2) = do
            s1 <- mgu (apply sub t1) (apply sub t2)
            return $ s1 <> sub
       in foldM f mempty $ zip ts1 ts2
mgu _ _ = fail "Do not unify: t1 t2"

varBind :: String -> Type -> Maybe Subst
varBind u t
  | t == TVar u = return mempty
  | u `S.member` ftv t = fail "infinite type"
  | otherwise = return $ Subst (M.singleton u t)
