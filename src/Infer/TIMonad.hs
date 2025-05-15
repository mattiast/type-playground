{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Infer.TIMonad where

import Control.Monad (foldM)
import Control.Monad.State.Class (MonadState (..), gets, modify)
import Control.Monad.Trans.Maybe (MaybeT)
import Control.Monad.Trans.State (State)
import Data.Map qualified as M
import Data.Set qualified as S
import Infer.Expr

newtype TypeEnv = TypeEnv (M.Map String Scheme)

remove :: TypeEnv -> String -> TypeEnv
remove (TypeEnv env) var = TypeEnv (M.delete var env)

instance Types TypeEnv where
  ftv (TypeEnv env) = ftv (M.elems env)
  apply s (TypeEnv env) = TypeEnv (M.map (apply s) env)

data TIState = TIState
  { nextVar :: Int,
    subst :: Subst,
    senv :: TypeEnv
  }

type TI a = MaybeT (State TIState) a

newTyVar :: String -> TI Type
newTyVar prefix = do
  st <- get
  let v = TVar (prefix ++ show (nextVar st))
  put $ st {nextVar = nextVar st + 1}
  return v

instantiate :: Scheme -> TI Type
instantiate (Scheme vars t) = do
  nvars <- mapM (\v -> (v,) <$> newTyVar "a") vars
  let s = Subst $ M.fromList nvars
  return $! apply s t

subb :: (Types a) => a -> TI a
subb t = do
  s <- get
  return $ apply (subst s) t

unify :: Type -> Type -> TI ()
unify t1 t2 = do
  Just sub <- return $ mgu t1 t2
  modify (\st -> st {subst = sub <> subst st})
  return ()

scopedExtend :: [(String, Scheme)] -> TI a -> TI a
scopedExtend bindings act = do
  te@(TypeEnv env) <- gets senv
  let env' = TypeEnv (M.fromList bindings `M.union` env)
  modify (\st -> st {senv = env'})
  x <- act
  env'' <- subb te
  modify (\st -> st {senv = env''})
  return x

tilookup :: String -> TI Type
tilookup x = do
  (TypeEnv env) <- gets senv
  Just sigma <- return $ M.lookup x env
  instantiate sigma

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
