{-# LANGUAGE OverloadedStrings #-}


-- |
-- Hindley-Milner algorithm, 90% plagiarized from https://github.com/wh5a/Algorithm-W-Step-By-Step
module Infer
  ( infer,
    myParse,
    myEnv,
    generalizeWithABC,
    renderScheme,
    main,
  )
where

import Control.Monad.State.Class (gets)
import Control.Monad.Trans.Maybe (MaybeT (runMaybeT))
import Control.Monad.Trans.State (evalState)
import Data.ByteString.Char8 qualified as B
import Data.Map qualified as M
import Data.Set qualified as S
import Infer.Expr
import Infer.Syntax (generalizeWithABC, myParse, renderScheme)
import Infer.TIMonad

generalize :: TypeEnv -> Type -> Scheme
generalize env t = Scheme vars t
  where
    vars = S.toList (ftv t `S.difference` ftv env)

ti :: Exp -> TI Type
ti (EVar n) = tilookup n
ti (EAbs ns e) = do
  tvs <- mapM (\_ -> newTyVar "a") ns -- these are the parameter types in lambda
  t1 <- scopedExtend (zip ns [Scheme [] tv | tv <- tvs]) $ ti e
  subb (TFun tvs t1)
ti (EApp ef eargs) = do
  ts <- traverse ti eargs
  t1 <- ti ef
  ts <- subb ts
  tv <- newTyVar "a" -- type of the return value
  unify t1 (TFun ts tv)
  subb tv
ti (ELet x e1 e2) = do
  t1 <- ti e1
  env <- gets senv
  scopedExtend [(x, generalize env t1)] $ ti e2

infer :: TypeEnv -> Exp -> Maybe Type
infer env e =
  evalState (runMaybeT $ ti e) (TIState 0 mempty env)

myEnv :: TypeEnv
myEnv =
  let a = TVar "a"
      b = TVar "b"
      tList t = TApp "list" [t]
      tInt = TApp "int" []
      tBool = TApp "bool" []
      tPair t1 t2 = TApp "pair" [t1, t2]
   in TypeEnv $
        M.fromList
          [ ("head", Scheme ["a"] (TFun [tList a] a)),
            ("tail", Scheme ["a"] (TFun [tList a] (tList a))),
            ("nil", Scheme ["a"] (tList a)),
            ("cons", Scheme ["a"] (TFun [a, tList a] (tList a))),
            ("cons_curry", Scheme ["a"] (TFun [a] (TFun [tList a] (tList a)))),
            ("map", Scheme ["a", "b"] (TFun [TFun [a] b, tList a] (tList b))),
            ("map_curry", Scheme ["a", "b"] (TFun [TFun [a] b] (TFun [tList a] (tList b)))),
            ("one", Scheme [] tInt),
            ("zero", Scheme [] tInt),
            ("succ", Scheme [] (TFun [tInt] tInt)),
            ("plus", Scheme [] (TFun [tInt, tInt] tInt)),
            ("eq", Scheme ["a"] (TFun [a, a] tBool)),
            ("eq_curry", Scheme ["a"] (TFun [a] (TFun [a] tBool))),
            ("not", Scheme [] (TFun [tBool] tBool)),
            ("true", Scheme [] tBool),
            ("false", Scheme [] tBool),
            ("pair", Scheme ["a", "b"] (TFun [a, b] (tPair a b))),
            ("pair_curry", Scheme ["a", "b"] (TFun [a] (TFun [b] (tPair a b)))),
            ("first", Scheme ["a", "b"] (TFun [tPair a b] a)),
            ("second", Scheme ["a", "b"] (TFun [tPair a b] b)),
            ("id", Scheme ["a"] (TFun [a] a)),
            ("const", Scheme ["a", "b"] (TFun [a] (TFun [b] a))),
            ("apply", Scheme ["a", "b"] (TFun [TFun [a] b, a] b)),
            ("apply_curry", Scheme ["a", "b"] (TFun [TFun [a] b] (TFun [a] b))),
            ("choose", Scheme ["a"] (TFun [a, a] a)),
            ("choose_curry", Scheme ["a"] (TFun [a] (TFun [a] a)))
          ]

main :: IO ()
main = do
  line <- B.getLine
  Right e <- return $ myParse line
  Just typ <- return $ infer myEnv e
  putStrLn $ renderScheme $ generalizeWithABC typ
