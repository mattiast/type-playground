module Lib
  ( someFunc,
    Expr (..),
    Typ (..),
    MonoType (..),
  )
where

import Control.Monad.Trans.State (State, get, put)
import Data.Map (Map)

someFunc :: IO ()
someFunc = putStrLn "someFunc"

newtype EIdent = V Int
  deriving (Eq, Show)

newtype TIdent = T Int
  deriving (Eq, Show)

data Expr
  = EVar EIdent
  | ELet EIdent Expr Expr
  | EFun [EIdent] Expr
  | EApp Expr [Expr]

-- NOTE quantifiers can only appear top level!
data MonoType
  = TLit String
  | TVar TIdent
  | TArr [MonoType] MonoType
  | TApp String [MonoType]

data Typ
  = TAll [TIdent] MonoType

type Context = Map EIdent Typ

-- unify two types

-- Type inference:
-- [Abs] Given (EFun xs e), we want Γ,x:τ |- e:τ'
--   Add a new type variable to the context for x
-- [Var] Given (EVar x), we want to take (x:σ) ∈ Γ and
--   give new variables to all quantified identifiers in σ
-- [Let] Given (ELet x e0 e)
--   1. first infer e0 in the same context Γ, get type τ
--   2. quantify all variables of τ not bound in Γ, to get type τ_Γ
--   3. infer e in context Γ,e0:τ_Γ
-- [App] Given (EApp e es), is more tricky
--   1. infer e in Γ, the result should be of the form τ → τ'
--   2. if it is an open type variable, bring in two new variables and refine it
--   3. if it's anything else, it's a type error
--   4. now argument should give the type τ, unify

-------------------------------------------------

-- State: must be able to get fresh variables

data InferState = InferState Int ()

type MMonad a = State InferState a

fresh :: MMonad Int
fresh = do
  (InferState i _) <- get
  put (InferState (i + 1) ())
  return i

inst :: Typ -> MMonad MonoType
inst = undefined

unify :: MonoType -> MonoType -> MMonad ()
unify = undefined

infer :: Context -> Expr -> MMonad (Maybe Typ)
infer gamma e = case e of
  EVar x -> undefined
  ELet x e0 e -> undefined
  EFun xs e -> undefined
  EApp e args -> undefined
