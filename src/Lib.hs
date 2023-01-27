module Lib
  ( someFunc,
    Expr (..),
    Typ (..),
    MonoType (..),
  )
where
import Data.Map (Map)

someFunc :: IO ()
someFunc = putStrLn "someFunc"

newtype EIdent = V String
  deriving (Eq, Show)

newtype TIdent = T String
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
  | TApp MonoType [MonoType]
data Typ
  = TAll [TIdent] MonoType

type Context = Map EIdent Typ

-- unify two types

