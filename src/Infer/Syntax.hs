{-# LANGUAGE OverloadedStrings #-}
{-# HLINT ignore "Use <$>" #-}

module Infer.Syntax where

import Control.Applicative (many, (<|>))
import Data.Attoparsec.ByteString.Char8 (Parser)
import Data.Attoparsec.ByteString.Char8 qualified as A
import Data.ByteString.Char8 qualified as B
import Data.List (intercalate, nub)
import Data.Map qualified as M
import Infer.Expr

parseExpr :: Parser Exp
parseExpr = parseLet <|> parseFun <|> parseSimple
  where
    parseLet = do
      _ <- A.string "let "
      var <- parseId
      _ <- A.string " = "
      e1 <- parseExpr
      _ <- A.string " in "
      e2 <- parseExpr
      return (ELet var e1 e2)
    parseId :: Parser String
    parseId = B.unpack <$> A.takeWhile1 (A.inClass "_a-zA-Z0-9")
    parseFun = do
      _ <- A.string "fun "
      alist <- parseId `A.sepBy` A.char ' '
      _ <- A.string " -> "
      e <- parseExpr
      return (EAbs alist e)
    parseFactor =
      (A.char '(' *> parseExpr <* A.char ')')
        <|> (EVar <$> parseId)
    parseSimple = do
      f <- parseFactor
      calls <- many (A.char '(' *> (parseExpr `A.sepBy` A.string ", ") <* A.char ')')
      return $ foldl EApp f calls

isSimple :: Type -> Bool
isSimple (TFun _ _) = False
isSimple _ = True

generalizeWithABC :: Type -> Scheme
generalizeWithABC t =
  let fvord :: Type -> [String]
      fvord (TVar n) = [n]
      fvord (TFun ts t2) = nub (concatMap fvord (ts ++ [t2]))
      fvord (TApp _c ts) = nub (concatMap fvord ts)
      vars = nub $ fvord t
      repl :: Subst
      repl = Subst $ M.fromList $ zip vars [TVar [c] | c <- ['a' .. 'z']]
      typ = apply repl t
      nvars = nub $ fvord typ
   in Scheme nvars typ

renderType :: Type -> String
renderType (TVar n) = n
renderType (TFun [t1] t2) | isSimple t1 = renderType t1 ++ " -> " ++ renderType t2
renderType (TFun ts t1) = "(" ++ intercalate ", " (map renderType ts) ++ ") -> " ++ renderType t1
renderType (TApp c []) = c
renderType (TApp c ts) = c ++ "[" ++ intercalate ", " (map renderType ts) ++ "]"

renderScheme :: Scheme -> String
renderScheme (Scheme vars t) =
  let foral = case vars of
        [] -> ""
        _ -> "forall[" ++ unwords vars ++ "] "
   in foral ++ renderType t

myParse :: B.ByteString -> Either String Exp
myParse = A.parseOnly (parseExpr <* A.endOfInput)