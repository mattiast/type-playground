{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}

module While where

import Control.Applicative (asum)
import Control.Monad (MonadPlus (mzero), forM_, void)
import Data.Char (isLower)
import Data.Functor (($>))
import Data.List (foldl', foldl1')
import Data.Map qualified as M
import Data.Text (Text, unpack)
import Data.Text.IO qualified as T (hGetContents, readFile)
import System.IO (stdin)
import Text.Megaparsec (MonadParsec (eof, takeWhile1P), Parsec, between, many, runParser, sepBy1)
import Text.Megaparsec.Char qualified as P
import Text.Megaparsec.Char.Lexer qualified as L

-- call L.space at the beginning of the file

mySpace :: MonadParsec e Text m => m ()
mySpace = L.space P.space1 mzero mzero

lexeme :: MonadParsec e Text m => m a -> m a
lexeme = L.lexeme mySpace

symbol :: MonadParsec e Text m => Text -> m Text
symbol = L.symbol mySpace

parens :: MonadParsec e Text m => m a -> m a
parens = between (symbol "(") (symbol ")")

braces :: MonadParsec e Text m => m a -> m a
braces = between (symbol "{") (symbol "}")

type Var = Text

data AOp = Plus | Minus | Times | Div
  deriving (Show)

data BOp = And | Or
  deriving (Show)

data ROp = Lt | Gt
  deriving (Show)

data Expr a where
  EILit :: Int -> Expr Int
  EBLit :: Bool -> Expr Bool
  EVar :: Var -> Expr Int
  EAOp :: AOp -> Expr Int -> Expr Int -> Expr Int
  EBOp :: BOp -> Expr Bool -> Expr Bool -> Expr Bool
  EROp :: ROp -> Expr Int -> Expr Int -> Expr Bool

instance Show (Expr a) where
  show (EILit x) = show x
  show (EBLit x) = show x
  show (EVar x) = unpack x
  show (EAOp op x y) = unwords ["(", show op, show x, show y, ")"]
  show (EBOp op x y) = unwords ["(", show op, show x, show y, ")"]
  show (EROp op x y) = unwords ["(", show op, show x, show y, ")"]

data Stmt
  = Assign Var (Expr Int)
  | Seq Stmt Stmt
  | While (Expr Bool) Stmt
  | If (Expr Bool) Stmt Stmt
  deriving (Show)

---

parseAOp1 :: MonadParsec e Text m => m AOp
parseAOp1 =
  asum
    [ symbol "*" $> Times,
      symbol "/" $> Div
    ]

parseAOp2 :: MonadParsec e Text m => m AOp
parseAOp2 =
  asum
    [ symbol "+" $> Plus,
      symbol "-" $> Minus
    ]

parseAExpr :: MonadParsec e Text m => m (Expr Int)
parseAExpr = parseAExpr3

parseAExpr1 :: MonadParsec e Text m => m (Expr Int)
parseAExpr1 =
  asum
    [ EILit <$> lexeme L.decimal,
      EVar <$> parseVar,
      parens parseAExpr
    ]

parseAExpr2 :: MonadParsec e Text m => m (Expr Int)
parseAExpr2 = do
  x <- parseAExpr1
  rest <- many ((,) <$> parseAOp1 <*> parseAExpr1)
  return $ foldl' (\e1 (op, e2) -> EAOp op e1 e2) x rest

parseAExpr3 :: MonadParsec e Text m => m (Expr Int)
parseAExpr3 = do
  x <- parseAExpr2
  rest <- many ((,) <$> parseAOp2 <*> parseAExpr2)
  return $ foldl' (\e1 (op, e2) -> EAOp op e1 e2) x rest

parseBExpr :: MonadParsec e Text m => m (Expr Bool)
parseBExpr = be3
  where
    be1 = asum [symbol "true" $> EBLit True, symbol "false" $> EBLit False, parens parseBExpr, rel]
    relop = asum [symbol ">" $> Gt, symbol "<" $> Lt]
    rel = do
      x <- parseAExpr
      op <- relop
      EROp op x <$> parseAExpr
    be2 = do
      x <- be1
      rest <- many ((,) <$> (symbol "and" $> And) <*> be1)
      return $ foldl' (\e1 (op, e2) -> EBOp op e1 e2) x rest
    be3 = do
      x <- be2
      rest <- many ((,) <$> (symbol "or" $> Or) <*> be2)
      return $ foldl' (\e1 (op, e2) -> EBOp op e1 e2) x rest

parseVar :: MonadParsec e Text m => m Var
parseVar = lexeme $ takeWhile1P (Just "identifier") isLower

parseStmt :: MonadParsec e Text m => m Stmt
parseStmt = do
  stmts <- parseStmt1 `sepBy1` symbol ";"
  return $ foldl1' Seq stmts

parseStmt1 :: MonadParsec e Text m => m Stmt
parseStmt1 =
  asum
    [ do
        void $ symbol "while"
        b <- parens parseBExpr
        void $ symbol "do"
        s <- braces parseStmt
        return $ While b s,
      do
        void $ symbol "if"
        b <- parens parseBExpr
        void $ symbol "then"
        s1 <- braces parseStmt
        void $ symbol "else"
        s2 <- braces parseStmt
        return $ If b s1 s2,
      do
        x <- parseVar
        void $ symbol ":="
        Assign x <$> parseAExpr
    ]

test1 :: IO ()
test1 = do
  t <- T.readFile "sample1.wh"
  let p = mySpace *> parseStmt <* eof :: Parsec String Text Stmt
      res = runParser p "sample1.wh" t
  case res of
    Left e -> print e
    Right s -> print (execute s M.empty)

test2 :: IO ()
test2 = do
  t <- T.readFile "sample2.wh"
  let p = mySpace *> parseStmt <* eof :: Parsec String Text Stmt
      res = runParser p "sample2.wh" t
  case res of
    Left e -> print e
    Right s -> print (execute s M.empty)

---

-- execute statement?

type State = M.Map Var Int

evaluate :: State -> Expr t -> Either String t
evaluate s e = case e of
  EILit x -> pure x
  EVar v -> maybe (Left "variable not in scope") pure (M.lookup v s)
  EAOp op e1 e2 -> do
    x1 <- evaluate s e1
    x2 <- evaluate s e2
    return $ aop op x1 x2
  EBLit x -> pure x
  EBOp op e1 e2 -> do
    x1 <- evaluate s e1
    x2 <- evaluate s e2
    return $ bop op x1 x2
  EROp op e1 e2 -> do
    x1 <- evaluate s e1
    x2 <- evaluate s e2
    return $ rop op x1 x2

aop :: AOp -> Int -> Int -> Int
aop Plus = (+)
aop Minus = (-)
aop Times = (*)
aop Div = div

bop :: BOp -> Bool -> Bool -> Bool
bop And = (&&)
bop Or = (||)

rop :: ROp -> Int -> Int -> Bool
rop Lt = (<)
rop Gt = (>)

execute :: Stmt -> State -> Either String State
execute (Assign v e) state = do
  x <- evaluate state e
  pure $ M.insert v x state
execute (Seq s1 s2) state = execute s1 state >>= execute s2
execute w@(While eb s) state = do
  x <- evaluate state eb
  if x
    then execute s state >>= execute w
    else pure state
execute (If eb s1 s2) state = do
  x <- evaluate state eb
  if x then execute s1 state else execute s2 state

main :: IO ()
main = do
  t <- T.hGetContents stdin
  let p = mySpace *> parseStmt <* eof :: Parsec String Text Stmt
      res = runParser p "<stdin>" t
  Right s <- pure res
  Right state <- pure $ execute s M.empty
  forM_ (M.toAscList state) $ \(v, x) -> do
    putStrLn $ unpack v ++ " " ++ show x
