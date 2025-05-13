{-# LANGUAGE OverloadedStrings #-}

import Infer qualified as I
import Test.QuickCheck (Result (Success), quickCheckResult)
import Control.Monad (forM_)
import Data.ByteString (ByteString)

main :: IO ()
main = do
  forM_ test_cases $ \(input, expected) -> do
    Right e <- return $ I.myParse input
    Just t <- return $ I.infer I.myEnv e
    let c1 = I.renderScheme (I.generalizeWithABC t) == expected
    Success {} <- quickCheckResult c1
    pure ()
  putStrLn "Test suite done"

test_cases :: [(ByteString, String)]
test_cases =
  [ ("fun x -> let y = fun z -> z in y(y)", "forall[a b] a -> b -> b"),
    ("fun f -> let x = fun g y -> let _ = g(y) in eq(f, g) in x", "forall[a b] (a -> b) -> (a -> b, a) -> bool")
  ]