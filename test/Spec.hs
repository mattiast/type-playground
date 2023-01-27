{-# LANGUAGE OverloadedStrings #-}
import qualified Infer as I
import Test.QuickCheck (quickCheckResult, Result (Success))

main :: IO ()
main = do
    Right e <- return $ I.myParse "fun f -> let x = fun g y -> let _ = g(y) in eq(f, g) in x"
    Just t <- return $ I.infer I.myEnv e
    let c1 = I.renderScheme (I.generalizeWithABC t) == "forall[a b] (a -> b) -> (a -> b, a) -> bool"
    Success {} <- quickCheckResult c1
    putStrLn "Test suite done"


