module Main where

import           Witnesses

import qualified Data.Map                      as M
import           Text.Show.Pretty               ( ppShow )
import           Control.Monad                  ( unless )

main :: IO ()
main =
    case
            generateWitnesses
                [ Subtype Nat (UniVar "u0")
                , Subtype (UniVar "u0") (Inter Int' Top)
                , Subtype Nat (Inter Top Top)
                , Subtype Nat (Inter (Inter Top Nat) Int')
                , Subtype (Union Int' (Union Nat Bot)) Int'
                , Subtype (FuncTy (Inter Top Int') Nat) (FuncTy Nat Int')
                , Subtype (RecTy "a" (FuncTy Nat (RecVar "a"))) (FuncTy Nat (RecTy "a" (FuncTy Nat (RecVar "a"))))
                ]
        of
            Left  err -> error err
            Right sol -> do
                putStrLn $ ppShow sol
                let test = and $ M.elems $ M.mapWithKey (\k val -> reconstruct val == k) sol
                putStrLn $ "Reconstruction correct: " ++ show test
                unless test $ do
                  let failures = M.filterWithKey (\k val -> reconstruct val == k) sol
                  putStrLn $ "Reconstruction: " ++ ppShow failures
