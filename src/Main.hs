module Main where

import           Witnesses

import qualified Data.Map                      as M
import           Text.Show.Pretty               ( ppShow )

main :: IO ()
main =
    case
            generateWitnesses
                [ Subtype Bot Top
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
                let test = M.mapWithKey (\k val -> reconstruct val == k) sol
                putStrLn $ "Sanity test: " ++ ppShow test
                putStrLn $ "All true? " ++ show (and $ M.elems test)
