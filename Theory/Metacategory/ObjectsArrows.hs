{- Given a count of objects in a category, such that for every object at index
   n : ℕ there is an arrow to it from every other object { m : ℕ | m < n },
   compute all the possible compositions of arrows in that category.

   Note that this is sufficient to describe an "arrows only" definition of the
   category, since the existence of "objects" is indicated by their identity
   morphisms, and domain and codomain of morphisms by how they compose with
   those identities. -}

module Main where

import Data.Bits
import Data.List
import System.Environment (getArgs)

-- 'step' folds over numbers, not including the starting number. So, for n =
-- 3, 'f' is called with [2,1,0], in that order.
step :: (Int -> a -> a) -> a -> Int -> a
step f z = go
  where
    go 0 = z
    go i = let j = i - 1 in f j (go j)
{-# INLINE step #-}

triangularNumber :: Int -> Int
triangularNumber n = shiftR (n * (n + 1)) 1
{-# INLINE triangularNumber #-}

composablePairsStep :: Int -> [((Int, Int), Int)]
composablePairsStep n = step go [] n
  where
    next = triangularNumber (n - 1)

    go i rest = step ((:) . k) rest (n - i)
      where
        k j = let mor = next + i
                  dom = triangularNumber (j + i) + i
                  cod = mor + j in ((cod, dom), mor)

composablePairs :: Int -> [((Int, Int), Int)]
composablePairs = step (\j rest -> composablePairsStep (j + 1) ++ rest) []

-- The number of composable pairs for a category of N objects as described
-- above is given by its tetrahedral number:
-- https://en.wikipedia.org/wiki/Tetrahedral_number

tetrahedralNumber :: Int -> Int
tetrahedralNumber n = (n * (n + 1) * (n + 2)) `div` 6

prop_composablePairs_len :: Int -> Bool
prop_composablePairs_len n = length (composablePairs n) == tetrahedralNumber n

coqSyntax :: String -> [((Int, Int), Int)] -> String
coqSyntax name pairs = concat
    [ "Program Definition " ++ name ++ " : Metacategory := {|\n"
    , "  pairs := [map "
    , intercalate "\n           ;    " (map render pairs)
    , " ]%N\n"
    , "|}."
    ]
  where
    render ((y, x), f) = "(" ++ show y ++ ", " ++ show x ++ ") +=> " ++ show f

main :: IO ()
main = do
    cmd:args <- getArgs
    case cmd of
        "length" -> case args of
            n:_ -> print $ length (composablePairs (read n :: Int))
            _ -> error "Bad arguments to length"

        "define" -> case args of
            name:n:_ ->
                putStrLn $ coqSyntax name (composablePairs (read n :: Int))
            _ -> error "Bad arguments to define"

        _ -> error "Unknown command!"
