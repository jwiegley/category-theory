module Main where

import Data.List
import System.Environment (getArgs)

-- Given a count of objects in a category, such that for every object at index
-- n : ℕ there is an arrow to it from every other object { m : ℕ | m < n },
-- compute all the possible compositions of arrows in that category.
--
-- Note that this is sufficient to describe an "arrows only" definition of the
-- category, since the existence of "objects" is indicated by their identity
-- morphisms, and domain and codomain of morphisms by how they compose with
-- those identities.

triangularNumber :: Int -> Int
triangularNumber n = (n * (n + 1)) `div` 2

composablePairsStep :: Int -> [((Int, Int), Int)]
composablePairsStep n = go n
  where
    next = triangularNumber (n - 1)

    go 0 = []
    go j' = go' (n - j)
      where
        j = j' - 1
        f = next + j

        go' 0 = go j
        go' i' = ((f + i, triangularNumber (i + j) + j), f) : go' i
          where i = i' - 1

composablePairs :: Int -> [((Int, Int), Int)]
composablePairs 0 = []
composablePairs j =
    composablePairs (j - 1) ++ composablePairsStep j

arrowCount :: Int -> Integer
arrowCount 0 = 0
arrowCount n = fromIntegral n^(2 :: Integer) + arrowCount (n - 1)

-- The number of composable pairs for a category of N objects as described
-- above is given by its tetrahedral number:
-- https://en.wikipedia.org/wiki/Tetrahedral_number

tetrahedralNumber :: Int -> Int
tetrahedralNumber n = (n * (n + 1) * (n + 2)) `div` 6

prop_composablePairs_length :: Int -> Bool
prop_composablePairs_length n =
    length (composablePairs n) == tetrahedralNumber n

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
