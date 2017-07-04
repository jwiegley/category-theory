module Main where

import Data.List
import Data.Foldable
import Debug.Trace
import System.Environment (getArgs)

-- jww (2017-07-03): This code is wrong. It generates a correct definition for
-- 3 objects, but fails for 4.

-- Given a count of objects in a category, such that for every object at index
-- n : ℕ there is an arrow to it from every other object { m : ℕ | m < n },
-- compute all the possible compositions of arrows in that category.
--
-- Note that this is sufficient to describe an "arrows only" definition of the
-- category, since the existence of "objects" is indicated by their identity
-- morphisms, and domain and codomain of morphisms by how they compose with
-- those identities.

makeArrows :: Int -> [((Int, Int), Int)]
makeArrows = fst . go
  where
    go 0 = ([], (0, []))
    go n =
        let (xs, (this, ids)) = go (n - 1)
            (_, next, ys) = foldr' (k this) ([], this + 1, []) ids in
        (xs ++ ((this, this), this) : ys, (next, this:ids))

    k this x (res, f, rest) =
        (x:res, f + 1,
         ((this, f), f) : ((f, x), f)
             : fst (foldr' (\_ (xs, (i, g)) -> (((f, i), g) : xs, (i + 1, g + 1)))
                           (rest, (x + 1, this + 1)) res))

arrowCount :: Int -> Integer
arrowCount 0 = 0
arrowCount n = fromIntegral n^(2 :: Integer) + arrowCount (n - 1)

-- The number of composable pairs for a category of N objects as described
-- above is given by its tetrahedral number:
-- https://en.wikipedia.org/wiki/Tetrahedral_number

prop_makeArrows_length :: Int -> Bool
prop_makeArrows_length n =
    length (makeArrows n) == (n * (n + 1) * (n + 2)) `div` 6

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
            n:_ -> print (length (makeArrows (read n :: Int)))
            _ -> error "Bad arguments to length"
        "define" -> case args of
            name:n:_ -> putStrLn (coqSyntax name (makeArrows (read n :: Int)))
            _ -> error "Bad arguments to define"
        _ -> error "Unknown command!"
