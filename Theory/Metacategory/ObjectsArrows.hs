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

makeArrows :: Int -> [((Int, Int), Int)]
makeArrows = fst . go
  where
    go 0 = ([], 0)
    go n =
        let (xs, this) = go (pred n)

            -- First, the "identity arrow" to represent this object.
            id'  = ((this, this), this)

            -- Find all the previous identity arrows
            ids  = [ f | ((x, y), f) <- xs, x == y ]

            -- For each previous identity arrow, add a morphism from it to the
            -- new identity arrow.
            ys   = concat [ [ ((f, x), f), ((this, f), f) ]
                          | (x, f) <- zip ids [succ this..] ]

            zs = xs ++ id' : ys
            next = this + length ys `div` 2 in

        (zs ++ composable this zs, succ next)

    -- Taking all known compositions into account, should there exist more?
    -- For example, considering object 4, if we have ((2,0),2), ((1,2),2),
    -- ((6,1),6), ((4,6),6), ((4,0),4), and ((4,4),4), then we should also
    -- have the composite ((6,2),4).

    composable this fs =
        [ ((f, g), succ this)
        | (((fcod, fdom), f), ((gcod, gdom), g)) <- [ (f, g) | f <- fs, g <- fs ]
        , gcod == fdom
        , gdom == g
        , gcod /= g
        , fcod == f
        , fdom /= f
        , ((g, 0), g) `elem` fs
        , ((this, f), f) `elem` fs
        ]

arrowCount :: Int -> Integer
arrowCount 0 = 0
arrowCount n = fromIntegral n^(2 :: Integer) + arrowCount (pred n)

-- The number of composable pairs for a category of N objects as described
-- above is given by the centered triangular number:
-- https://en.wikipedia.org/wiki/Centered_triangular_number

prop_makeArrows_length :: Int -> Bool
prop_makeArrows_length n =
    length (makeArrows (n + 1)) == (3 * (n^(2 :: Integer)) + 3 * n + 2) `div` 2

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
