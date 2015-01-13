module Main where

import System.Environment
import Control.Monad.Trans.State

----------------------
-- Formula occurrences
-- Syntactic categories of LG: Atoms, Lambek connectives (product, left & right
-- division), and Grishin connectives (coproduct, left & right difference)

type Identifier   = Integer
data Occurrence a = Identifier :@ a deriving (Eq, Show)

data Formula= N | NP | S
            | Formula :<×> Formula | Formula :\   Formula | Formula :/   Formula
            | Formula :<+> Formula | Formula :<\> Formula | Formula :</> Formula
            deriving (Eq, Show)

atomary :: Formula -> Bool
atomary c = c == N || c == NP || c == S

abstract :: Occurrence a -> a
abstract (_ :@ x) = x

--------
-- Links

data Link v = [(v, Link v)] :●: [(v, Link v)]  -- Cotensor
            | [(v, Link v)] :○: [(v, Link v)]  -- Tensor
            | Top (v, Link v)                  -- Hypothesis
            | Bot (v, Link v) deriving (Eq)    -- Conclusion

up, down :: Link v -> [(v, Link v)]
up   (xs :●: _) = xs
up   (xs :○: _) = xs
up   (Top _)    = []
up   (Bot x)    = [x]
down (_ :●: xs) = xs
down (_ :○: xs) = xs
down (Top x)    = [x]
down (Bot _)    = []

hypotheses, conclusions, labels :: Link v -> [v]
hypotheses  = map fst . up
conclusions = map fst . down
labels link = hypotheses link ++ conclusions link

predecessors, successors, adjacent :: Link v -> [Link v]
predecessors  = map snd . up
successors    = map snd . down
adjacent link = predecessors link ++ successors link

contains :: (Eq v) => v -> Link v -> Bool
contains v link = v `elem` labels link

------------------
-- Proof structure
--
-- A proof structure is fully defined by its links and leaves
-- Each formula occurrence must occur twice in this representation

type ProofContext = State ProofStructure
data ProofStructure = PrfStr { unusedID :: [Integer]
                             , links :: [Link (Occurrence Formula)] }

initial :: [Formula] -> ProofStructure
initial = f [0..] where f id []     = PrfStr id []
                        f id (x:xs) = let t = Top (i :@ x, b)
                                          b = Bot (i :@ x, t)
                                          PrfStr (i:id') xs' = f id xs
                                      in  PrfStr id' (t:b:xs')

------------
-- Unfolding

-- Was planning on generalising this but there's definitely better ways

unfoldable :: Link (Occurrence Formula) -> Bool
unfoldable (Bot (_:@f,_)) = atomary f
unfoldable (Top (_:@f,_)) = atomary f
unfoldable _ = False

-- Hypothesis unfolding (L)
unfold' j k (Bot main@((_:@formula),_)) =
  let top f@(_:@_) = (f, Top (f, this))
      bot f@(_:@_) = (f, Bot (f, this))
      this = case formula of
        a :/   b -> [main, top (j:@b)] :○: [bot (k:@a)]
        a :<×> b ->             [main] :●: [bot (j:@a), bot (k:@b)]
        a :\   b -> [top (j:@b), main] :○: [bot (k:@a)]
        a :</> b -> [main, top (j:@b)] :●: [bot (k:@a)]
        a :<+> b -> [main]             :○: [bot (j:@a), top (k:@b)]
        a :<\> b -> [top (j:@b), main] :●: [top (k:@a)]
  in up this ++ down this

-- Conclusion unfolding (R)
unfold' j k (Top main@((_:@formula),_)) =
  let top f@(_:@_) = (f, Top (f, this))
      bot f@(_:@_) = (f, Bot (f, this))
      this = case formula of
        a :/   b -> [top (j:@a)]             :●: [main, bot (k:@b)]
        a :<×> b -> [top (j:@a), top (k:@b)] :○: [main]
        a :\   b -> [top (j:@a)]             :●: [bot (k:@b), main]
        a :</> b -> [top (j:@a)]             :○: [main, bot (k:@b)]
        a :<+> b -> [top (j:@a), top (k:@b)] :●: [main]
        a :<\> b -> [top (j:@a)]             :○: [top (k:@b), main]
  in up this ++ down this


----------

instance Show v => Show (Link v) where
  show l@(_ :●: _)    = " (" ++ (show $ hypotheses l) ++ "●" ++ (show $ conclusions l) ++ ") "
  show l@(_ :○: _)    = " (" ++ (show $ hypotheses l) ++ "○" ++ (show $ conclusions l) ++ ") "
  show (Top (v,_))    = " ⌈" ++ show v ++ "⌉ "
  show (Bot (v,_)) = " ⌊" ++ show v ++ "⌋ "

instance Show ProofStructure where
  show (PrfStr _ l) = show l

test :: ProofContext ProofStructure
test = do return $ initial [N :<×> (N :\ NP)]

main :: IO ()
main = do args <- getArgs
          putStrLn $ show a
    where a = initial [N, N :<×> (N :\ NP)]
