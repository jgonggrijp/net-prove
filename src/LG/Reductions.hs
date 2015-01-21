module LG.Reductions where

import LG.Graph
import qualified Data.Map as Map
import Data.List
import Data.Maybe


-- Proof net transformations as in Moortgat & Moot 2012, pp 9-10

data ProofTransformation = [Link] :⤳ [Link]
contraction              = (:⤳ [])
interaction              = ([[ Active 1, Active 2 ] :○: [ Active 0 ],
                             [ Active 0 ] :○: [ Active 3, Active 4 ]] :⤳)

contractions = [ rdivR, prodL, ldivR, rdifL, cprdR, ldifL ]
interactions = [ g1, g3, g2, g4 ]

rdivR = contraction [[ Active 1, Active 2 ] :○: [ Active 3 ], -- R/
                     [ Active 3 ] :●: [ MainT  4, Active 2 ]]

prodL = contraction [[ MainT  1 ] :●: [ Active 2, Active 3 ], -- L<×>
                     [ Active 2, Active 3 ] :○: [ Active 4 ]]

ldivR = contraction [[ Active 2, Active 1 ] :○: [ Active 3 ], -- R\
                     [ Active 3 ] :●: [ Active 2, MainT  4 ]]

rdifL = contraction [[ MainT  1, Active 2 ] :●: [ Active 3 ], -- L</>
                     [ Active 3 ] :○: [ Active 4, Active 2 ]]

cprdR = contraction [[ Active 1 ] :○: [ Active 2, Active 3 ], -- R<+>
                     [ Active 2, Active 3 ] :●: [ MainT  4 ]]

ldifL = contraction [[ Active 2, MainT  1 ] :●: [ Active 3 ], -- L<\>
                     [ Active 3 ] :○: [ Active 2, Active 4 ]]

g1    = interaction [[ Active 1 ] :○: [ Active 3, Active 0 ], -- Associativity
                     [ Active 0, Active 2 ] :○: [ Active 4 ]]

g3    = interaction [[ Active 1, Active 0 ] :○: [ Active 3 ], -- Associativity
                     [ Active 2 ] :○: [ Active 0, Active 4 ]]

g2    = interaction [[ Active 1 ] :○: [ Active 0, Active 4 ], -- Commutativity
                     [ Active 0, Active 2 ] :○: [ Active 3 ]]

g4    = interaction [[ Active 2 ] :○: [ Active 3, Active 0 ], -- Commutativity
                     [ Active 1, Active 0 ] :○: [ Active 4 ]]


--------------------------------------------------------------------------------
-- Eliminate axiom links so that the composition graph may be interpreted as a
-- proof structure. (Note that this also deletes any unconnected subgraph
-- consisting of no links or only axiom links!)
-- After this, the formula and term parts become meaningless

reduce :: CompositionGraph -> CompositionGraph
reduce = Map.mapMaybe (\(Node f t p s) -> case (del p, del s) of
  (Nothing, Nothing) -> Nothing
  (p', s')           -> Just $ Node f t p' s')
  where del (Just (_ :|: _)) = Nothing
        del other            = other


--------------------------------------------------------------------------------
-- An instance of the unifiable class represents an object that can be wholly
-- unified with another object of the same type, while respecting and updating
-- previous unifications. We also keep track of identifiers that occur once
-- (fst) and those that occur more often (snd).
-- Note that [x,y] unifies with [z,z], but [z,z] does not unify with [x,y].

type  Unification = ([(Identifier, Identifier)], [(Identifier, Identifier)])
class Unifiable a where
  unify  :: a -> a -> Unification -> Maybe Unification
  unify' :: a -> a -> Maybe Unification
  unify' x y = unify x y ([],[])

instance Unifiable Int where
  unify x y (seen1x, seen) = case lookup x seen of
    Nothing -> Just ((x,y):seen1x, (x,y):seen)
    Just y' -> if y == y'
               then Just (Data.List.delete (x,y) seen1x, seen)
               else Nothing

instance Unifiable a => Unifiable [a] where
  unify (x:xs) (y:ys) u = unify x y u >>= unify xs ys
  unify []     []     u = Just u
  unify _      _      _ = Nothing

instance Unifiable Tentacle where
  unify (MainT  x) (MainT  y) u = unify x y u
  unify (Active x) (Active y) u = unify x y u
  unify _          _          _ = Nothing

instance Unifiable Link where
  unify l1 l2 u = case (l1, l2) of
    ((p1 :○: s1), (p2 :○: s2)) -> unify s1 s2 u >>= unify p1 p2
    ((p1 :●: s1), (p2 :●: s2)) -> unify s1 s2 u >>= unify p1 p2
    ((p1 :|: s1), (p2 :|: s2)) -> unify s1 s2 u >>= unify p1 p2
    _                          -> Nothing

-- Give all possible unifications for some set of links such that the links
-- occur in the given graph.
partialUnify :: [Link] -> CompositionGraph -> [Unification]
partialUnify []     _ = []
partialUnify (l1:ls1) g = firsts l1 >>= rest ls1 where
-- To find the unifications of the first link, we simply try to unify with all
-- links. This assumes that all links have at least one tentacle leading up.
  firsts link = Map.elems $ Map.mapMaybe (\n -> succedentOf n >>= unify' link) g
-- When we have the first set of (tentatively) possible unifications, we expand
-- (or shrink) this set nondeterministically by attempting to unify at least all
-- 'outer' links (that is, at least all the links that are either a premise or a
-- succedent of nodes that we've only seen once). Because of this, each next
-- link must be in some way connected to one that came before!
-- Although laziness helps us a lot here, this could be done more efficiently by
-- already doing it at the individual link unification stage, but the code
-- would be much uglier, and we never have big subgraphs anyway.
  rest []     u             = [u]
  rest (l:ls) u@(seen1x, _) = let outerNodes   = map snd seen1x
                                  all' getLink = mapMaybe (getLink . (g Map.!))
                                  nearLinks    = all' succedentOf outerNodes ++
                                                 all' premiseOf   outerNodes
                              in  mapMaybe (\l' -> unify l l' u) nearLinks
                                  >>= rest ls
