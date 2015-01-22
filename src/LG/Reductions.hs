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
-- Collapse axiom links so that the composition graph may be interpreted as a
-- proof net.
-- After this, the formula and term parts become meaningless (?)

reduce :: CompositionGraph -> CompositionGraph
reduce = Map.mapMaybe adjust where
  adjust (Node f t Nothing (Just (_ :|: _))) = Nothing
  adjust (Node f t (Just (_ :|: _)) Nothing) = Nothing
  adjust (Node f t s                p)       = Just $ Node f t (del s) (del p)
  del (Just (_ :|: _))                       = Nothing
  del other                                  = other


--------------------------------------------------------------------------------
-- An instance of the unifiable class represents an object that can be wholly
-- unified with another object of the same type, while respecting and updating
-- previous unifications.
-- Note that [x,y] unifies with [z,z], but [z,z] does not unify with [x,y].

type  Unification = [(Identifier, Identifier)]
class Unifiable a where
  apply  :: Unification -> a -> a
  unify  :: a -> a -> Unification -> Maybe Unification
  unify' :: a -> a -> Maybe Unification
  unify' x y = unify x y []

instance Unifiable Int where
  apply u x   = fromJust $ lookup x u -- throws error if there is any identifier
  unify x y u = case lookup x u of -- without translation. substitute wouldn't.
    Nothing -> Just ((x, y) : u)
    Just y' -> if y == y' then Just u else Nothing

instance Unifiable a => Unifiable [a] where
  apply                 = fmap . apply
  unify (x:xs) (y:ys) u = unify x y u >>= unify xs ys
  unify []     []     u = Just u
  unify _      _      _ = Nothing

instance Unifiable Tentacle where
  apply u (MainT  x)          = MainT  $ apply u x
  apply u (Active x)          = Active $ apply u x
  unify (MainT  x) (MainT  y) = unify x y
  unify (Active x) (Active y) = unify x y
  unify _          _          = const Nothing

instance Unifiable Link where
  apply u (p :○: s) = apply u p :○: apply u s
  apply u (p :●: s) = apply u p :●: apply u s
  apply u (p :|: s) = apply u p :|: apply u s
  unify l1 l2 u     = case (l1, l2) of
    ((p1 :○: s1), (p2 :○: s2)) -> unify s1 s2 u >>= unify p1 p2
    ((p1 :●: s1), (p2 :●: s2)) -> unify s1 s2 u >>= unify p1 p2
    ((p1 :|: s1), (p2 :|: s2)) -> unify s1 s2 u >>= unify p1 p2
    _                          -> Nothing

instance Unifiable ProofTransformation where
  apply u (p :⤳ s) = apply u p :⤳ apply u s
  unify (p1 :⤳ s1) (p2 :⤳ s2) u = unify s1 s2 u >>= unify p1 p2


-- Give all possible unifications for some set of links such that all the links
-- occur in the given graph in conjunction.
-- To find the unifications of the first link, we simply try to unify with all
-- links. This assumes that all links have at least one tentacle leading up.
-- When we have the first set of (tentatively) possible unifications, we expand
-- (or shrink) this set nondeterministically by attempting to unify all
-- neighbour links (that is, all links that are connected to nodes that we've
-- seen before). Note that this requires each next link to be in some way
-- connected to one that came before! Although laziness helps us a lot here,
-- this could be done more efficiently by already doing it at the individual
-- link unification stage, but the code would be much uglier, and we never have
-- big subgraphs anyway.
partialUnify :: [Link] -> CompositionGraph -> [Unification]
partialUnify []       _ = []
partialUnify (l1:ls1) g = firsts l1 >>= rest ls1 where
  firsts link = Map.elems $ Map.mapMaybe (\n -> premiseOf n >>= unify' link) g
  rest []     u = [u]
  rest (l:ls) u = let nodes = map snd u
                      all' ref = mapMaybe (ref . (g Map.!))
                      links = all' premiseOf nodes ++ all' succedentOf nodes
                  in  mapMaybe (\l' -> unify l l' u) links >>= rest ls


--------------------------------------------------------------------------------
-- Once we have a transformation rule and a way to unify it with the graph
-- structure, we can start actually changing the graph

-- Remove/add the succedentOf/premiseOf link references to the nodes of a graph
connect, disconnect :: CompositionGraph -> [Link] -> CompositionGraph
connect    = foldl' (update $ Just)
disconnect = foldl' (update $ const Nothing)

-- Update all references to some (hypothetical) link that may exist to in the
-- nodes of a graph to refer to some other link (or its absence)
update :: (Link -> Maybe Link) -> CompositionGraph -> Link -> CompositionGraph
update r graph link = update' graph (premises link) (succedents link) where
  updatePremise   (Node f t p s) = Node f t (r link) s
  updateSuccedent (Node f t p s) = Node f t p (r link)
  update' g' (k:ks) s = update' (Map.adjust updatePremise   k g') ks s
  update' g' p (k:ks) = update' (Map.adjust updateSuccedent k g') p ks
  update' g' _      _ = g'


-- Get all the instances of a proof transformation rule (that is, the
-- transformations with identifiers that correspond to those in the graph) that
-- can be applied to a graph
ruleInstances :: CompositionGraph -> ProofTransformation -> [ProofTransformation]
ruleInstances g r@(p :⤳ _) = map (flip apply r) (partialUnify p g)


-- Partition the nodes of a set of links into those at the hypothesis end, those
-- 'inside' the links structure and those at the conclusion end, respectively
sift :: [Link] -> ([Identifier], [Identifier], [Identifier])
sift links = (p \\ s, p `intersect` s, s \\ p)
  where all' = flip concatMap links
        p    = all' premises
        s    = all' succedents


-- Transform the graph given an instance (!) of a proof transformation that we
-- assume to be valid (!)
transformInstance :: CompositionGraph -> ProofTransformation -> CompositionGraph
transformInstance g (p :⤳ s) = let g1  = disconnect g p
                                   g2 = g1 -- We need a way to deal with orphaned links...
                                   g3 = connect g2 s --also a way to deal with [] conclusions
                               in g3


-- What nodes are orphaned after a transformation and should be deleted?
-- What nodes were disconnected during a transformation and should be combined?
updates :: ProofTransformation -> [Identifier]
updates (old :⤳ new) =
  let (oldHypotheses, oldInterior, oldConclusions) = sift old
      (newHypotheses, newInterior, newConclusions) = sift new
      orphans = oldInterior \\ (newHypotheses ++ newInterior ++ newConclusions)
      divorceeH = oldHypotheses \\ newHypotheses
      divorceeC = oldConclusions \\ newConclusions
  in  orphans
