module LG.Reductions where

import LG.Base
import LG.Graph
import qualified Data.Map as Map
import Data.List
import Data.Maybe


-- Proof net transformations as in Moortgat & Moot 2012, pp 9-10

data ProofTransformation = [Link] :⤳ [Link]
contraction              = (:⤳ [])
interaction              = ([[ Active 1, Active 2 ] :○: [ Active 0 ],
                             [ Active 0 ] :○: [ Active 3, Active 4 ]] :⤳)

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

rules = [(rdivR,   "R/"), (prodL, "L<×>"), (ldivR,   "R\\"),
         (rdifL, "L</>"), (cprdR, "R<+>"), (ldifL, "L<\\>"),
         (g1, "associativity G1"), (g3, "associativity G3"),
         (g2, "commutativity G2"), (g4, "commutativity G4")]


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
  apply u x   = maybe x id $ lookup x u
  unify x y u = case lookup x u of
    Nothing -> Just ((x, y) : u)
    Just y' -> if y == y' then Just u else Nothing

instance Unifiable a => Unifiable [a] where
  apply                 = fmap . apply
  unify (x:xs) (y:ys) u = unify x y u >>= unify xs ys
  unify []     []     u = Just u
  unify _      _      _ = Nothing

instance Unifiable a => Unifiable (Maybe a) where
  apply                     = fmap . apply
  unify (Just x) (Just y) u = unify x y u
  unify Nothing  Nothing  u = Just u
  unify _        _        _ = Nothing

instance Unifiable a => Unifiable (Occurrence a) where
  apply u (k :@ x)          = k :@ apply u x
  unify (k :@ x) (i :@ y) u | k == i    = unify x y u
                            | otherwise = Nothing

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


-- An inefficient but convenient way to substitute y by x in z, by exploiting
-- the way unifications work
subst :: Unifiable a => Identifier -> Identifier -> a -> a
subst x y z = flip apply z $ map sub' $ fromJust $ unify' z z where
  sub' (k,v) |   k==y    = (k,x)
             | otherwise = (k,v)


-- Give all possible unifications for some set of links such that all the links
-- occur in the given graph in conjunction.
-- To find the unifications of the first link, we simply try to unify with all
-- links. When we have the first set of (tentatively) possible unifications, we
-- expand (or shrink) this set nondeterministically by attempting to unify all
-- neighbour links (that is, all links that are connected to nodes that we've
-- seen before). Note that this requires each next link to be in some way
-- connected to one that came before! Although laziness helps us a lot here,
-- this could be done more efficiently by already doing it at the individual
-- link unification stage, but the code would be much uglier, and we never have
-- big subgraphs anyway.
partialUnify :: [Link] -> CompositionGraph -> [Unification]
partialUnify []       _ = []
partialUnify (l1:ls1) g = firsts l1 >>= rest ls1 where
  firsts l      = mapMaybe (unify' l) (links g)
  rest []     u = [u]
  rest (l:ls) u = let nodes    = map snd u
                      all' ref = mapMaybe (ref . (g Map.!))
                      options  = all' premiseOf nodes ++ all' succedentOf nodes
                  in  mapMaybe (\l' -> unify l l' u) options >>= rest ls


--------------------------------------------------------------------------------
-- Net manipulation

-- Identify 'lost' hypotheses and conclusions with eachother. We assume that the
-- 'hypotheses' in the first list are not actually the premise of any link
-- anymore, and that the 'conclusions' are not the succedent of any link.
reunite :: [Identifier] -> [Identifier] -> CompositionGraph -> CompositionGraph
reunite []  []  g = g
reunite [h] [c] g = Map.delete h . Map.adjust (l⤴) c
                  . adjust (l⤵) upstream . adjust (l⤴) neighbour $ g
  where l         = subst c h $ uplink h g
        upstream  = maybe [] prem l
        neighbour = maybe [] conc l
reunite _ _ _     = error "Cannot reconnect multiple disconnected hypotheses\
      \and conclusions. Make sure that the proof transformations are sensible."


-- Collapse axiom links so that the composition graph may be interpreted as a
-- proof net directly. It is still represented as a compositiongraph because it
-- holds all the necessary information, but the semantics don't correspond any-
-- more. Perhaps change the data type?
asProofnet :: CompositionGraph -> CompositionGraph
asProofnet = let collapseAxiom = [ Active 0  :|:  Active 1 ] :⤳ []
             in  loop (listToMaybe . step [collapseAxiom])


-- Get all the instances of a proof transformation rule (that is, the
-- transformations with identifiers that correspond to those in the graph) that
-- can be applied to a graph
instancesIn :: CompositionGraph -> ProofTransformation -> [ProofTransformation]
instancesIn graph r@(old :⤳ _) = map (flip apply r) (partialUnify old graph)


-- Get the proof net that results when applying some proof transformation to a
-- graph. The proof transformation must be instantiated with identifiers as they
-- occur in the graph.
transform :: CompositionGraph -> ProofTransformation -> CompositionGraph
transform graph (old :⤳ new) =
  let (oldHypotheses, oldInterior, oldConclusions) = sift old
      (newHypotheses, newInterior, newConclusions) = sift new
      orphans = oldInterior  \\ newInterior
      widower = oldHypotheses \\ newHypotheses
      widow   = oldConclusions \\ newConclusions
  in reunite widower widow $ kill orphans $ connect new $ disconnect old graph


-- Get all possible proof nets after performing (one of) the generic
-- transformations given
step :: [ProofTransformation] -> CompositionGraph -> [CompositionGraph]
step transformations graph =
  let possibilities = concatMap (instancesIn graph) transformations
  in  map (transform graph) possibilities


-- Get all possible proof nets, keep track of rule application history (inverse)
stepTrace :: [(ProofTransformation, String)] -> (CompositionGraph, [String])
          -> [(CompositionGraph, [String])]
stepTrace transformations (graph, history) =
  let results      = map (transform graph) . instancesIn graph
      try (t, log) = zip (results t) $ zipWith counter [1..] (repeat log)
      counter i s  = (:history) $ (s ++ " (" ++ show i ++ ")")
  in  concatMap try transformations


-- Is the composition graph a valid proof net?
valid :: CompositionGraph -> Bool
valid = isTree . loop greedy . asProofnet where
  greedy = listToMaybe . step (map fst rules)


-- Looping. The code is already clearer than any explanation can be
loop :: (a -> Maybe a) -> a -> a
loop f start = case f start of
  Just next -> loop f next
  Nothing   -> start


-- Looping while keeping a list of intermediate results
loopTrace :: (a -> Maybe a) -> a -> [a]
loopTrace f start = (start : case f start of
  Just next -> loopTrace f next
  Nothing   -> [])

{-
-- Nondeterministic looping while keeping a trace of intermediate results
-- Earlier results are at the back of the list
loopNondeterministic :: (a -> [a]) -> a -> [[a]]
loopNondeterministic f start = concatMap (loopND f) [[start]] where
  loopND f (prev:history) = map (++ history) $ f prev --uh
-}

{-

-}
