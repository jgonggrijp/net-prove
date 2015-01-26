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

instance Unifiable a => Unifiable (Maybe a) where
  apply u (Just x) = Just $ apply u x
  unify (Just x) (Just y) u = unify x y u
  unify Nothing  Nothing  u = Just u
  unify _        _        _ = Nothing


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
-- Net information


-- Get all links inside a graph by enumerating all links under each node that is
-- the first premise of a link. Assumes that all links have at least one
-- tentacle leading up!
links :: CompositionGraph -> [Link]
links = Map.elems . Map.mapMaybeWithKey spotByRepresentative where
  first                    = fmap (head . premises) . premiseOf
  spotByRepresentative k n = if first n == Just k then premiseOf n else Nothing


-- Find out to what link some node is a premise (downlink) / succedent (uplink)
downlink, uplink :: Identifier -> CompositionGraph -> Maybe Link
downlink k g = premiseOf   $ g Map.! k
uplink   k g = succedentOf $ g Map.! k


--------------------------------------------------------------------------------
-- Net manipulation

-- Delete all given nodes from a graph. Mind any other refs!
kill :: [Identifier] -> CompositionGraph -> CompositionGraph
kill = flip $ foldl' $ flip Map.delete


-- Update the referred nodes using the given node transformer. Mind other refs!
adjust :: (NodeInfo -> NodeInfo) ->
          [Identifier] -> CompositionGraph -> CompositionGraph
adjust f = flip $ foldl' $ flip $ Map.adjust f


-- Change the link above or below a node
(⤴) , (⤵) :: Maybe Link -> NodeInfo -> NodeInfo
new ⤴ Node f t p _ = Node f t p new
new ⤵ Node f t _ s = Node f t new s


-- Remove/add the succedentOf/premiseOf link references to the nodes of a graph.
-- Makes use of a helper function that simply updates all nodes that are
-- referred to in some (hypothetical) link to either actually refer to such a
-- link or to put Nothings in its place
connect, disconnect :: [Link] -> CompositionGraph -> CompositionGraph
connect          = install Just
disconnect       = install (const Nothing)
install presence = flip $ foldl' (\g l -> adjust (presence l ⤴) (succedents l)
                                        $ adjust (presence l ⤵) (premises l) g)


-- Identify 'lost' hypotheses and conclusions with eachother. We assume that the
-- 'hypotheses' in the first list are not actually the premise of any link
-- anymore, and that the 'conclusions' are not the succedent of any link.
reunite :: [Identifier] -> [Identifier] -> CompositionGraph -> CompositionGraph
reunite []  []  g = g
reunite [h] [c] g = Map.delete h . Map.adjust (l⤴) c . adjust (l⤵) upstream $ g
  where l         = sub c h $ uplink h g
        upstream  = maybe [] premises l
reunite _ _ _     = error "Cannot reconnect multiple disconnected hypotheses\
      \and conclusions. Make sure that the proof transformations are sensible."

-- An inefficient but convenient way to substitute c for h in l
sub :: Identifier -> Identifier -> Maybe Link -> Maybe Link
sub c h l = flip apply l $ map sub' $ fromJust $ unify' l l where
  sub' (k,v) |   k==h    = (k,c)
             | otherwise = (k,v)


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


-- Partition the nodes of a set of links into those at the hypothesis end, those
-- 'inside' the links structure and those at the conclusion end, respectively
sift :: [Link] -> ([Identifier], [Identifier], [Identifier])
sift ls = (p \\ s, p `intersect` s, s \\ p)
  where all' = flip concatMap ls
        p    = all' premises
        s    = all' succedents


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
step  :: [ProofTransformation] -> CompositionGraph -> [CompositionGraph]
step  transformations graph =
  let possibilities = concatMap (instancesIn graph) transformations
  in  map (transform graph) possibilities


-- Looping. The code is already clearer than any explanation can be.
loop :: (a -> Maybe a) -> a -> a
loop f start = case f start of
  Just next -> loop f next
  Nothing   -> start


-- Is the composition graph a valid proof net?
valid :: CompositionGraph -> Bool
valid = isTree . loop greedy . asProofnet where
  greedy = listToMaybe . step (contractions ++ interactions)


-- Is our graph a tree? For now, we just disregard connectedness
isTree :: CompositionGraph -> Bool
isTree = not . cyclic


-- Naive (?) cycle detection
cyclic :: CompositionGraph -> Bool
cyclic g | Map.null g     = False
         | otherwise      = cyclic' up   [] [first] &&
                            cyclic' down [] [first] where
  first                   = head $ Map.keys g
  up k                    = maybe [] premises   $ uplink   k g
  down k                  = maybe [] succedents $ downlink k g
  cyclic' xplr seen (x:q) | x `elem` seen = True
                          | otherwise     = cyclic' xplr (x:seen) (xplr x++q)
  cyclic' _       _    [] = False
