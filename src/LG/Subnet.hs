module LG.TermDerivation where

import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

import LG.Term
import LG.Graph

data Subnet = Subnet { nodes         :: Set.Set Identifier
                     , term          :: Term
                     , commandLinks  :: [Link]  -- followable only
                     , cotensorLinks :: [Link]  -- same
                     , muLinks       :: [Link]  -- same
                     }
            deriving (Eq, Show)

fromNode :: Occurrence NodeInfo -> Subnet
fromNode (nodeID :@ nodeInfo) = Subnet (Set.singleton nodeID) nodeTerm [] [] []
  where nodeTerm = fromNodeTerm (term nodeInfo)

-- merge first subnet into second, hooking the former's term into
-- the given (co)variable of the latter's term
merge :: ValidSubstitution a => Subnet -> Subnet -> a -> Subnet
merge net1 net2 v = Subnet allNodes mergeTerm mergeCommand mergeCotensor mergeMu
  where (Subnet nodes1 term1 command1 cotensor1 mu1) = net1
        (Subnet nodes2 term2 command2 cotensor2 mu2) = net2
        allNodes = Set.union nodes1 nodes2
        mergeTerm = substitute term1 v term2
        mergeCommand = command1 ++ command2
        mergeCotensor = cotensor1 ++ cotensor2
        mergeMu = mu1 ++ mu2

-- test whether the latter falls within the former
includes :: Subnet -> Subnet -> Bool
net2 `includes` net1 = and [incNodes, incTerm, incCommand, incCotensor, incMu]
  where incNodes = (nodes net1) `Set.isSubsetOf` (nodes net2)
        incTerm = (term net1) `isSubtermOf` (term net2)
        incCommand = (comSet net1) `Set.isSubsetOf` (comSet net2)
        incCotensor = (cotSet net1) `Set.isSubsetOf` (cotSet net2)
        incMu = (muSet net1) `Set.isSubsetOf` (muSet net2)
        comSet = Set.fromList . commandLinks
        cotSet = Set.fromList . cotensorLinks
        muSet = Set.fromList . muLinks

consumeLink :: Subnet -> CompositionGraph -> Identifier -> Link -> Subnet
consumeLink net graph nodeID link@(_ :○: _)
    | nodeID == head ids = linkNet''
    | otherwise          = expandTentacle' linkNet'' graph tMain
  where nodeInfo@(Node _ nodeTerm _ _) = Map.lookup nodeID graph
        (Just tMain :-: actives@[t1, t2]) = transpose link
        ids = map referee' (tMain:actives)
        [n1, n2] = map (flip Map.lookup graph) (tail ids)
        [o1, o2] = zipWith (:@) (tail ids) [n1, n2]
        linkTerm = fromNodeTerm $ term $ Map.lookup (head ids) graph
        linkNet = Subnet (Set.fromList ids) linkTerm [] [] []
        sub1 | nodeID == referee' t1 = net
             | otherwise             = expandTentacle' (fromNode o1) graph t1
        sub2 | nodeID == referee' t2 = net
             | otherwise             = expandTentacle' (fromNode o2) graph t2
        linkNet' = merge sub1 linkNet $ asSubstitution $ term n1
        linkNet'' = merge sub2 linkNet' $ asSubstitution $ term n2
consumeLink net graph nodeID link@(_ :●: _)
    | nodeID == referee' tMain = fromNode $ nodeID :@ nodeInfo
    | otherwise                = net''
  where nodeInfo@(Node _ nodeTerm _ _) = Map.lookup nodeID tMain
        term = fromNodeTerm nodeTerm
        (Just tMain :-: actives) = transpose link
        net' = Subnet (Set.singleton nodeID) term [] [link] []
        net'' = merge net net' $ asSubstitution nodeTerm
consumeLink net graph nodeID link@(t1 :|: t2)
    | nodeID == i1 = case terms of
        ((Va _), (Ev _)) -> commandNet
        ((Ev _), (Va _)) -> muNet
        _                -> expandTentacle' net graph (Succ i2)
    | nodeID == i2 = case terms of
        ((Va _), (Ev _)) -> commandNet'
        ((Ev _), (Va _)) -> comuNet
        _                -> expandTentacle' net graph (Prem i1)
  where ids@(i1, i2) = fmap referee (t1, t2)
        infos@(n1, n2) = fmap (flip Map.lookup graph) ids
        terms@(term1, term2) = fmap term infos
        f1 = formula n1
        (Subnet is t cms cts mus) = net
        commandNet = case f1 of
            (P _) -> Subnet is t (link:cms) cts mus
            (N _) -> net
        commandNet' = case f1 of
            (P _) -> net
            (N _) -> Subnet is t (link:cms) cts mus
        muNet = case f1 of
            (P _) -> net
            (N _) -> Subnet is t cms cts (link:mus)
        comuNet = case f1 of
            (P _) -> Subnet is t cms cts (link:mus)
            (N _) -> net

expandTentacle' :: Subnet -> Graph -> Tentacle' -> Subnet
expandTentacle' net graph tentacle' = case tentacle' of
    (Prem nodeID) -> maybe net (expandNode nodeID net graph) $ succedentOf node
    (Succ nodeID) -> maybe net (expandNode nodeID net graph) $ premiseOf node
  where node = lookup nodeID graph

expandNode :: Identifier -> Subnet -> Graph -> Link -> Subnet
expandNode nodeID net graph link | net' `includes` net = net'
                                 | otherwise           = merge net' net var
  where net' = consumeLink net graph nodeID link
        var = asSubstitution $ term $ lookup nodeID graph
