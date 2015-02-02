module LG.Subnet where

{-
    As explained in [MM12 p. 24], term derivation for a proof net
    takes two steps. First, all maximal rooted subnets (i.e. with a
    single main formula) consisting of tensor links are extracted
    from the composition graph and the corresponding links are marked
    as visited. Second, the remaining cotensor/command/mu links are
    followed and subnets are merged until all links have been visited.

    This module defines a datastructure that corresponds to the
    aforementioned subnets, as well as several associated functions
    that facilicate the first step of term derivation. There are some
    superficial differences between the theoretical description in
    [MM12] and the technical implementation in here, which will be
    highlighted as appropriate. The results, however, are exactly the
    same.
-}

import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

import LG.Base
import LG.Term
import LG.Graph

{-
    A subnet is essentially a connected subset of a CompositionGraph
    which is a valid proof net with an associated term in its own
    right. While the "substance" of a subnet is defined by its
    interior nodes and links, we are more interested in its direct
    environment of *exterior* links that can be followed towards
    other subnets (for the purpose of deriving a term for the entire
    CompositionGraph). Hence, the datastructure below emphasizes
    those followable exterior links.

    A command link is an axiom link (:|:) of which the upper
    tentacle is attached to a value node and the lower tentacle is
    attached to a context node. A (co)mu link is an axiom link of
    which the tentacles are attached in the opposite way. These types
    of links have been illustrated in Figure 16 of [MM12].

    The rules to determine whether an exterior link is followable
    are described partially in definitions (8) of [MM12 p. 16] and
    partially in the enumeration on [MM12 p. 25]. They are summarized
    as follows. A command link is followable upwards from the current
    subnet if the associated formula is negative, or downwards if the
    formula is positive. A cotensor link is followable if both of its
    active formulae belong to nodes which are already interior to the
    current subnet. A mu link is followable upwards from the current
    subnet if its associated formula is positive, or downwards if the
    formula is negative.
-}
data Subnet = Subnet { nodes         :: Set.Set Identifier
                     , sterm         :: Term
                     , commandLinks  :: Set.Set Link
                     , cotensorLinks :: Set.Set Link
                     , muLinks       :: Set.Set Link
                     }
            deriving (Eq, Show)

{-
    Subnets are built inductively. Trivially, a node in isolation is
    always a subnet where the subnet term is the term of the node and
    there are at most two followable exterior links.

    fromNode produces such a trivial single-node subnet, in which
    the followable links are not yet identified.
-}
fromNode :: Occurrence NodeInfo -> Subnet
fromNode (nodeID :@ nodeInfo) = Subnet onlyNodeID nodeTerm none none none
  where onlyNodeID = Set.singleton nodeID
        nodeTerm = fromNodeTerm (term nodeInfo)
        none = Set.empty

{-
    There are two types of circumstances under which a subnet can be
    absorbed into another, adjacent subnet, to produce a larger
    subnet that includes all nodes and links of both as well as the
    link that connected them in its interior. In the first type of
    circumstance, the connecting link is either a tensor or a
    substitution link (axiom attached to two nodes of the same type)
    and the followable exterior links are unaffected. Which subnet
    should be absorbed into which is determined by tentacle
    direction; main merges into active. In the second type of
    circumstance, the connecting link is a followable (as defined
    above) and the subnet from which the connecting link is
    followable is absorbed into the other. In this case the
    followable link should be removed from the combined subnet.

    merge as defined below assumes the first type of circumstance,
    and is used as such in the current module. However, with proper
    preparation it can also be used for the second type of
    circumstance and it is used in this way in LG.SubnetGraph.

    net1 is merged into net2, substituting the term of net1 for v of
    net2.
-}
merge :: Subnet -> Subnet -> NodeTerm -> Subnet
merge net1 net2 v = Subnet allNodes mergeTerm mergeCommand mergeCotensor mergeMu
  where (Subnet nodes1 term1 command1 cotensor1 mu1) = net1
        (Subnet nodes2 term2 command2 cotensor2 mu2) = net2
        allNodes = Set.union nodes1 nodes2
        mergeTerm = case (term1, v) of
            ((V term1'), (Va v')) -> substitute term1' (V' v') term2
            ((E term1'), (Ev v')) -> substitute term1' (E' v') term2
        mergeCommand = Set.union command1 command2
        mergeCotensor = Set.union cotensor1 cotensor2
        mergeMu = Set.union mu1 mu2

-- Tests whether net1 is a sub-Subnet of net2.
includes :: Subnet -> Subnet -> Bool
net2 `includes` net1 = and [incNodes, incTerm, incCommand, incCotensor, incMu]
  where incNodes = (nodes net1) `Set.isSubsetOf` (nodes net2)
        incTerm = (sterm net1) `isSubtermOf` (sterm net2)
        incCommand = (commandLinks net1) `Set.isSubsetOf` (commandLinks net2)
        incCotensor = (cotensorLinks net1) `Set.isSubsetOf` (cotensorLinks net2)
        incMu = (muLinks net1) `Set.isSubsetOf` (muLinks net2)

consumeLink :: Subnet -> CompositionGraph -> Identifier -> Link -> Subnet
consumeLink net graph nodeID link@(_ :○: _)
    | nodeID == head ids = linkNet''
    | otherwise          = expandTentacle' linkNet'' graph tMain
  where (Just tMain :-: [t1, t2]) = transpose link
        ids = map referee' [tMain, t1, t2]
        [n1, n2] = map (fromJust . flip Map.lookup graph) (tail ids)
        [o1, o2] = zipWith (:@) (tail ids) [n1, n2]
        linkTerm = fromNodeTerm $ term $ fromJust $ Map.lookup (head ids) graph
        none = Set.empty
        linkNet = Subnet (Set.fromList ids) linkTerm none none none
        sub1 | nodeID == referee' t1 = net
             | otherwise             = expandTentacle' (fromNode o1) graph t1
        sub2 | nodeID == referee' t2 = net
             | otherwise             = expandTentacle' (fromNode o2) graph t2
        linkNet' = merge sub1 linkNet $ term n1
        linkNet'' = merge sub2 linkNet' $ term n2
consumeLink _ graph nodeID link@(_ :●: _)
    | nodeID == referee' tMain = fromNode $ nodeID :@ nodeInfo
    | otherwise                = net'
  where nodeInfo@(Node _ nodeTerm _ _) = fromJust $ Map.lookup nodeID graph
        term = fromNodeTerm nodeTerm
        (Just tMain :-: actives) = transpose link
        none = Set.empty
        net' = Subnet (Set.singleton nodeID) term none (Set.singleton link) none
consumeLink net graph nodeID link@(t1 :|: t2)
    | nodeID == i1 = case terms of
        [(Va _), (Ev _)] -> commandNet
        [(Ev _), (Va _)] -> muNet
        _                -> if sub2' `includes` sub2
            then merge net sub2' term2
            else merge sub2' net term1
    | nodeID == i2 = case terms of
        [(Va _), (Ev _)] -> commandNet'
        [(Ev _), (Va _)] -> comuNet
        _                -> if sub1' `includes` sub1
            then merge net sub1' term1
            else merge sub1' net term2
  where ids@[i1, i2] = fmap referee [t1, t2]
        infos@[n1, n2] = fmap (fromJust . flip Map.lookup graph) ids
        terms@[term1, term2] = fmap term infos
        f1 = formula n1
        (Subnet is t cms cts mus) = net
        commandNet = case f1 of
            (P _) -> Subnet is t (Set.insert link cms) cts mus
            (N _) -> net
        commandNet' = case f1 of
            (P _) -> net
            (N _) -> Subnet is t (Set.insert link cms) cts mus
        muNet = case f1 of
            (P _) -> net
            (N _) -> Subnet is t cms cts (Set.insert link mus)
        comuNet = case f1 of
            (P _) -> Subnet is t cms cts (Set.insert link mus)
            (N _) -> net
        [sub1, sub2] = fmap fromNode $ zipWith (:@) ids infos
        sub1' = expandTentacle' sub1 graph (Prem i1)
        sub2' = expandTentacle' sub2 graph (Succ i2)

expandTentacle' :: Subnet -> CompositionGraph -> Tentacle' -> Subnet
expandTentacle' net graph tentacle' = case tentacle' of
    (Prem nodeID) -> maybe net (expandNode nodeID net graph) $ succedentOf $ fromJust $ Map.lookup nodeID graph
    (Succ nodeID) -> maybe net (expandNode nodeID net graph) $ premiseOf $ fromJust $ Map.lookup nodeID graph

expandNode :: Identifier -> Subnet -> CompositionGraph -> Link -> Subnet
expandNode nodeID net graph link | net' `includes` net = net'
                                 | otherwise           = merge net' net var
  where net' = consumeLink net graph nodeID link
        var = term $ fromJust $ Map.lookup nodeID graph
