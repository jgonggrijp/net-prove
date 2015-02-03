module LG.SubnetGraph where

{-
    Term derivation from a proof net takes two steps: first, rooted
    subnets are extracted from the graph and followable
    command/cotensor/mu links are registered; second, the
    aforementioned followable links are tracked and the subnets are
    merged until a single term is associated with the entire proof
    net. See also LG.Subnet and (of course) [MM12].

    This module contains algorithms for both steps, which are
    related through the SubnetGraph type. The latter is an
    administrative interface, which may be regarded both as the
    output of the first step of term derivation and as the input to
    the second step of term derivation. The logic for the first step
    contained in this module is just a wrapper for the core logic
    contained in LG.Subnet. The logic for the second step, on the
    other hand, is contained entirely in this module. At the end of
    the module, we find a couple of function that server to wrap up
    the entire procedure.
-}

import Data.Maybe
import Data.Tuple (swap)
import qualified Data.Map as Map
import qualified Data.Set as Set

import LG.Base
import LG.Term
import LG.Graph
import LG.Subnet

{-
    The administrative interface that is output of the first step and
    input to the second step of term derivation. It just maps node
    identifiers to subnets.
-}
type SubnetGraph = Map.Map Identifier Subnet

{-
    The wrapper for step 1 starts here. In LG.Subnet we defined the
    necessary logic to find and accumulate the complete subnet that
    any given node from a CompositionGraph belongs to. Now, we want
    to do that for all nodes in a CompositionGraph and end up with
    the complete set of its rooted subnets. This calls for a fold!

    During the fold, several things need to be kept track of. Not
    only do we want to collect subnets and remember which node
    belongs to which subnet, but we also want to keep track of which
    nodes have been visited in order to not repeat any work. On top
    of that, we need the CompositionGraph in order to find the nodes
    that are attached to a particular link. ExtractionProgress is our
    convenient datastructure to hold all that inforation.
-}
data ExtractionProgress = Progress { graph        :: CompositionGraph
                                   , nodesVisited :: Set.Set Identifier
                                   , subnets      :: [Subnet]
                                   , subnetGraph  :: SubnetGraph
                                   }

{-
    seedProgress provides the initial accumulator for the fold.
-}
seedProgress :: CompositionGraph -> ExtractionProgress
seedProgress graph = Progress graph Set.empty [] Map.empty

{-
    extractSubnets does the actual fold.
-}
extractSubnets :: CompositionGraph -> ([Subnet], SubnetGraph)
extractSubnets graph = (subnets extractEnd, subnetGraph extractEnd)
  where extractEnd = Map.foldrWithKey extractSubnets' extractStart graph
        extractStart = seedProgress graph

{-
    extractSubnets' is the function with which we fold over the
    CompositionGraph, and which uses the core logic from LG.Subnet
    internally.
-}
extractSubnets' :: Identifier -> NodeInfo -> ExtractionProgress -> ExtractionProgress
extractSubnets' index node progress | Set.member index visited = progress
                                    | otherwise                = progress'
  where (Progress graph visited subs subsGraph) = progress
        seed = fromNode (index :@ node)
        newsub' = expandTentacle' seed    graph (Succ index)
        newsub  = expandTentacle' newsub' graph (Prem index)
        visited' = Set.union visited (nodes newsub)
        subsGraph' = Set.foldr (flip Map.insert newsub) subsGraph (nodes newsub)
        progress' = Progress graph visited' (newsub:subs) subsGraph'
{-
    With hindsight, this part of the module could have been
    streamlined a bit by partially applying extractSubnets' to the
    CompositionGraph first and by using (subnetGraph
    ExtractionProgress) also as a lookup table for nodes that have
    already been visited, because its keys contain the same
    information as (nodesVisited ExtractionProgress). Then it would
    suffice to use a tuple ([Subnet], SubnetGraph) as the
    accumulator, and ExtractionProgress and seedProgress could be
    eliminated altogether.
-}


validExtensions :: SubnetGraph -> CompositionGraph -> Link -> Subnet -> [Subnet]
validExtensions sgraph cgraph target net = case net of
    (Subnet _ (C _) _ cots _) -> if Set.null cots then muExtensions
                                                  else cotensorExtensions
    _                         -> commandExtensions
  where muExtensions = concatMap (extendMu net sgraph cgraph target) muL
        cotensorExtensions = concatMap (extendCotensor net sgraph cgraph target) cotL
        commandExtensions = concatMap (extendCommand net sgraph cgraph target) comL
        muL = Set.toList $ muLinks net
        cotL = Set.toList $ cotensorLinks net
        comL = Set.toList $ commandLinks net

extendMu :: Subnet -> SubnetGraph -> CompositionGraph -> Link -> Link -> [Subnet]
extendMu net sgraph cgraph target link@(t1 :|: t2)
    | link == target = finalMu
    | otherwise      = validExtensions sgraph' cgraph target mergeNet
  where (Subnet ourNodes (C commandTerm) coms cots mus) = net
        (i1, i2) = (referee t1, referee t2)
        (ourID, theirID) | Set.member i1 ourNodes = (i1, i2)
                         | Set.member i2 ourNodes = (i2, i1)
        ourVar = term $ fromJust $ Map.lookup ourID cgraph
        theirVar = term $ fromJust $ Map.lookup theirID cgraph
        theirNet = fromJust $ Map.lookup theirID sgraph
        muTerm = case ourVar of
            (Va (Variable v)) -> E $ Comu v commandTerm
            (Ev (Covariable v)) -> V $ Mu v commandTerm
        mus' = Set.delete link mus
        ourNet = Subnet ourNodes muTerm coms cots mus'
        mergeNet = merge ourNet theirNet theirVar
        mergeNodes = nodes mergeNet
        update i s | Set.member i mergeNodes = mergeNet
                   | otherwise = s
        sgraph' = Map.mapWithKey update sgraph
        finalMu | Set.null mus' && (Set.size mergeNodes == Map.size cgraph) = [mergeNet]
                | otherwise     = []

extendCommand :: Subnet -> SubnetGraph -> CompositionGraph -> Link -> Link -> [Subnet]
extendCommand net sgraph cgraph target link@(t1 :|: t2) = extensions
  where (Subnet ourNodes ourTerm coms cots mus) = net
        (i1, i2) = (referee t1, referee t2)
        (ourID, theirID) | Set.member i1 ourNodes = (i1, i2)
                         | Set.member i2 ourNodes = (i2, i1)
        theirVar = term $ fromJust $ Map.lookup theirID cgraph
        commandTerm = case (theirVar, ourTerm) of
            (Va (Variable   v), E (E' t)) -> C $ v :⌉ t
            (Ev (Covariable v), V (V' t)) -> C $ t :⌈ v
        coms' = Set.delete link coms
        mergeNodes = Set.insert theirID ourNodes
        mergeNet = Subnet mergeNodes commandTerm coms' cots mus
        update i s | Set.member i mergeNodes = mergeNet
                   | otherwise = s
        sgraph' = Map.mapWithKey update sgraph
        extensions = validExtensions sgraph' cgraph target mergeNet

extendCotensor :: Subnet -> SubnetGraph -> CompositionGraph -> Link -> Link -> [Subnet]
extendCotensor net sgraph cgraph target link | bothActiveIncluded = extensions
                                             | otherwise          = []
  where (Just tm :-: [t1, t2]) = transpose link
        (Subnet ourNodes ourTerm@(C commandTerm) coms cots mus) = net
        (im, i1, i2) = (referee' tm, referee' t1, referee' t2)
        bothActiveIncluded = Set.member i1 ourNodes && Set.member i2 ourNodes
        termOfHead = term . fromJust . flip Map.lookup cgraph . referee . head
        representative t
            | fromNodeTerm v `isSubtermOf` ourTerm = v
            | otherwise = case t of
                (Prem i) -> termOfHead $ premises $ fromJust $ succedentOf $ node i
                (Succ i) -> termOfHead $ succedents $ fromJust $ premiseOf $ node i
          where v = term $ fromJust $ Map.lookup (referee' t) cgraph
                node = fromJust . flip Map.lookup cgraph
        extractName (Va (Variable v)) = v
        extractName (Ev (Covariable v)) = v
        name = extractName . representative
        names = (name t1, name t2)
        (n1, n2) = case link of
            ([MainT _] :●: [Active _, Active _]) -> names
            ([Active _] :●: [MainT _, Active _]) -> names
            ([Active _] :●: [Active _, MainT _]) -> swap names
            ([MainT _, Active _] :●: [Active _]) -> swap names
            ([Active _, MainT _] :●: [Active _]) -> names
            ([Active _, Active _] :●: [MainT _]) -> names
        nm = extractName $ term $ fromJust $ Map.lookup im cgraph
        mergeNodes = Set.insert im ourNodes
        mergeTerm = C $ Cut n1 n2 nm commandTerm
        cots' = Set.delete link cots
        mergeNet = Subnet mergeNodes mergeTerm coms cots' mus
        update i s | Set.member i mergeNodes = mergeNet
                   | otherwise = s
        sgraph' = Map.mapWithKey update sgraph
        extensions = validExtensions sgraph' cgraph target mergeNet

termsFromProofnet :: CompositionGraph -> Link -> [Term]
termsFromProofnet cgraph target = map sterm extensions
  where (nets, sgraph) = extractSubnets cgraph
        extensions = concatMap (validExtensions sgraph cgraph target) nets

-- variant of the above that attempts to auto-detect the target link
termsFromProofnet' :: CompositionGraph -> [Term]
termsFromProofnet' cgraph = case target of
    Nothing -> []
    _       -> map sterm extensions
  where (nets, sgraph) = extractSubnets cgraph
        (_, lastSubnet) = Map.findMax sgraph
        target = findInwardsMu lastSubnet nets
        target' = fromJust target
        extensions = concatMap (validExtensions sgraph cgraph target') nets

findInwardsMu :: Subnet -> [Subnet] -> Maybe Link
findInwardsMu net nets = listToMaybe candidates'
  where nets' = filter (/= net) nets
        candidates = concatMap (Set.toList . muLinks) nets'
        inside = flip Set.member (nodes net)
        pointsIntoNet = any inside . map referee . tentacles
        candidates' = filter pointsIntoNet candidates
