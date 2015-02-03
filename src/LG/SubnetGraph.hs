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

    Extraction is the accumulator type as well as the result type.
-}
type Extraction = ([Subnet], SubnetGraph)

{-
    extractSubnets does the actual fold.
-}
extractSubnets :: CompositionGraph -> Extraction
extractSubnets graph = Map.foldrWithKey extract ([], Map.empty) graph
  where extract = extractSubnets' graph

{-
    extractSubnets' is the function with which we fold over the
    CompositionGraph, and which uses the core logic from LG.Subnet
    internally.
-}
extractSubnets' :: CompositionGraph -> Identifier -> NodeInfo -> Extraction -> Extraction
extractSubnets' graph index node accum@(subs, subsGraph)
    | Map.member index subsGraph = accum
    | otherwise                  = ((newsub:subs), subsGraph')
  where seed = fromNode (index :@ node)
        newsub' = expandTentacle' seed    graph (Succ index)
        newsub  = expandTentacle' newsub' graph (Prem index)
        subsGraph' = Set.foldr (flip Map.insert newsub) subsGraph (nodes newsub)

{-
    Step 2 starts here. We consider a Subnet in the context of a
    SubnetGraph, a CompositionGraph and the target mu Link that
    should be followed last (we want to finish with a mu binding
    because we are interested in terms for focused formulae only). If
    the current Subnet has a Command term and hence is in an
    asynchronous phase, we want to follow all cotensor links that are
    available, then switch to a synchronous phase and follow a (co)mu
    link. Otherwise we are in a synchronous phase and we want to look
    for a command link that we can follow to switch to an
    asynchronous phase again. These rules are also described in [MM12
    p. 25].

    We continue following any available links according to these
    rules, until we have collected the entire CompositionGraph or we
    run into a dead end. Along the way we may find multiple orders in
    which the links can be followed; for these reasons we store the
    results in a list (which may end up being empty). Each Subnet in
    the final list (if any) contains a possible term for the entire
    graph. In order to find *all* possible terms for the graph, we
    run the above procedure for all Subnets in parallel and
    concatenate the results.

    validExtensions runs the above procedure for a single given
    Subnet in a given context. It works in cyclic recursion with
    extendMu, extendCotensor and extendCommand.
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

{-
    extendMu, extendCotensor and extendCommand are relatively large
    functions, because they use LG.Subnet.merge internally (see
    description over there) and they have to prepare the ingredients
    for the merger, in order to remove the link that is being
    followed and to build the appropriate term. Despite being large,
    the functions are not as complicated as they may appear; apart
    from managing the merger ingredients, most of what they do is
    preparing to recursively call validExtensions in search for a
    completely merged Subnet. In order to grasp the logic, you may
    want to read extendCommand first because it is the simplest.

    extendMu has a special case because it might be the last step in
    the search tree. In this case it results in a list, finalMu, with
    at most one element.
-}
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

{-
    extendCommand is very similar to extendMu, but without the
    special case.
-}
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

{-
    extendCotensor is very large even relatively, because in addition
    to preparing merge ingredients and recursively calling
    validExtensions, it has to (1) check whether both active
    tentacles are attached to the current subnet and (2) determine in
    which order the (co)variables corresponding to those tentacles
    should appear in the resulting Cut term.
-}
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
            -- (this expression could be written with half as many 
            --  cases, but the intent is clearer in this way)
        nm = extractName $ term $ fromJust $ Map.lookup im cgraph
        mergeNodes = Set.insert im ourNodes
        mergeTerm = C $ Cut n1 n2 nm commandTerm
        cots' = Set.delete link cots
        mergeNet = Subnet mergeNodes mergeTerm coms cots' mus
        update i s | Set.member i mergeNodes = mergeNet
                   | otherwise = s
        sgraph' = Map.mapWithKey update sgraph
        extensions = validExtensions sgraph' cgraph target mergeNet

{-
    Finally, the functions that wrap up the term derivation procedure.
    
    termsFromProofnet runs steps 1 and 2 consecutively, trying subnet
    extension for all rooted subsets and concatenating the results as
    discussed above. It depends on an externally provided target mu
    link.
-}
termsFromProofnet :: CompositionGraph -> Link -> [Term]
termsFromProofnet cgraph target = map sterm extensions
  where (nets, sgraph) = extractSubnets cgraph
        extensions = concatMap (validExtensions sgraph cgraph target) nets

{-
    termsFromProofnet' is a variant of the above, which attempts to
    detect the target mu link automatically. It only succeeds if the
    target is the rightmost conclusion and the graph was produced by
    serially unfolding the formulae left to right with increasing
    identifiers, because it assumes that the node corresponding to
    the greatest identifier is in the subnet of the target formula.
    This happens to be true in our user interface where the user may
    specify a list of lexical items and request a proof that they can
    form a valid sentence, and the formulae are handled as by
    LG.Unfold.unfold. Note, however, that the function does not work
    for LG.TestGraph.testGraph because the identifiers in that graph
    were assigned manually in a different order.
-}
termsFromProofnet' :: CompositionGraph -> [Term]
termsFromProofnet' cgraph = case target of
    Nothing -> []
    _       -> map sterm extensions
  where (nets, sgraph) = extractSubnets cgraph
        (_, lastSubnet) = Map.findMax sgraph
        target = findInwardsMu lastSubnet nets
        target' = fromJust target
        extensions = concatMap (validExtensions sgraph cgraph target') nets

{-
    findInwardsMu is an implementation detail of termsFromProofnet'.
    As the name implies, it searches for an inwards-pointing (i.e.
    the opposite of followable) mu link for the given subnet in the
    given list of (other) subnets. Note that in a proof net, any
    subnet can have at most one inwards-pointing mu link.
-}
findInwardsMu :: Subnet -> [Subnet] -> Maybe Link
findInwardsMu net nets = listToMaybe candidates'
  where nets' = filter (/= net) nets
        candidates = concatMap (Set.toList . muLinks) nets'
        inside = flip Set.member (nodes net)
        pointsIntoNet = any inside . map referee . tentacles
        candidates' = filter pointsIntoNet candidates
