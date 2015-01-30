module LG.SubnetGraph where

import Data.Maybe
import Data.Tuple (swap)
import qualified Data.Map as Map
import qualified Data.Set as Set

import LG.Base
import LG.Term
import LG.Graph
import LG.Subnet

type SubnetGraph = Map.Map Identifier Subnet  -- in which subnet is this node?

data ExtractionProgress = Progress { graph        :: CompositionGraph
                                   , nodesVisited :: Set.Set Identifier
                                   , subnets      :: [Subnet]
                                   , subnetGraph  :: SubnetGraph
                                   }

seedProgress :: CompositionGraph -> ExtractionProgress
seedProgress graph = Progress graph Set.empty [] Map.empty

extractSubnets :: CompositionGraph -> ([Subnet], SubnetGraph)
extractSubnets graph = (subnets extractEnd, subnetGraph extractEnd)
  where extractEnd = Map.foldrWithKey extractSubnets' extractStart graph
        extractStart = seedProgress graph

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
