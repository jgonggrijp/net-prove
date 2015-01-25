module LG.SubnetGraph where

import Data.Maybe
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
    (Subnet _ (C _) _ Set.empty _) -> muExtensions
    (Subnet _ (C _) _ _         _) -> cotensorExtensions
    _                              -> commandExtensions
  where muExtensions = concatMap (extendMu net sgraph cgraph target) muL
        cotensorExtensions = concatMap (extendCotensor net sgraph cgraph) cotL
        commandExtensions = concatMap (extendCommand net sgraph cgraph) comL
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
        ourVar = term $ Map.lookup ourID cgraph
        theirVar = term $ Map.lookup theirID cgraph
        theirNet = Map.lookup theirID sgraph
        muTerm = case ourVar of
            (Va (Variable v)) -> E $ Comu v commandTerm
            (Ev (Covariable v)) -> V $ Mu v commandTerm
        mus' = Set.delete link mus
        ourNet = Subnet ourNodes muTerm coms cots mus'
        mergeNet = merge ourNet theirNet theirVar
        update i s | Set.member i (nodes ourNet) = mergeNet
                   | Set.member i (nodes theirNet) = mergeNet
                   | otherwise = s
        sgraph' = Map.mapWithKey update sgraph
        finalMu | Set.null mus' = [mergeNet]
                | otherwise     = []
