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
