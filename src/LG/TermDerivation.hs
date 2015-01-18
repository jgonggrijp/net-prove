module LG.TermDerivation where

import LG.Graph
import LG.Term
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set

data Subnet = Subnet { nodes         :: Set.Set Identifier
                     , term          :: Term
                     , commandLinks  :: [Link]  -- followable only
                     , cotensorLinks :: [Link]  -- same
                     , muLinks       :: [Link]  -- same
                     }
            deriving (Eq, Show)

type SubnetGraph = Map.Map Identifier Subnet  -- in which subnet is this node?

data ExtractionProgress = Progress { graph        :: CompositionGraph
                                   , nodesVisited :: Set.Set Identifier
                                   , subnets      :: [Subnet]
                                   , subnetGraph  :: SubnetGraph
                                   }

extractStart = Progress Set.empty [] Map.empty

extractSubnets :: CompositionGraph -> ([Subnet], SubnetGraph)
extractSubnets graph = subnets, subsGraph
  where (Progress _ _ subnets subsGraph) = Map.foldrWithKey extractSubnets' extractStart graph

extractSubnets' :: Identifier -> NodeInfo -> ExtractionProgress -> ExtractionProgress
extractSubnets' index node progress | Set.member index visited = progress
                                    | otherwise                = progress'
  where (Progress graph visited subs subsGraph) = progress
        seed = Subnet (Set.singleton index) (term node) [] [] []
        expand s = expandSubnet s graph (index :@ node)  -- note: partial appl.
        newsub' = maybe seed (expand seed) $ premiseOf node
        newsub = maybe newsub' (expand newsub') $ succedentOf node
        visited' = union visited (nodes newsub)
        subsGraph' = Set.foldr (flip Map.insert newsub) subsGraph (nodes newsub)
        progress' = Progress graph visited' newsub:subs subsGraph'

