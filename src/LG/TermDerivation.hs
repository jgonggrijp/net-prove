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

fromNode :: Occurrence NodeInfo -> Subnet
fromNode (nodeID :@ nodeInfo) = Subnet (Set.singleton nodeID) nodeTerm [] [] []
  where nodeTerm = fromNodeTerm (term nodeInfo)

consumeLink :: Subnet -> CompositionGraph -> Identifier -> Link -> Subnet
consumeLink net graph nodeID link@(_ :○: _)
    | nodeID == head ids = net'
    | otherwise          = expandTentacle' net' graph tMain
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
        --

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

expandSubnet :: Subnet -> CompositionGraph -> Occurrence NodeInfo -> Link -> Subnet
expandSubnet net graph node link@([t1, t2] :○: [t3])  -- fusion tensor
    | something
  where (nodeID :@ (Node _ nodeTerm _ _)) = node
        linkMain = fromJust $ mainFormula link
        (Node _ linkTerm _ _) = fromJust $ Map.lookup linkMain graph
