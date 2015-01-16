module LG.TermDerivation where

import LG.Graph
import qualified Data.Map as Map
import qualified Data.Set as Set

data Term = V ValueTerm | E ContextTerm | C CommandTerm deriving (Eq, Show)

data Subnet = Subnet { context       :: CompositionGraph
                     , fringe        :: Set.Set Identifier
                     , term          :: Term
                     , commandLinks  :: [Link]  -- followable only
                     , cotensorLinks :: [Link]  -- same
                     , muLinks       :: [Link]  -- same
                     }
            deriving (Eq, Show)

data SubnetGraph = Map.Map Identifier Subnet  -- in which subnet is this node?