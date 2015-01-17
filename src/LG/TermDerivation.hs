module LG.TermDerivation where

import LG.Graph
import qualified Data.Map as Map
import qualified Data.Set as Set

class Substitutable a where
    substitute :: ValidSubstitution b => b -> b -> a -> a
    --substitute x for y in z

class ValidSubstitution a where
    asValue    :: a -> Maybe ValueTerm
    asContext  :: a -> Maybe ContextTerm
    asValue   _ = Nothing
    asContext _ = Nothing

instance ValidSubstitution ValueTerm where
    asValue x = Just x

instance ValidSubstitution ContextTerm where
    asContext x = Just x

instance Substitutable CommandTerm where
    substitute x y (Cut s t u z) = Cut s t u $ substitute x y z
    substitute x y (z :⌈ s)      = substitute x y z :⌈ s
    substitute x y (s :⌉ z)      = s :⌉ substitute x y z

instance Substitutable ContextTerm where
    -- the following matcher enables substitution of a co-mu binding
    -- for a covariable
    substitute x y z@(Ee (Covariable s)) = case (asContext x, asContext y) of
        (Just x', Just (Ee (Covariable t))) -> if s == t then x' else z
        _ -> z
    substitute x y (Ee z)                = Ee     $ substitute x y z
    substitute x y (Comu s z)            = Comu s $ substitute x y z

instance Substitutable ContextTerm' where
    substitute x y (v  :\  w)       = substitute x y v  :\  substitute x y w
    substitute x y (v  :/  w)       = substitute x y v  :/  substitute x y w
    substitute x y (v :<+> w)       = substitute x y v :<+> substitute x y w
    -- given instance Substitutable ContextTerm, the following matcher
    -- can only apply directly after recursion into (s' :⌉ z')
    substitute x y z@(Covariable s) = case (asContext x, asContext y) of
        (Just (Ee x'), Just (Ee (Covariable t))) -> if s == t then x' else z
        _ -> z

instance Substitutable ValueTerm where
    substitute x y z@(Vv (Variable s)) = case (asValue x, asValue y) of
        (Just x', Just (Vv (Variable t))) -> if s == t then x' else z
        _ -> z
    substitute x y (Mu s z)            = Mu s $ substitute x y z
    substitute x y (Vv z)              = Vv   $ substitute x y z

instance Substitutable ValueTerm' where
    substitute x y (v :<×> w)     = substitute x y v :<×> substitute x y w
    substitute x y (v :<\> w)     = substitute x y v :<\> substitute x y w
    substitute x y (v :</> w)     = substitute x y v :</> substitute x y w
    substitute x y z@(Variable s) = case (asValue x, asValue y) of
        (Just (Vv x'), Just (Vv (Variable t))) -> if s == t then x' else z
        _ -> z

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
  where (Progress _ subnets subsGraph) = Map.foldrWithKey extractSubnets' extractStart graph

extractSubnets' :: Identifier -> NodeInfo -> ExtractionProgress -> ExtractionProgress
extractSubnets' index node progress | Set.member index visited = progress
                                    | otherwise                = progress'
  where (Progress graph visited subs subsGraph) = progress
        progress' = Progress graph visited' newsub:subs subsGraph'
        newsub = expandSubnet seed (index :@ node) graph  -- use maybe on links instead
        seed = Subnet (Set.singleton index) (term node) [] [] []
        visited' = union visited (nodes newsub)
        subsGraph' = Set.foldr (flip Map.insert newsub) subsGraph (nodes newsub)
