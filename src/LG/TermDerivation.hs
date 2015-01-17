module LG.TermDerivation where

import LG.Graph
import qualified Data.Map as Map
import qualified Data.Set as Set

data Subnet a = Subnet { context       :: CompositionGraph
                       , fringe        :: Set.Set Identifier
                       , term          :: a
                       , commandLinks  :: [Link]  -- followable only
                       , cotensorLinks :: [Link]  -- same
                       , muLinks       :: [Link]  -- same
                       }
              deriving (Eq, Show)

type SubnetGraph a = Map.Map Identifier (Subnet a)  -- in which subnet is this node?

class Term a where
  substitute :: Term b => b -> b -> a -> a --substitute x for y in z
  asValue    :: a -> Maybe ValueTerm'
  asContext  :: a -> Maybe ContextTerm'
  asValue   _ = Nothing
  asContext _ = Nothing

instance Term CommandTerm where
  substitute x y (Cut s t u z) = Cut s t u $ substitute x y z
  substitute x y (z :⌈ s)      = substitute x y z :⌈ s
  substitute x y (s :⌉ z)      = s :⌉ substitute x y z

instance Term ContextTerm where
  asContext (Ee x) = asContext x
  substitute x y (Comu s z) = Comu s $ substitute x y z
  substitute x y (Ee z)     = Ee     $ substitute x y z

instance Term ContextTerm' where
  asContext x@(Covariable _) = Just x
  substitute x y (v  :\  w)       = substitute x y v  :\  substitute x y w
  substitute x y (v  :/  w)       = substitute x y v  :/  substitute x y w
  substitute x y (v :<+> w)       = substitute x y v :<+> substitute x y w
  substitute x y z@(Covariable _) = case (asContext x, asContext y) of
    (Just x', Just y') -> if y' == z then x' else z
    _ -> z

instance Term ValueTerm where
  asValue (Vv x) = asValue x
  substitute x y (Mu s z) = Mu s $ substitute x y z
  substitute x y (Vv z)   = Vv   $ substitute x y z

instance Term ValueTerm' where
  asValue x@(Variable _) = Just x
  substitute x y (v :<×> w) = substitute x y v :<×> substitute x y w
  substitute x y (v :<\> w) = substitute x y v :<\> substitute x y w
  substitute x y (v :</> w) = substitute x y v :</> substitute x y w
  substitute x y z@(Variable _) = case (asValue x, asValue y) of
    (Just x', Just y') -> if y' == z then x' else z
    _ -> z
