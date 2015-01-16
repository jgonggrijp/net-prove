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

type SubnetGraph = Map.Map Identifier Subnet  -- in which subnet is this node?

-- replace x by y in z
substitute :: s -> s -> t -> t
substitute x y (V z)         = V $ substitute x y z
substitute x y (E z)         = E $ substitute x y z
substitute x y (C z)         = C $ substitute x y z
substitute (Vv (Variable s))   y z@(Vv (Variable t))   = if s == t then y else z
substitute (Ee (Covariable s)) y z@(Ee (Covariable t)) = if s == t then y else z
substitute x y (Vv z)        = Vv $ substitute x y z
substitute x y (Ee z)        = Ee $ substitute x y z
substitute x y (Mu s z)      = Mu s $ substitute x y z
substitute x y (Comu s z)    = Comu s $ substitute x y z
substitute x y (v :<×> w)    = substitute x y v :<×> substitute x y w
substitute x y (v :<\> w)    = substitute x y v :<\> substitute x y w
substitute x y (v :</> w)    = substitute x y v :</> substitute x y w
substitute x y (v  :\  w)    = substitute x y v  :\  substitute x y w
substitute x y (v  :/  w)    = substitute x y v  :/  substitute x y w
substitute x y (v :<+> w)    = substitute x y v :<+> substitute x y w
substitute x y (Cut s t u z) = Cut s t u $ substitute x y z
substitute x y (z :⌈ s)      = substitute x y z :⌈ s
substitute x y (s :⌉ z)      = s :⌉ substitute x y z
