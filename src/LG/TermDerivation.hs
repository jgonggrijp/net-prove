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

class Substitutable t1 t2 where
    substitute :: t1 -> t1 -> t2 -> t2  -- substitute x for y in z

instance Substitutable ValueTerm Term where
    substitute x y (V z) = V $ substitute x y z
    substitute x y (E z) = E $ substitute x y z
    substitute x y (C z) = C $ substitute x y z

instance Substitutable ContextTerm Term where
    substitute x y (V z) = V $ substitute x y z
    substitute x y (E z) = E $ substitute x y z
    substitute x y (C z) = C $ substitute x y z

instance Substitutable ValueTerm ValueTerm where
    substitute x (Vv (Variable s)) z@(Vv (Variable t)) = if s == t then x else z
    substitute x y (Vv z) = Vv $ substitute x y z
    substitute x y (Mu s z) = Mu s $ substitute x y z

instance Substitutable ValueTerm ContextTerm where
    substitute x y (Ee z) = Ee $ substitute x y z
    substitute x y (Comu s z) = Comu s $ substitute x y z

instance Substitutable ValueTerm CommandTerm where
    substitute x y (Cut s t u z) = Cut s t u $ substitute x y z
    substitute x y (z :⌈ s) = substitute x y z :⌈ s
    substitute x y (s :⌉ z) = s :⌉ substitute x y z

instance Substitutable ContextTerm ValueTerm where
    substitute x y (Vv z) = Vv $ substitute x y z
    substitute x y (Mu s z) = Mu s $ substitute x y z

instance Substitutable ContextTerm ContextTerm where
    substitute x (Ee (Covariable s)) z@(Ee (Covariable t)) = if s == t then x else z
    substitute x y (Ee z) = Ee $ substitute x y z
    substitute x y (Comu s z) = Comu s $ substitute x y z

instance Substitutable ContextTerm CommandTerm where
    substitute x y (Cut s t u z) = Cut s t u $ substitute x y z
    substitute x y (z :⌈ s) = substitute x y z :⌈ s
    substitute x y (s :⌉ z) = s :⌉ substitute x y z

instance Substitutable ValueTerm ValueTerm' where
    substitute (Vv x) (Vv (Variable s)) z@(Variable t) = if s == t then x else z
    substitute x y (v :<×> w) = substitute x y v :<×> substitute x y w
    substitute x y (v :<\> w) = substitute x y v :<\> substitute x y w
    substitute x y (v :</> w) = substitute x y v :</> substitute x y w

instance Substitutable ValueTerm ContextTerm' where
    substitute x y (v  :\  w) = substitute x y v  :\  substitute x y w
    substitute x y (v  :/  w) = substitute x y v  :/  substitute x y w
    substitute x y (v :<+> w) = substitute x y v :<+> substitute x y w

instance Substitutable ContextTerm ValueTerm' where
    substitute x y (v :<×> w) = substitute x y v :<×> substitute x y w
    substitute x y (v :<\> w) = substitute x y v :<\> substitute x y w
    substitute x y (v :</> w) = substitute x y v :</> substitute x y w

instance Substitutable ContextTerm ContextTerm' where
    substitute (Ee x) (Ee (Covariable s)) z@(Covariable t) = if s == t then x else z
    substitute x y (v  :\  w) = substitute x y v  :\  substitute x y w
    substitute x y (v  :/  w) = substitute x y v  :/  substitute x y w
    substitute x y (v :<+> w) = substitute x y v :<+> substitute x y w
