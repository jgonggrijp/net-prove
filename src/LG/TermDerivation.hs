module LG.TermDerivation where

import LG.Graph
import qualified Data.Map as Map
import qualified Data.Set as Set

class Substitutable t where
    substituteV :: ValueTerm -> ValueTerm -> t -> t  -- substitute x for y in z
    substituteE :: ContextTerm -> ContextTerm -> t -> t

instance Substitutable Term where
    substituteV x y (V z) = V $ substituteV x y z
    substituteV x y (E z) = E $ substituteV x y z
    substituteV x y (C z) = C $ substituteV x y z
    substituteE x y (V z) = V $ substituteE x y z
    substituteE x y (E z) = E $ substituteE x y z
    substituteE x y (C z) = C $ substituteE x y z

instance Substitutable ValueTerm where
    substituteV x (Vv (Variable s)) z@(Vv (Variable t)) = if s == t then x else z
    substituteV x y (Vv z)   = Vv $ substituteV x y z
    substituteV x y (Mu s z) = Mu s $ substituteV x y z
    substituteE x y z@(Vv (Variable _)) = z
    substituteE x y (Vv z)   = Vv $ substituteE x y z
    substituteE x y (Mu s z) = Mu s $ substituteE x y z

instance Substitutable ContextTerm where
    substituteE x (Ee (Covariable s)) z@(Ee (Covariable t)) = if s == t then x else z
    substituteE x y (Ee z)     = Ee $ substituteE x y z
    substituteE x y (Comu s z) = Comu s $ substituteE x y z
    substituteV x y z@(Ee (Covariable _)) = z
    substituteV x y (Ee z)     = Ee $ substituteV x y z
    substituteV x y (Comu s z) = Comu s $ substituteV x y z

instance Substitutable CommandTerm where
    substituteV x y (Cut s t u z) = Cut s t u $ substituteV x y z
    substituteV x y (z :⌈ s)      = substituteV x y z :⌈ s
    substituteV x y (s :⌉ z)      = s :⌉ substituteV x y z
    substituteE x y (Cut s t u z) = Cut s t u $ substituteE x y z
    substituteE x y (z :⌈ s)      = substituteE x y z :⌈ s
    substituteE x y (s :⌉ z)      = s :⌉ substituteE x y z

instance Substitutable ValueTerm' where
    substituteV (Vv x) (Vv (Variable s)) z@(Variable t) = if s == t then x else z
    substituteV x y (v :<×> w) = substituteV x y v :<×> substituteV x y w
    substituteV x y (v :<\> w) = substituteV x y v :<\> substituteV x y w
    substituteV x y (v :</> w) = substituteV x y v :</> substituteV x y w
    substituteE x y z@(Variable _) = z
    substituteE x y (v :<×> w) = substituteE x y v :<×> substituteE x y w
    substituteE x y (v :<\> w) = substituteE x y v :<\> substituteE x y w
    substituteE x y (v :</> w) = substituteE x y v :</> substituteE x y w

instance Substitutable ContextTerm' where
    substituteE (Ee x) (Ee (Covariable s)) z@(Covariable t) = if s == t then x else z
    substituteE x y (v  :\  w) = substituteE x y v  :\  substituteE x y w
    substituteE x y (v  :/  w) = substituteE x y v  :/  substituteE x y w
    substituteE x y (v :<+> w) = substituteE x y v :<+> substituteE x y w
    substituteV x y z@(Covariable _) = z
    substituteV x y (v  :\  w) = substituteV x y v  :\  substituteV x y w
    substituteV x y (v  :/  w) = substituteV x y v  :/  substituteV x y w
    substituteV x y (v :<+> w) = substituteV x y v :<+> substituteV x y w

data Subnet = Subnet { context       :: CompositionGraph
                     , fringe        :: Set.Set Identifier
                     , term          :: Term
                     , commandLinks  :: [Link]  -- followable only
                     , cotensorLinks :: [Link]  -- same
                     , muLinks       :: [Link]  -- same
                     }
            deriving (Eq, Show)

type SubnetGraph = Map.Map Identifier Subnet  -- in which subnet is this node?

