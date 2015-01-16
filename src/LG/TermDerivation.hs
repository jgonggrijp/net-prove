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

substituteValue :: ValueTerm -> ValueTerm -> Term -> Term
substituteValue (Vv (Variable s)) expansion (V (Vv (Variable s))) = V expansion
substituteValue var expansion (V (Vv (a :<×> b))) = V (Vv (subVA :<×> subVB))
substituteValue var expansion (V (Vv (a :<\> b))) = V (Vv (subEA :<\> subVB))
substituteValue var expansion (V (Vv (a :</> b))) = V (Vv (subVA :</> subEB))
substituteValue var expansion (V (Mu s a)) = V (Mu s subCA)
substituteValue var expansion unmodified@(E (Ee (Covariable _))) = unmodified
substituteValue var expansion (E (Ee (a :<+> b))) = E (Ee (subEA :<+> subEB))
substituteValue var expansion (E (Ee (a :\ b))) = E (Ee (subVA :\ subEB))
substituteValue var expansion (E (Ee (a :/ b))) = E (Ee (subEA :/ subVB))
substituteValue var expansion (E (Comu s a)) = E (Comu s subCA)
substituteValue var expansion (C (Cut s t u a)) = (C (Cut s t u subCA))
substituteValue var expansion (C (s :⌈ a)) = (C (s :⌈ subEA))
substituteValue var expansion (C (a :⌉ s)) = (C (subVA :⌉ s))
