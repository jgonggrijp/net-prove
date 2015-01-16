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
substituteValue a b (V t) = V $ substituteValueV a b t
substituteValue a b (E t) = E $ substituteValueE a b t
substituteValue a b (C t) = C $ substituteValueC a b t

substituteValueV :: ValueTerm -> ValueTerm -> ValueTerm -> ValueTerm
substituteValueV (Vv (Variable s)) expansion (Vv (Variable s)) = expansion
substituteValueV var expansion (Vv (a :<×> b)) = Vv (subV a :<×> subV b)
  where subV = substituteValueV var expansion
substituteValueV var expansion (Vv (a :<\> b)) = Vv (subE a :<\> subV b)
  where subV = substituteValueV var expansion
        subE = substituteValueE var expansion
substituteValueV var expansion (Vv (a :</> b)) = Vv (subV a :</> subE b)
  where subV = substituteValueV var expansion
        subE = substituteValueE var expansion
substituteValueV var expansion (Mu s a) = Mu s subC a
  where subC = substituteValueC var expansion

substituteValueE :: ValueTerm -> ValueTerm -> ContextTerm -> ContextTerm
substituteValueE var expansion unmodified@(Ee (Covariable _)) = unmodified
substituteValueE var expansion (Ee (a :<+> b)) = Ee (subE a :<+> subE b)
  where subE = substituteValueE var expansion
substituteValueE var expansion (Ee (a :\ b)) = Ee (subV a :\ subE b)
  where subV = substituteValueV var expansion
        subE = substituteValueE var expansion
substituteValueE var expansion (Ee (a :/ b)) = Ee (subE a :/ subV b)
  where subV = substituteValueV var expansion
        subE = substituteValueE var expansion
substituteValueE var expansion (Comu s a) = Comu s subC a
  where subC = substituteValueC var expansion

substituteValueC :: ValueTerm -> ValueTerm -> CommandTerm -> CommandTerm
substituteValueC var expansion (Cut s t u a) = (Cut s t u subC a)
  where subC = substituteValueC var expansion
substituteValueC var expansion (s :⌈ a) = (s :⌈ subE a)
  where subE = substituteValueE var expansion
substituteValueC var expansion (a :⌉ s) = (subV a :⌉ s)
  where subV = substituteValueV var expansion
