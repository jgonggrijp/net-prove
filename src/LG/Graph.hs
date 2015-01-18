module LG.Graph where

import Data.List
import Data.Maybe
import qualified Data.Map as Map

type Name = String
type Identifier = Int  -- to be assigned using Data.IORef

data Occurrence a = Identifier :@ a deriving (Eq, Show)

abstract :: Occurrence a -> a
abstract (_ :@ x) = x

data Formula = P PositiveFormula | N NegativeFormula deriving (Eq, Show)

data PositiveFormula = AtomP Name
                     | Formula :<×>: Formula
                     | Formula :<\>: Formula
                     | Formula :</>: Formula
                     deriving (Eq, Show)

data NegativeFormula = AtomN Name
                     | Formula  :\:  Formula
                     | Formula  :/:  Formula
                     | Formula :<+>: Formula
                     deriving (Eq, Show)

data ValueTerm   = Variable Name
                 | ValueTerm   :<×> ValueTerm
                 | ContextTerm :<\> ValueTerm
                 | ValueTerm   :</> ContextTerm
                 | Mu Name CommandTerm
                 deriving (Eq, Show)

data ContextTerm = Covariable Name
                 | ValueTerm    :\  ContextTerm
                 | ContextTerm  :/  ValueTerm
                 | ContextTerm :<+> ContextTerm
                 | Comu Name CommandTerm
                 deriving (Eq, Show)

data CommandTerm = Cut Name Name Name CommandTerm  -- (first second) / third
                 | ValueTerm :⌈ Name               -- Command right
                 | Name      :⌉ ContextTerm        -- Command left
                 deriving (Eq, Show)

data Tentacle = MainT Identifier | Active Identifier deriving (Eq, Show)

referee :: Tentacle -> Identifier
referee (MainT  i) = i
referee (Active i) = i

isMain :: Tentacle -> Bool
isMain (MainT  _) = True
isMain (Active _) = False

-- there should be at most one main formula in any given tentacle list
findMain :: [Tentacle] -> Maybe Identifier
findMain = listToMaybe . map referee . filter isMain

--           premises       succedents
data Link = [Tentacle] :○: [Tentacle]  -- Tensor
          | [Tentacle] :●: [Tentacle]  -- Cotensor
          |  Tentacle  :|:  Tentacle   -- Axioma
          deriving (Eq, Show)

premises, succedents :: Link -> [Identifier]
premises   (ts :○: _ ) = map referee ts
premises   (ts :●: _ ) = map referee ts
premises   (t  :|: _ ) = [referee t]
succedents (_  :○: ts) = map referee ts
succedents (_  :●: ts) = map referee ts
succedents (_  :|: t ) = [referee t]

mainFormula :: Link -> Maybe Identifier
mainFormula (ts :○: tt) = maybe (findMain tt) Just (findMain ts)
mainFormula (ts :●: tt) = maybe (findMain tt) Just (findMain ts)
mainFormula (_  :|: _ ) = Nothing

-- dual link representation: separate main from active, annotate
-- tentacles with premise/succedent. WARNING: loses information!

data Tentacle' = Prem Identifier | Succ Identifier deriving (Eq, Show)

referee' :: Tentacle' -> Identifier
referee' (Prem i) = i
referee' (Succ i) = i

data Link' = Maybe Tentacle' :-: [Tentacle'] deriving (Eq, Show)

transpose :: Link -> Link'
transpose link = listToMaybe (pMain ++ sMain) :-: (pActive ++ sActive)
  where p = partition isMain $ premises link
        s = partition isMain $ succedents link
        pMain = map (Prem . referee) (fst p)
        sMain = map (Succ . referee) (fst s)
        pActive = map (Prem . referee) (snd p)
        sActive = map (Succ . referee) (snd s)

data NodeInfo = Value   { pformula    :: PositiveFormula
                        , vterm       :: ValueTerm          -- see note below
                        , premiseOf   :: Maybe Link
                        , succedentOf :: Maybe Link
                        }
              | Context { nformula    :: NegativeFormula
                        , cterm       :: ContextTerm
                        , premiseOf   :: Maybe Link
                        , succedentOf :: Maybe Link
                        }
              deriving (Eq, Show)
{-
    A value term may be associated with a negative formula, or
    a context term with a positive formula, after mu/comu binding.
    However, this will only occur during term derivation and will
    never be important during unfolding, connecting or verification
    and hence never needs to be represented in the graph itself.
-}

type CompositionGraph = Map.Map Identifier NodeInfo

hypotheses :: CompositionGraph -> [Identifier]
hypotheses = Map.keys . Map.filter (isNothing . succedentOf)

conclusions :: CompositionGraph -> [Identifier]
conclusions = Map.keys . Map.filter (isNothing . premiseOf)

-- unfoldHypothesis :: IO Int -> Identifier -> CompositionGraph
