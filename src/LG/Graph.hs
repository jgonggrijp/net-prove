module LG.Graph where

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

data Term = V ValueTerm | E ContextTerm | C CommandTerm deriving (Eq, Show)

data NodeTerm = Va ValueTerm | Ev ContextTerm deriving (Eq, Show)

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

data NodeInfo = Node { formula     :: Formula
                     , term        :: NodeTerm
                     , premiseOf   :: Maybe Link
                     , succedentOf :: Maybe Link
                     }
              deriving (Eq, Show)

type CompositionGraph = Map.Map Identifier NodeInfo

hypotheses :: CompositionGraph -> [Identifier]
hypotheses = Map.keys . Map.filter (isNothing . succedentOf)

conclusions :: CompositionGraph -> [Identifier]
conclusions = Map.keys . Map.filter (isNothing . premiseOf)

-- unfoldHypothesis :: IO Int -> Identifier -> CompositionGraph
