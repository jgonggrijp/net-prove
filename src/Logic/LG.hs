module Logic.LG where

import Data.IORef
import qualified Data.Map as Map

data Formula = Atom String
    | Formula :*: Formula
    | Formula :\\ Formula
    | Formula :// Formula
    | Formula :+: Formula
    | Formula :-\ Formula
    | Formula :-/ Formula
    deriving (Eq, Ord, Show)

data Term = Variable String
    | Term :*:: Term
    | Term :\\: Term
    | Term ://: Term
    | Term :+:: Term
    | Term :-\: Term
    | Term :-/: Term
    | MuBind String Term
    | ComuBind String Term
    | CommandLeft String Term
    | CommandRight String Term
    | Cut String String String Term  -- first second / third
    deriving (Eq, Ord, Show)

data IndexedFormula = IndexedFormula {
    formula :: Formula,
    term :: Term,
    index :: Int }  -- use Data.IORef to keep a global counter
    deriving (Eq, Ord, Show)

data TentacleType = Premise | Succedent deriving (Eq, Ord, Show)

data Tentacle = Tentacle {
    tentacleType :: TentacleType,
    formula :: IndexedFormula }
    deriving (Eq, Ord)

data LinkType = Tensor | Cotensor | Axioma deriving (Eq, Ord, Show)

data Link = Link {
    linkType :: LinkType,
    tentacles :: [Tentacle], -- ordered from left to right
    mainTentacle :: Int } -- index of main formula, if applicable
    deriving (Eq, Ord, Show)

-- get all premises/succedents of a link
getAll :: TentacleType -> Link -> [IndexedFormula]
getAll t = map formula . filter ((== t) . tentacleType) . tentacles

mainFormula :: Link -> Maybe IndexedFormula
mainFormula (Link Axioma _  _) = Nothing
mainFormula (Link _      [] _) = Nothing
mainFormula (Link _      ts n) = Just $ formula $ ts !! n

data NodeType = Value | Context deriving (Eq, Ord, Show)

data NodeInfo = NodeInfo {
    nodeType :: NodeType,
    premiseLink :: Maybe Link,
    succedentLink :: Maybe Link }
    deriving (Eq, Ord, Show)

type CompositionGraph = Map.Map IndexedFormula NodeInfo

hypotheses :: CompositionGraph -> [IndexedFormula]
hypotheses = Map.keys . Map.filter ((== Nothing) . succedentLink)

conclusions :: CompositionGraph -> [IndexedFormula]
conclusions = Map.keys . Map.filter ((== Nothing) . premiseLink)

-- unfoldHypothesis :: IO Int -> IndexedFormula -> CompositionGraph
