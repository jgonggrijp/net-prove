module LG.Graph where

import Data.List
import Data.Maybe
import qualified Data.Map as Map

import LG.Base
import LG.Term

data Tentacle = MainT Identifier | Active Identifier deriving (Eq, Ord, Show)

referee :: Tentacle -> Identifier
referee (MainT  i) = i
referee (Active i) = i

isMain :: Tentacle -> Bool
isMain (MainT  _) = True
isMain (Active _) = False

-- there should be at most one main formula in any given tentacle list
findMain :: [Tentacle] -> Maybe Tentacle
findMain = listToMaybe . filter isMain

--           premises       succedents
data Link = [Tentacle] :○: [Tentacle]  -- Tensor
          | [Tentacle] :●: [Tentacle]  -- Cotensor
          |  Tentacle  :|:  Tentacle   -- Axioma
          deriving (Eq, Ord, Show)

prem, conc :: Link -> [Identifier]
prem = map referee . premises
conc = map referee . succedents

premises, succedents :: Link -> [Tentacle]
premises   (ts :○: _ ) = ts
premises   (ts :●: _ ) = ts
premises   (t  :|: _ ) = [t]
succedents (_  :○: ts) = ts
succedents (_  :●: ts) = ts
succedents (_  :|: t ) = [t]

mainFormula :: Link -> Maybe Tentacle
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

-- Function that inserts nodes at given ids, overwriting any pre-existing mappings
-- Complexity: O(m*(log (n+m))), for m is the number of nodes being added and n is the number of nodes in the graph
insertNodes ::  [Occurrence NodeInfo] -> CompositionGraph -> CompositionGraph
insertNodes [] graph = graph
insertNodes ((id :@ formula):nodes) graph = insertNodes nodes (Map.insert id formula graph)
