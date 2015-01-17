module LG.Reductions where

import LG.Graph
import qualified Data.Map as Map

-- Eliminate axiom links so that the composition graph may be interpreted as a
-- proof structure. (Note that this also deletes any unconnected formula!)
reduce :: CompositionGraph -> CompositionGraph
reduce = Map.mapMaybe (\(Node f t p s) -> case (del p, del s) of
  (Nothing, Nothing) -> Nothing
  (p', s')           -> Just $ Node f t p' s')
  where del (Just (_ :|: _)) = Nothing
        del other            = other
