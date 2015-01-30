module LG.Graph where

import Data.List
import Data.Maybe
import qualified Data.Map as Map

import LG.Base
import LG.Term


--------------------------------------------------------------------------------
-- Links & tentacles

--           premises       succedents
data Link = [Tentacle] :○: [Tentacle]  -- Tensor
          | [Tentacle] :●: [Tentacle]  -- Cotensor
          |  Tentacle  :|:  Tentacle   -- Axioma
          deriving (Eq, Ord, Show)

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


mainFormula :: Link -> Maybe Tentacle
mainFormula (ts :○: tt) = maybe (findMain tt) Just (findMain ts)
mainFormula (ts :●: tt) = maybe (findMain tt) Just (findMain ts)
mainFormula (_  :|: _ ) = Nothing


premises, succedents, tentacles :: Link -> [Tentacle]
premises   (ts :○: _ ) = ts
premises   (ts :●: _ ) = ts
premises   (t  :|: _ ) = [t]
succedents (_  :○: ts) = ts
succedents (_  :●: ts) = ts
succedents (_  :|: t ) = [t]
tentacles link = premises link ++ succedents link


prem, conc :: Link -> [Identifier]
prem = map referee . premises
conc = map referee . succedents


-- Partition the nodes of an interconnected set of links into those at the
-- hypothesis end, those 'inside' the links structure and those at the
-- conclusion end, respectively
sift :: [Link] -> ([Identifier], [Identifier], [Identifier])
sift ls = (p \\ s, p `intersect` s, s \\ p)
  where all' = flip concatMap ls
        p    = all' prem
        s    = all' conc

--------------------------------------------------------------------------------
-- Dual link representation: separate main from active, annotate
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


--------------------------------------------------------------------------------
-- Nodes

data NodeInfo = Node { formula     :: Formula
                     , term        :: NodeTerm
                     , premiseOf   :: Maybe Link
                     , succedentOf :: Maybe Link
                     }
              deriving (Eq, Show)


-- Change the link above or below a node
(⤴) , (⤵) :: Maybe Link -> NodeInfo -> NodeInfo
new ⤴ Node f t p _ = Node f t p new
new ⤵ Node f t _ s = Node f t new s


--------------------------------------------------------------------------------
-- Graph querying

type CompositionGraph = Map.Map Identifier NodeInfo

hypotheses :: CompositionGraph -> [Identifier]
hypotheses = Map.keys . Map.filter (isNothing . succedentOf)

conclusions :: CompositionGraph -> [Identifier]
conclusions = Map.keys . Map.filter (isNothing . premiseOf)


-- Get all links inside a graph by enumerating all links under each node that is
-- the first premise of a link. Assumes that all links have at least one
-- tentacle leading up!
links :: CompositionGraph -> [Link]
links = Map.elems . Map.mapMaybeWithKey spotByRepresentative where
  first                    = fmap (head . prem) . premiseOf
  spotByRepresentative k n = if first n == Just k then premiseOf n else Nothing


-- Find out to what link some node is a premise (downlink) / succedent (uplink)
downlink, uplink :: Identifier -> CompositionGraph -> Maybe Link
downlink k g = premiseOf   $ g Map.! k
uplink   k g = succedentOf $ g Map.! k


-- Naive (?) cycle detection
cyclic :: CompositionGraph -> Bool
cyclic g | Map.null g     = False
         | otherwise      = cyclic' up   [] [first] &&
                            cyclic' down [] [first] where
  first                   = head $ Map.keys g
  up k                    = maybe [] prem $ uplink   k g
  down k                  = maybe [] conc $ downlink k g
  cyclic' xplr seen (x:q) | x `elem` seen = True
                          | otherwise     = cyclic' xplr (x:seen) (xplr x++q)
  cyclic' _       _    [] = False


-- Is our graph a tree? For now, we just disregard connectedness
isTree :: CompositionGraph -> Bool
isTree = not . cyclic


--------------------------------------------------------------------------------
-- Graph manipulation

-- Function that inserts nodes at given ids, overwriting any pre-existing mappings
-- Complexity: O(m*(log (n+m))), for m is the number of nodes being added and n is the number of nodes in the graph
insertNodes ::  [Occurrence NodeInfo] -> CompositionGraph -> CompositionGraph
insertNodes [] graph = graph
insertNodes ((id :@ formula):nodes) graph = insertNodes nodes (Map.insert id formula graph)


-- Delete all given nodes from a graph. Mind any other refs!
kill :: [Identifier] -> CompositionGraph -> CompositionGraph
kill = flip $ foldl' $ flip Map.delete


-- Update the referred nodes using the given node transformer. Mind other refs!
adjust :: (NodeInfo -> NodeInfo) ->
          [Identifier] -> CompositionGraph -> CompositionGraph
adjust f = flip $ foldl' $ flip $ Map.adjust f


-- Remove/add the succedentOf/premiseOf link references to the nodes of a graph.
-- Makes use of a helper function that simply updates all nodes that are
-- referred to in some (hypothetical) link to either actually refer to such a
-- link or to put Nothings in its place
connect, disconnect :: [Link] -> CompositionGraph -> CompositionGraph
connect          = install Just
disconnect       = install (const Nothing)
install presence = flip $ foldl' (\g l -> adjust (presence l ⤴) (conc l)
                                        $ adjust (presence l ⤵) (prem l) g)

--------------------------------------------------------------------------------
-- Show instance

newtype Proofnet = Proofnet CompositionGraph

instance Show Proofnet where
  show (Proofnet g) = intercalate "\n\n" $ map (showLink g) $ links g

layout :: Int -> [String] -> String
layout width = intercalate "\n" . map (center width)

pad, center :: Int -> String -> String
center n s = let m = (n - length s) `div` 2
                 p = take m $ repeat ' '
             in take n $ p ++ s ++ repeat ' '

pad n s = let m = (n - length s)
          in take m $ repeat ' '

showTentacles :: CompositionGraph -> Link -> (Int, String, String)
showTentacles g link = (width, top', bottom') where
  top'          = showNs $ nodes $ prem link
  bottom'       = showNs $ nodes $ conc link
  width         = max (length top') (length bottom') + 2
  nodes         = map (\k -> show $ (k :@) $ formula $ g Map.! k)
  showNs (x:xs) = let n = maximum $ map length (x:xs)
                  in intercalate "   " $ ((pad n x ++ x):map (\x -> x ++ pad n x) xs)


showLink :: CompositionGraph -> Link -> String
showLink g l@([a, b] :○: [c]) = let (w, top, bottom) = showTentacles g l
  in layout w [top, [arlup a, ' ', arrup b], "○", [arsdn c], bottom]
showLink g l@([a] :○: [b, c]) = let (w, top, bottom) = showTentacles g l
  in layout w [top, [arsup a], "○", [arldn b, ' ', arrdn c], bottom]
showLink g l@([a, b] :●: [c]) = let (w, top, bottom) = showTentacles g l
  in layout w [top, [arlup a, ' ', arrup b], "●", [arsdn c], bottom]
showLink g l@([a] :●: [b, c]) = let (w, top, bottom) = showTentacles g l
  in layout w [top, [arsup a], "●", [arldn b, ' ', arrdn c], bottom]
showLink g l@(a :|: b) = let (w, top, bottom) = showTentacles g l
  in layout w [top, "|", "|", "|", bottom]
showLink _ l = show l

arsup,arlup,arrup,arsdn,arldn,arrdn :: Tentacle -> Char
arsup (MainT  _) = '↑'
arsup (Active _) = '|'
arlup (MainT  _) = '↖'
arlup (Active _) = '\\'
arrup (MainT  _) = '↗'
arrup (Active _) = '/'
arsdn (MainT  _) = '↓'
arsdn (Active _) = '|'
arldn (MainT  _) = '↙'
arldn (Active _) = '/'
arrdn (MainT  _) = '↘'
arrdn (Active _) = '\\'
