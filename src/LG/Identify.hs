module LG.Identify (identifyNodes) where
import LG.Base
import LG.Term
import LG.Graph
import LG.Base
import LG.Term
import qualified Data.Map as Map
import qualified Data.Set as Set

-- A (simple) identification contains two references to a node: one will be the
-- premise of the axiom link; the other the conclusion.
type Identification = (Identifier, Identifier)

-- An IdentificationProfile is a set of identifications, representing all
-- identifications that will happen in one contingent universe for the
-- given composition graph.
type IdentificationProfile = Set.Set Identification

-- A verbose identification contains information not just about which two nodes
-- identify, but also the graphs they are in
type VerboseIdentification = ((CompositionGraph, LeafNode), (CompositionGraph, LeafNode))


fromVerboseIdentifications :: [VerboseIdentification] -> [Identification]
fromVerboseIdentifications = map fromVerboseIdentification

fromVerboseIdentification :: VerboseIdentification -> Identification
fromVerboseIdentification ((_, Leaf (id1:@_)), (_, Leaf (id2:@_))) = (id1, id2)


-- identifyNodes is used to identify leaf nodes in a composition graph in a maximal way,
-- that is: all possible combinations of identification are tried out, exhaustively.
--
-- See M&M, p. 7: "We obtain a proof structure of (s </> s) <\> np ⇒ s / (np \ s) by
-- identifying atomic formulas"
--
-- Note that the returned composition graphs are not guaranteed to be proof nets, only
-- guaranteed to have no more possibilities of identifying leaf nodes!
--
-- (TODO: fix this) Also note that this function does not take node order into account,
-- and so will produce a proof net for 'mary likes john' as well as 'john likes mary' if
-- they're both of the form 'np <x> (np\s)/np<x> np'.
--
-- Input :  A (ordered) list of input formulas that corresponds to the order of words. Node identifiers must not clash.
-- Output:  A list of composition graphs in which the atomic nodes of the input graphs are connected maximally
identifyNodes :: [CompositionGraph] -> [CompositionGraph]
identifyNodes subgraphs = Set.toList (Set.map (identifyNodes' (Map.unions subgraphs)) identificationProfiles)
  where identificationProfiles = Set.map Set.toList (generateIdentificationProfiles subgraphs)

-- Function that recursively applies node identifications to a composition graph
--
-- Input:  A composition graph and a list of identifications. An identification is a pair of node identifiers.
-- Output: Composition graph with all node identifications applied to it
identifyNodes' graph []         = graph
identifyNodes' graph (identification:xs) = identifyNodes' (graphAfterIdentification identification graph) xs

-- Completes an identification: id1 and id2 are removed from the graph, and linkMe1 and linkMe2
-- get a new axioma link between them:
--
--             * linkMe2
--             |                             * linkMe2
--             X id2                ->       |
-- X id1                                     * linkMe1
-- |
-- * linkMe1
--
-- Note that axiom link collapse (M&M, p. 23: Def 3.2; bullet 3) happens implicitly in this
-- function as id1 and id2 are removed from the graph.
--
-- Complexity: O(log n)
graphAfterIdentification :: Identification -> CompositionGraph -> CompositionGraph
graphAfterIdentification (id1,id2) g0 = g3
  where  newLink = Just (linkMe1:|:linkMe2)
         Just (Node _ _ Nothing (Just (linkMe1:|:_))) = Map.lookup id1 g0
         Just (Node _ _ (Just (_:|:linkMe2)) Nothing) = Map.lookup id2 g1
         g1 = setIsPremiseOf    newLink (referee linkMe1) g0
         g3 = ((Map.delete id1).(Map.delete id2)) g2
         g2 = setIsConclusionOf newLink (referee linkMe2) g1



-- Input : A (ordered) list of input formulas that corresponds to the order of words. Node identifiers must not clash.
-- Output: Set of sets of possible node identifications that guarantee that the merged graph will be connected
generateIdentificationProfiles :: [CompositionGraph] -> Set.Set IdentificationProfile
generateIdentificationProfiles subgraphs = maximalProfiles
  where subgraphLeafNodes = map (\g -> (g, leafNodes g)) subgraphs
        allPairings         = generateIdentifications subgraphLeafNodes -- Gives us a list of pairing for every leaf node.
        allProfiles         = getProfilesFromPossiblePairings allPairings
        validProfiles       = getValidProfiles subgraphs allProfiles
        validSimpleProfiles = map (Set.fromList . fromVerboseIdentifications) validProfiles
        maximalProfiles     = Set.fromList $ filter (isMaximalInRegardTo validSimpleProfiles) validSimpleProfiles -- Filter out profiles that are strict subsets of other profiles


-- TODO we might be able to make this more efficient by clustering
-- our VerboseIdentifications per Node, so that in this function we
-- don't generate profiles where a node occurs more than once as
-- the premise/conclusion in the identification profile, but that
-- would make our code so much more complex.
getProfilesFromPossiblePairings :: [VerboseIdentification] -> [[VerboseIdentification]]
getProfilesFromPossiblePairings = subsets

-- Filter identification profiles to those that are valid.
getValidProfiles :: [CompositionGraph] -> [[VerboseIdentification]] -> [[VerboseIdentification]]
getValidProfiles graphs = filter (isValidProfile graphs)

-- A profile is valid if:
--  - The resulting graph is connected
--  - Across all identifications, nodes are at most once the premise and at most once the conclusion of the axiom link
isValidProfile :: [CompositionGraph] -> [VerboseIdentification] -> Bool
isValidProfile graphs profile =
  allGraphsAreTouched (Set.fromList graphs) profile &&
  hasNoDuplicates (fromVerboseIdentifications profile)

hasNoDuplicates :: [Identification] -> Bool
hasNoDuplicates [] = True
hasNoDuplicates ((id1,id2):idts) =
  isNotId1 id1 idts &&
  isNotId2 id2 idts &&
  hasNoDuplicates idts
  where isNotId1 _ [] = True
        isNotId1 id ((jd,_):xs) = if id == jd then False else isNotId1 id xs
        isNotId2 _ [] = True
        isNotId2 id ((_,jd):xs) = if id == jd then False else isNotId2 id xs

allGraphsAreTouched :: Set.Set CompositionGraph -> [VerboseIdentification] -> Bool
allGraphsAreTouched graphSet profile =
   ((length commonTerritories) == 1) && ((commonTerritories !! 0) == graphSet)
    where
        graphTerritories = map (\(g1,g2)->Set.fromList [g1,g2]) $ map getGraphPair profile
        commonTerritories = amassCommonTerritory graphTerritories []


-- Returns just the graphs from a verbose identification
getGraphPair :: VerboseIdentification -> (CompositionGraph, CompositionGraph)
getGraphPair ((g1, _), (g2, _)) = (g1, g2)



amassCommonTerritory (p1:p2:ps) noMatch =
  if (Set.intersection p1 p2) /= Set.empty
  then amassCommonTerritory ((Set.union p1 p2):noMatch) [] --Start over with new union
  else amassCommonTerritory (p2:ps) (p1:noMatch)
amassCommonTerritory commonTerritories noMatch = commonTerritories++noMatch




type LeafSubgraph = (CompositionGraph, [LeafNode])

-- This function gives us back all possible pairings of leaf nodes.
-- Note that a - b and b - a duplicates are weeded out in `getPossIdsForLeafWith`: we only get id1 is the upper and id2 the lower.
generateIdentifications :: [LeafSubgraph] -> [VerboseIdentification]
generateIdentifications leafGraphs = generateIdentifications' isolatedNodes leafGraphs []
  where isolatedNodes = map isolateNodesForGraph leafGraphs
        isolateNodesForGraph (g, ns) = map (\x->(g,x)) ns

generateIdentifications' :: [[(CompositionGraph, LeafNode)]]
     -> [LeafSubgraph]
     -> [VerboseIdentification]
     -> [VerboseIdentification]
generateIdentifications' []                     _        acc = reverse acc
generateIdentifications' (subgraphLeafNodes:ns) allLeafs acc = generateIdentifications' ns allLeafs (a++acc)
  where a = getPossIdsForLeafs subgraphLeafNodes allLeafs []

getPossIdsForLeafs []     _            acc = reverse acc
getPossIdsForLeafs ((c1, l):ls) allLeafNodes acc = getPossIdsForLeafs ls allLeafNodes (possibilities++acc)
  where possibilities = getPossIdsForLeaf (c1, l) allLeafNodes []

getPossIdsForLeaf :: (CompositionGraph, LeafNode) -> [(CompositionGraph, [LeafNode])] -> [VerboseIdentification] -> [VerboseIdentification]
getPossIdsForLeaf _          []                      acc = reverse acc
getPossIdsForLeaf leaf ((c2, otherLeafs):rest) acc = getPossIdsForLeaf leaf rest (possibilities++acc)
  where possibilities = leaf `getPossIdsForLeafWith` (c2, otherLeafs)

getPossIdsForLeafWith :: (CompositionGraph, LeafNode) -> (CompositionGraph, [LeafNode]) -> [VerboseIdentification]
getPossIdsForLeafWith (c1, (leaf@(Leaf (id1:@(Node formula1 _ downlink1 uplink1))))) (c2, otherLeafs) =
        [((c1, leaf), (c2, otherLeaf)) | otherLeaf@(Leaf (id2:@(Node formula2 _ downlink2 uplink2))) <- otherLeafs,
                            leaf/=otherLeaf,                                             -- We can't identify exactly the same node
                            sameName formula1 formula2,                                  -- Select pairs with the same formula (polarity doesn't matter)
                            downlink1 == Nothing && uplink2 == Nothing,                  -- Select pairs that are not saturated
                            if uplink1/=Nothing then not(uplink1 == downlink2) else True -- Don't match up atoms that are already connected with an axiom link
        ]










-- Replaces premise of node in given map for given Identifier with given link. (Note: this does not check whether the given node id is *actually* a premise of the given link)
--
-- Complexity: O(log n)
setIsPremiseOf :: Maybe Link -> Identifier -> CompositionGraph -> CompositionGraph
setIsPremiseOf premOf id g = Map.insert id (Node f t premOf concOf) g
  where Just (Node f t _ concOf) = if Map.lookup id g == Nothing then error ((show id)++" not found") else Map.lookup id g

-- Replaces conclusion of node in given map for given Identifier with given link. (Note: this does not check whether the given node id is *actually* a conclusion of the given link)
--
-- Complexity: O(log n)
setIsConclusionOf :: Maybe Link -> Identifier -> CompositionGraph -> CompositionGraph
setIsConclusionOf concOf id g = Map.insert id (Node f t premOf concOf) g
  where Just (Node f t premOf _) = Map.lookup id g







-- Return the name of an atomic formula
getNameOfAtomicFormula (P (AtomP s)) = Just s
getNameOfAtomicFormula (N (AtomN s)) = Just s
getNameOfAtomicFormula _ = Nothing

-- Returns whether node a and b are both atomic and have the same formula name
sameName a b = (aName == bName) && (aName /= Nothing)
  where aName = getNameOfAtomicFormula a
        bName = getNameOfAtomicFormula b









-- NOTE: this function is not correct: it should leave the main formula intact, while deleting the active
-- formula. This is not always the case. Currently, we ignore this function because it is not needed for
-- any of the following steps. (Validation collapses *all* axiom links anyway and it's an extra complication
-- for term labeling.)
--
-- See M&M, p. 23: "all axiom links connecting terms of the same type (value or context) are collapsed."
collapseAxiomLinks :: CompositionGraph -> CompositionGraph
collapseAxiomLinks g = collapseConclusionLinks (((map (\(Node _ _ _ l)->l)) . (filter isAxiomConclusion) . Map.elems) g) g
  where isAxiomConclusion (Node _ _ _ (Just (_ :|: _))) = True
        isAxiomConclusion _ = False
        collapseConclusionLinks :: [Maybe Link] -> CompositionGraph -> CompositionGraph
        collapseConclusionLinks [] g = g
        collapseConclusionLinks (Just (Active id1 :|: Active id2):xs) g0 = if sameTermTypes t1 t2 then g1 else g
          where Just (Node f1 t1 premOf1 concOf1) = Map.lookup id1 g0
                Just (Node f2 t2 premOf2 concOf2) = Map.lookup id2 g0
                newNode = (Node f1 t1 premOf2 concOf1)
                sameTermTypes (Ev _) (Ev _) = True
                sameTermTypes (Va _) (Va _) = True
                sameTermTypes _ _ = False
                g1 :: CompositionGraph
                g1 = ((replaceIdInConclusion id2 id1 premOf2) . (Map.insert id1 newNode) . (Map.delete id2) . (Map.delete id1)) g0
                replaceIdInConclusion :: Identifier -> Identifier -> Maybe Link -> CompositionGraph -> CompositionGraph
                replaceIdInConclusion _ _ Nothing g = g
                replaceIdInConclusion replaceMe withMe (Just l) g = replaceIdInConclusion' replaceMe withMe (map referee (succedents l)) g
                replaceIdInConclusion' replaceMe withMe [] g = g
                replaceIdInConclusion' replaceMe withMe (id:xs) g0 = g1
                  where Just (Node f t premOf (Just link)) = Map.lookup id g0
                        g1 = Map.insert id newNode g0
                        newNode = (Node f t premOf (Just (replaceInLink replaceMe withMe link)))
                        replaceInLink :: Identifier -> Identifier -> Link -> Link
                        replaceInLink replaceMe withMe (prems :○: concs) = (replaceInList replaceMe withMe prems) :○: (replaceInList replaceMe withMe concs)
                        replaceInLink replaceMe withMe (prems :●: concs) = (replaceInList replaceMe withMe prems) :○: (replaceInList replaceMe withMe concs)
                        replaceInLink replaceMe withMe (prem :|: conc) = p :|: c
                          where p = if replaceMe==(referee prem) then (Active withMe) else prem
                                c = if replaceMe==(referee conc) then (Active withMe) else conc
                        replaceInList replaceMe withMe inList = map replaceIdInTentance inList
                        replaceIdInTentance t@(Active x) = if x==replaceMe then Active withMe else t
                        replaceIdInTentance t@(MainT x) = if x==replaceMe then MainT withMe else t

-------------
-- SET UTILS
-------------
-- NOTE: I can't decide whether to put these functions in another module

-- Generates all subsets of a given list
subsets :: [a] -> [[a]]
subsets [] = [[]]
subsets (x:xs) = (map (x:) y) ++ y
  where y = subsets xs

-- Returns whether s1 is a maximal subset in regards to all other
-- sets, that is, whether s1 is not a proper subset of any other
-- set.
isMaximalInRegardTo [] _ = True
isMaximalInRegardTo (s2:xs) s1 = if s1 `Set.isProperSubsetOf` s2 then False else isMaximalInRegardTo xs s1