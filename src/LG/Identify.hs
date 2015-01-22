module LG.Identify where
import LG.Graph
import qualified Data.Map as Map
import qualified Data.Set as Set

identifyNodes :: CompositionGraph -> [CompositionGraph]
identifyNodes g0 = map ((createGraph g0).Set.toList) compatibleSubsets
  where leafs = leafNodes g0
        possibleIdentifications = [(i,j) | i@(id1:@(Node iFormula _ iPrem iConc)) <- leafs,
                                        j@(id2:@(Node jFormula _ jPrem jConc)) <- leafs,
                                        not(i==j),
                                        (getName iFormula == getName jFormula) && not (getName iFormula == Nothing),--Select pairs with the same formula (polarity doesn't matter)
                                        (iPrem==Nothing && jConc==Nothing),--Select pairs that are not saturated
                                        not(iConc==jPrem)||iConc==Nothing--Don't match up atoms that are already connected with an axiom link
                                        ]
        compatibleSubsets = filter (isMaximalInRegardTo possibleSubsets) possibleSubsets
          where possibleSubsets = getCompatibleSubsets possibleIdentifications
                isMaximalInRegardTo [] set = True
                isMaximalInRegardTo (s2:xs) s1 = if s1 `Set.isProperSubsetOf` s2 then False else isMaximalInRegardTo xs s1
        getCompatibleSubsets nodes = map (Set.fromList . (map (\(id1:@_,id2:@_)->(id1,id2)))) (filter isCompatible (subsets nodes))
        isCompatible [] = True
        isCompatible ((i,j):xs) = not(occursInP i xs || occursInC j xs) && isCompatible xs
          where occursInP x [] = False
                occursInP x ((i,_):xs) = x==i||(occursInP x xs)
                occursInC x [] = False
                occursInC x ((_,j):xs) = x==j||(occursInC x xs)
        compatibleIdentifications _ [] acc = acc
        compatibleIdentifications (i1,j1) ((i2,j2):xs) acc = compatibleIdentifications (i1,j1) xs (if (i1/=i2 && j1/=j2 && i1/=j2 && i2/=j1) then ((i2,j2):acc) else acc)
        --createGraph :: CompositionGraph -> Set.Set (Occurrence NodeInfo, Occurrence NodeInfo) -> CompositionGraph
        createGraph g [] = g
        createGraph g (pair:ns) = createGraph g' ns
          where g' = (graphAfterIdentification pair g)

-- Completes an identification: id1 and id2 are removed from the graph, and linkMe1 and linkMe2 get a new axioma link:
--             * linkMe2
--             |                             * linkMe2
--             X id2                ->       |
-- X id1                                     * linkMe1
-- |
-- * linkMe1
--
-- Complexity: O(log n)
graphAfterIdentification :: (Identifier,Identifier) -> CompositionGraph -> CompositionGraph
graphAfterIdentification (id1,id2) g0 = g3
  where  newLink = Just (linkMe1:|:linkMe2)
         Just (Node _ _ Nothing (Just (linkMe1:|:_))) = Map.lookup id1 g0
         Just (Node _ _ (Just (_:|:linkMe2)) Nothing) = Map.lookup id2 g1
         g1 = setIsPremiseOf    newLink (referee linkMe1) g0
         g2 = setIsConclusionOf newLink (referee linkMe2) g1
         g3 = ((Map.delete id1).(Map.delete id2)) g2

-- Replaces premise of node in given map for given Identifier with given link. (Note: this does not check whether the given node id is *actually* a premise of the given link)
-- Complexity: O(log n)
setIsPremiseOf :: Maybe Link -> Identifier -> CompositionGraph -> CompositionGraph
setIsPremiseOf premOf id g = Map.insert id (Node f t premOf concOf) g
  where Just (Node f t _ concOf) = if Map.lookup id g == Nothing then error ((show id)++" not found") else Map.lookup id g 

-- Replaces conclusion of node in given map for given Identifier with given link. (Note: this does not check whether the given node id is *actually* a conclusion of the given link)
-- Complexity: O(log n)
setIsConclusionOf :: Maybe Link -> Identifier -> CompositionGraph -> CompositionGraph
setIsConclusionOf concOf id g = Map.insert id (Node f t premOf concOf) g
  where Just (Node f t premOf _) = Map.lookup id g

subsets :: [a] -> [[a]]
subsets [] = [[]]
subsets (x:xs) = (map (x:) y) ++ y
  where
    y = subsets xs

leafNodes :: CompositionGraph -> [Occurrence NodeInfo]
leafNodes g = map (\(id, occurrence)->id :@ occurrence) (Map.toList (Map.filter isLeafNode g))
  where isLeafNode (Node _ _ Nothing _) = True
        isLeafNode (Node _ _ _ Nothing) = True
        isLeafNode _ = False

getName (P (AtomP s)) = Just s
getName (N (AtomN s)) = Just s
getName _ = Nothing