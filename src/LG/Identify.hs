module LG.Identify where
import LG.Base
import LG.Term
import LG.Graph
import Lexicon
import qualified Data.Map as Map
import qualified Data.Set as Set

-- Generates all subsets of a given list
subsets :: [a] -> [[a]]
subsets [] = [[]]
subsets (x:xs) = (map (x:) y) ++ y
  where
    y = subsets xs

-- identifyNodes is used to identify atomic nodes in a composition graph in a maximal way, that is: all possible combinations are tried out, exhaustively.
-- See M&M, p. 7: "We obtain a proof structure of (s </> s) <\> np ⇒ s / (np \ s) by identifying atomic formulas"
-- Note that the returned composition graphs are not guaranteed to be proof nets, only guaranteed to have no more possibilities of identifying atomic formula nodes!
-- Also note that this function does not take node order into account, and so will produce a proof net for 'mary likes john' as well as 'john likes mary' if they're both of the form 'np <x> (np\s)/np<x> np'.
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
--
--             * linkMe2
--             |                             * linkMe2
--             X id2                ->       |
-- X id1                                     * linkMe1
-- |
-- * linkMe1
--
-- Note that axiom link collapse (M&M, p. 23: Def 3.2; bullet 3) happens implicitly in this function.
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

-- Return all leaf nodes for given composition graph
-- Complexity: O(n)
leafNodes :: CompositionGraph -> [Occurrence NodeInfo]
leafNodes g = map (\(id, occurrence)->id :@ occurrence) (Map.toList (Map.filter isLeafNode g))
  where isLeafNode (Node _ _ Nothing _) = True
        isLeafNode (Node _ _ _ Nothing) = True
        isLeafNode _ = False

-- Return the name of an atomic formula
getName (P (AtomP s)) = Just s
getName (N (AtomN s)) = Just s
getName _ = Nothing

-- See M&M, p. 23: "all axiom links connecting terms of the same type (value or context) are collapsed."
collapseAxiomLinks :: CompositionGraph -> CompositionGraph
collapseAxiomLinks g = collapseConclusionLinks (((map (\(Node _ _ _ l)->l)) . (filter isAxiomConclusion) . Map.elems) g) g
  where isAxiomConclusion (Node _ _ _ (Just (_ :|: _))) = True
        isAxiomConclusion _ = False
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
                replaceIdInConclusion _ _ Nothing g = g
                replaceIdInConclusion replaceMe withMe (Just l) g = replaceIdInConclusion' replaceMe withMe (succedents l) g
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