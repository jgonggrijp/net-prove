module Main where
import LG.Graph
import LG.Unfold
import LG.Identify
import Data.IORef
import qualified Data.Map as Map
import qualified Data.Set as Set

insertNodes ::  [Occurrence NodeInfo] -> CompositionGraph -> CompositionGraph
insertNodes [] graph = graph
insertNodes ((id :@ formula):ns) graph = insertNodes ns (Map.insert id formula graph)

main = do
    (putStrLn . show) figure18

figure15 = g1
  where f = P( N ( P (AtomP "a"):/:P (AtomP "b")):<×>: (P (AtomP "b")))
        (id, nodes, c) = unfoldHypothesis f "f" 0
        g1 = identifyNodes (insertNodes nodes Map.empty)

figure18 = g1s
  where sub = P ((N ((P (AtomP "np")):/:(P (AtomP "n")))):<×>: (P (AtomP "n")))
        tv  = N (N ((P (AtomP "np")):\:(P (AtomP "s"))):/:(P (AtomP "np")))
        det = N ((P (AtomP "np")):/:(P (AtomP "n")))
        noun = P (AtomP "n")
        goal = N (AtomN "s")
        (sbId, nodes1, count1) = unfoldHypothesis sub "mary" 0
        (tvId, nodes2, count2) = unfoldHypothesis tv "likes" count1
        (dtId, nodes3, count3) = unfoldHypothesis det "the" count2
        (nnId, nodes4, count4) = unfoldHypothesis noun "horse" count3
        (glId, nodes5, count5) = unfoldHypothesis goal "!" count4
        g0 = (insertNodes nodes1 . insertNodes nodes2 . insertNodes nodes3 . insertNodes nodes4 . insertNodes nodes5) Map.empty
        g1s = ((map collapseAxiomLinks) . identifyNodes) g0

exampleGraph = g2
  where
    g0 = Map.empty
    f =  P (N (P (AtomP "B") :/: P (AtomP "A")) :<×>: P (AtomP "C"))
    idLink = (Active 0) :|: (Active 1)
    nodeInfo :: NodeInfo
    nodeInfo = Node f (Va (Variable "0")) (Just idLink) Nothing
    g1 = insertNodes [0 :@ nodeInfo] g0
    g2 = unfoldHypothesis f "f" 0