module Main where
import LG.Graph
import LG.Unfold
import LG.Identify
import LG.Reductions
import LG.TestGraph
import qualified Lexicon as Lexicon
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List.Split
import Data.Char
import Data.Maybe
import Data.List

main :: IO ()
main = let r = reductions rules testGraph
       in if length r > 0
          then putStrLn $ showReduction $ head r
          else putStrLn $ "Does not reduce to a tree."


line :: String
line = "\n------------------\n"

showReduction :: (CompositionGraph, [String]) -> String
showReduction (pn, history) = line ++ recount ++ show (Proofnet pn) ++ line ++ "\n\n"
  where recount = "Proof net found by application of the following rules:\n  initial -> "
                ++ intercalate " -> " (reverse history) ++ "\n\n"



{-
main = do
    (putStrLn . show) (getPossibleProofStructures "John likes Mary")
-}

proveSentence string = proofs
  where proofStructures = getPossibleProofStructures string
        proofs = proofStructures -- TODO filter out those structures that are not nets

getPossibleProofStructures string = unfoldedGraph
  where words = ((wordsBy (not . isLetter)) string)
        hypotheses  = Lexicon.entries words
        conclusions = Lexicon.entries ["s"]
        unfoldedGraph = unfold hypotheses conclusions
        proofStructures = ((map collapseAxiomLinks) . identifyNodes) unfoldedGraph

-- Generates possible proof structures for "(a/b)/b", as in Figure 15 of M&M (2012)
figure15 = g1
  where g0 = unfold (Lexicon.entries ["figure15"]) []
        g1 = identifyNodes g0

-- Generates possible proof structures for "sub tv det noun |- s", as in Figure 18 of M&M (2012)
figure18 = getPossibleProofStructures "sub tv det noun"
