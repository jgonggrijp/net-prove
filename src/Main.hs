module Main where
import LG.Graph
import LG.Unfold
import LG.Identify
import qualified Lexicon as Lexicon
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List.Split
import Data.Char

main = do
    (putStrLn . show) (getPossibleProofStructures "John likes Mary")

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
