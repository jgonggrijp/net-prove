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
    (putStrLn . show) (proveSentence "John likes Mary")


proveSentence string = g
  where words = ((wordsBy (not . isLetter)) string)
        hypotheses  = Lexicon.entries words
        conclusions = Lexicon.entries ["s"]
        g = unfold hypotheses conclusions

-- Generates possible proof structures for "(a/b)/b", as in Figure 15 of M&M (2012)
figure15 = g1
  where (id, nodes, c) = unfoldHypothesis (Lexicon.lookup "figure15") 0
        g1 = identifyNodes (insertNodes nodes Map.empty)

-- Generates possible proof structures for "sub tv det noun |- s", as in Figure 18 of M&M (2012)
figure18 = proofStructures
  where graph = unfold (Lexicon.entries ["sub", "tv", "det", "noun"]) (Lexicon.entries ["s"])
        -- Identify atomic nodes and collapse axiom links. We now have an array of proof structures which might or might not be proof nets.
        proofStructures = ((map collapseAxiomLinks) . identifyNodes) graph


