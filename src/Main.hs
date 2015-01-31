module Main where
import LG.Graph
import LG.Unfold
import LG.Identify
import LG.Reductions
import LG.TestGraph
import LG.SubnetGraph
import qualified Lexicon as Lexicon
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List.Split
import Data.Char
import Data.Maybe
import Data.List
import System.Environment

main :: IO ()
main = do
  putStrLn "Enter sentence to prove:"
  sentence <- getLine
  stage0 sentence


-- Parsing
stage0 :: String -> IO ()
stage0 sentence = do
  case Lexicon.entries . wordsBy (not . isLetter) $ sentence of
    Just hypotheses -> stage1 hypotheses conclusionSentence
    Nothing         -> putStrLn "The expression was not recognised."


-- Unfolding
stage1 :: [Lexicon.Entry] -> [Lexicon.Entry] -> IO ()
stage1 hypotheses conclusion = do
  putStrLn $ show $ unfold hypotheses conclusion
  stage2 $ identifyNodes $ unfold hypotheses conclusion


-- Validation
stage2 :: [CompositionGraph] -> IO ()
stage2 gs = do
  putStrLn $ "There are " ++ show n ++ " ways to identify the hypotheses. Taking the first valid one.\n"
  (putStrLn . intercalate line . (\x -> [x]) . show . Proofnet . asProofnet) g
  putStrLn $ showReduction r
  stage3 [g]
  where g = head $ filter valid gs
        r = head $ reductions rules g
        n = length gs
        --g = gs!!4 bug for "John likes Mary"! *** Exception (reporting due to +RTS -xc): (THUNK_STATIC), stack trace: LG.Identify.graphAfterIdentification.linkMe2, ...


-- Term computation
stage3 :: [CompositionGraph] -> IO ()
stage3 gs = do
  putStrLn "The associated term(s) are:"
  putStrLn $ show $ map (termsFromProofnet g) ls
  where g  = head gs
        ls = links g


-- Generates possible proof structures for "(a/b)/b", as in Figure 15 of M&M (2012)
figure15 = g1
  where g0 = unfold (fromJust $ Lexicon.entries ["figure15"]) []
        g1 = identifyNodes g0


-- Generates possible proof structures for "sub tv det noun |- s", as in Figure 18 of M&M (2012)
figure18 = stage0 "sub tv det noun"


conclusionSentence :: [Lexicon.Entry]
conclusionSentence = fromJust $ Lexicon.entries ["s"]

line :: String
line = "\n------------------\n"


showReduction :: (CompositionGraph, [String]) -> String
showReduction (pn, history) = line ++ recount ++ show (Proofnet pn) ++ line ++ "\n\n"
  where recount = "Proof net found by application of the following rules:\n  initial -> "
                ++ intercalate " -> " (reverse history) ++ "\n\n"
