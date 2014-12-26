module Logic.ProofStructure
( ProofStructure,
 constructProofStructure,
 formulas,
 links,
 hypotheses
)
where
import qualified Logic.Link as Link

-- Moortgat & Moot 2012:
--   *Definition 2.2.* A proof structure <S, L> is a finite set of formula occurrences S
--   and a set of links L [...] such that
--   • each formula is at most once the premise of a link,
--   • each formula is at most once the conclusion of a link

-- Inductive constructor for a proof structure:
-- TODO experiment if this works better than the set approach
data ProofStructureInd f = Empty | Structure (Link.Link f) (ProofStructureInd f) deriving (Show)

-- Constructor for a proof structure using lists:
data ProofStructure f = ProofStructure {formulas :: [f], links :: [Link.Link f]} deriving (Show, Eq)

-- TODO formulas and links arrays must be sets...
-- TODO is it legal for formulas to contain formulas that are not represented in the links? (I guess so)
constructProofStructure :: (Eq f) => [f] -> [Link.Link f] -> ProofStructure f
constructProofStructure formulas links =
   if formulas `allOccurAtMostOnce` linkPremises && formulas `allOccurAtMostOnce` linkConclusions
   then ProofStructure formulas links -- Construct proof structure if it is well formed
   else error "Each formula should be at most once the premise of a link and at most once the conclusion of a link"
   where
     linkPremises = Link.getAllPremises links
     linkConclusions = Link.getAllConclusions links

     countIs1OrLess :: (Eq f) => f -> [f] -> Int->Bool
     countIs1OrLess _ [] _ = True
     countIs1OrLess f1 (f2:formulas) count =
       if f1 == f2
       then if count >=1
            then False
            else countIs1OrLess f1 formulas (count+1)
       else countIs1OrLess f1 formulas count

     allOccurAtMostOnce :: (Eq f) => [f] -> [f] -> Bool
     allOccurAtMostOnce [] links = True
     allOccurAtMostOnce (f:formulas) linkFormulas =
       if countIs1OrLess f linkFormulas 0
       then allOccurAtMostOnce formulas linkFormulas
       else False

-- M&M 2012, p7: "Formulas which are not the conclusion of any link are called the hypotheses
-- of the proof structure."
hypotheses :: (Eq f)=> ProofStructure f -> [f]
hypotheses s = getProofHypotheses (formulas s)
  where
   getProofHypotheses = foldl (addIfNotConclusion (links s)) []
   addIfNotConclusion :: (Eq f) => [Link.Link f] -> [f] -> f -> [f]
   addIfNotConclusion links acc formula =
     if not (formula `Link.isConclusionOfAnyLink` links)
     then (formula:acc)
     else acc


-- M&M 2012, p7: "Formulas which are not the premise of any link are called
-- the conclusions of the proof structure."
conclusions :: (Eq f)=> ProofStructure f -> [f]
conclusions s = getProofConclusions (formulas s)
  where
   getProofConclusions = foldl (addIfNotPremise (links s)) []
   addIfNotPremise :: (Eq f) => [Link.Link f] -> [f] -> f -> [f]
   addIfNotPremise links acc formula =
     if not (formula `Link.isPremiseOfAnyLink` links)
     then (formula:acc)
     else acc



