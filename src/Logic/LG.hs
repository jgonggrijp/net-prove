module Logic.LG where

import qualified Data.Set as Set

data LinkType = Tensor | Cotensor deriving (Eq, Ord)
data LinkMode = Fusion | Fission deriving (Eq, Ord)
data LinkMain = LeftT | RightT | ThirdT deriving (Eq, Ord)

data Link = Link {
    linkType :: LinkType,
    linkMode :: LinkMode,
    linkMain :: LinkMain,
    left :: Node,
    right :: Node,
    third :: Node } deriving (Eq, Ord)

premises :: Link -> [Node]
premises (Link Tensor   Fusion  _ a b _) = [a, b]
premises (Link Cotensor Fusion  _ _ _ c) = [c]
premises (Link Tensor   Fission _ _ _ c) = [c]
premises (Link Cotensor Fission _ a b _) = [a, b]

succedents :: Link -> [Node]
succedents (Link Tensor   Fusion  _ _ _ c) = [c]
succedents (Link Cotensor Fusion  _ a b _) = [a, b]
succedents (Link Tensor   Fission _ a b _) = [a, b]
succedents (Link Cotensor Fission _ _ _ c) = [c]

mainNode :: Link -> Node
mainNode (Link _ _ LeftT  a _ _) = a
mainNode (Link _ _ RightT _ b _) = b
mainNode (Link _ _ ThirdT _ _ c) = c

data Node = Node {
    formula :: Formula,
    premiseLink :: Maybe Link,
    succedentLink :: Maybe Link } deriving (Eq, Ord)

type ProofStructure = Set.Set Node

hypotheses :: ProofStructure -> Set.Set Node
hypotheses = Set.filter ((== Nothing) . succedentLink)

conclusions :: ProofStructure -> Set.Set Node
conclusions = Set.filter ((== Nothing) . premiseLink)

data Atom = NP | N | S deriving (Eq, Ord)

data Formula = Atomic Atom
    | Formula :*: Formula
    | Formula :\\ Formula
    | Formula :// Formula
    | Formula :+: Formula
    | Formula :-\ Formula
    | Formula :-/ Formula
    deriving (Eq, Ord)

unfoldHypothesis :: Formula -> Node
unfoldHypothesis = unfoldHypothesis' Nothing

unfoldHypothesis' :: Maybe Link -> Formula -> Node
unfoldHypothesis' k f@(Atomic a) = Node f Nothing k
unfoldHypothesis' k f@(g :*: h)  = third
  where link = Link Cotensor Fusion ThirdT left right third
        left = unfoldHypothesis' (Just link) g
        right = unfoldHypothesis' (Just link) h
        third = Node f (Just link) k
unfoldHypothesis' k f@(g :\\ h)  = right
  where link = Link Tensor Fusion RightT left right third
        left = unfoldConclusion' (Just link) g
        right = Node f (Just link) k
        third = unfoldHypothesis' (Just link) h
unfoldHypothesis' k f@(g :// h)  = left
  where link = Link Tensor Fusion LeftT left right third
        left = Node f (Just link) k
        right = unfoldHypothesis' (Just link) h
        third = unfoldConclusion' (Just link) g
unfoldHypothesis' k f@(g :+: h)  = third
  where link = Link Tensor Fission ThirdT left right third
        left = unfoldHypothesis' (Just link) g
        right = unfoldHypothesis' (Just link) h
        third = Node f (Just link) k
unfoldHypothesis' k f@(g :-\ h)  = right
  where link = Link Cotensor Fission RightT left right third
        left = unfoldConclusion' (Just link) g
        right = Node f (Just link) k
        third = unfoldHypothesis' (Just link) h
unfoldHypothesis' k f@(g :-/ h)  = left
  where link = Link Cotensor Fission LeftT left right third
        left = Node f (Just link) k
        right = unfoldHypothesis' (Just link) h
        third = unfoldConclusion' (Just link) g

unfoldConclusion :: Formula -> Node
unfoldConclusion = unfoldConclusion' Nothing

unfoldConclusion' :: Maybe Link -> Formula -> Node
unfoldConclusion' k f@(Atomic a) = Node f k Nothing
unfoldConclusion' k f@(g :*: h)  = third
  where link = Link Tensor Fusion ThirdT left right third
        left = unfoldConclusion' (Just link) g
        right = unfoldConclusion' (Just link) h
        third = Node f k (Just link)
unfoldConclusion' k f@(g :\\ h)  = right
  where link = Link Cotensor Fusion RightT left right third
        left = unfoldHypothesis' (Just link) g
        right = Node f k (Just link)
        third = unfoldConclusion' (Just link) h
unfoldConclusion' k f@(g :// h)  = left
  where link = Link Cotensor Fusion LeftT left right third
        left = Node f k (Just link)
        right = unfoldConclusion' (Just link) h
        third = unfoldHypothesis' (Just link) g
unfoldConclusion' k f@(g :+: h)  = third
  where link = Link Cotensor Fission ThirdT left right third
        left = unfoldConclusion' (Just link) g
        right = unfoldConclusion' (Just link) h
        third = Node f k (Just link)
unfoldConclusion' k f@(g :-\ h)  = right
  where link = Link Tensor Fission RightT left right third
        left = unfoldHypothesis' (Just link) g
        right = Node f k (Just link)
        third = unfoldConclusion' (Just link) h
unfoldConclusion' k f@(g :-/ h)  = left
  where link = Link Tensor Fission LeftT left right third
        left = Node f k (Just link)
        right = unfoldConclusion' (Just link) h
        third = unfoldHypothesis' (Just link) g
