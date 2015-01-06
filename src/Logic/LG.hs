module Logic.LG where

import Data.Set (Set)

data LinkType = Tensor | Cotensor deriving (Eq, Ord)
data LinkMode = Fusion | Fission deriving (Eq, Ord)
data LinkDirection = Left | Right | Third deriving (Eq, Ord)

data Link = Link {
    linkType :: LinkType,
    linkMode :: LinkMode,
    linkDirection :: LinkDirection,
    left :: Node,
    right :: Node,
    third :: Node } deriving (Eq, Ord)

premises :: Link -> [Node]
premises (Link Tensor Fusion    _ a b _) = [a, b]
premises (Link Cotensor Fusion  _ _ _ c) = [c]
premises (Link Tensor Fission   _ _ _ c) = [c]
premises (Link Cotensor Fission _ a b _) = [a, b]

succedents :: Link -> [Node]
succedents (Link Tensor Fusion    _ _ _ c) = [c]
succedents (Link Cotensor Fusion  _ a b _) = [a, b]
succedents (Link Tensor Fission   _ a b _) = [a, b]
succedents (Link Cotensor Fission _ _ _ c) = [c]

mainNode :: Link -> Node
mainNode (Link _ _ Left  a _ _) = a
mainNode (Link _ _ Right _ b _) = b
mainNode (Link _ _ Third _ _ c) = c

data Node = Node {
    formula :: Formula,
    premiseLink :: Maybe Link,
    succedentLink :: Maybe Link } deriving (Eq, Ord)

type ProofStructure = Set Node

hypotheses :: ProofStructure -> Set Node
hypotheses = filter ((== Nothing) . succedentLink)

conclusions :: ProofStructure -> Set Node
conclusions = filter ((== Nothing) . premiseLink)

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
  where link = Link Cotensor Fusion Third left right third
        left = unfoldHypothesis' link g
        right = unfoldHypothesis' link h
        third = Node f (Just link) k
unfoldHypothesis' k f@(g :\\ h)  = right
  where link = Link Tensor Fusion Right left right third
        left = unfoldConclusion' link g
        right = Node f (Just link) k
        third = unfoldHypothesis' link h
unfoldHypothesis' k f@(g :// h)  = left
  where link = Link Tensor Fusion Left left right third
        left = Node f (Just link) k
        right = unfoldHypothesis' link h
        third = unfoldConclusion' link g
