module Logic.LG where

data LinkType = Tensor | Cotensor
data LinkMode = Fusion | Fission
data LinkDirection = Left | Right | Third

data Link = Link {
    linkType :: LinkType,
    linkMode :: LinkMode,
    linkDirection :: LinkDirection,
    left :: Node,
    right :: Node,
    third :: Node }

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
    succedentLink :: Maybe Link }

data Atom = NP | N | S

data Formula = Atomic Atom
    | Formula :*: Formula
    | Formula :\\ Formula
    | Formula :// Formula
    | Formula :+: Formula
    | Formula :-\ Formula
    | Formula :-/ Formula
