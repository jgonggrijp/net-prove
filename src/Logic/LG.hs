module Logic.LG where

data LinkType = Tensor | Cotensor

class Link a where
    linkType :: a -> LinkType
    premises :: a -> [Node]
    conclusions :: a -> [Node]
    mainFormula :: a -> Node
    mainFormula = main

data FusionTensor = FusionTensor {
    left :: Node,
    right :: Node,
    bottom :: Node,
    main :: Node }
instance Link FusionTensor where
    linkType fut = Tensor
    premises fut = [left fut, right fut]
    conclusions fut = [bottom fut]

data FusionCotensor = FusionCotensor {
    left :: Node,
    right :: Node,
    top :: Node,
    main :: Node }
instance Link FusionCotensor where
    linkType fuc = Cotensor
    conclusions fuc = [left fuc, right fuc]
    premises fuc = [top fuc]

data FissionTensor = FissionTensor {
    left :: Node,
    right :: Node,
    top :: Node,
    main :: Node }
instance Link FissionTensor where
    linkType fit = Tensor
    conclusions fit = [left fit, right fit]
    premises fit = [top fit]

data FissionCotensor = FissionCotensor {
    left :: Node,
    right :: Node,
    bottom :: Node,
    main :: Node }
instance Link FissionCotensor where
    linkType fic = Cotensor
    premises fic = [left fic, right fic]
    conclusions fic = [bottom fic]

class Formula a where
    -- common functions on formulas
    -- (obviously, this should actually be in the Framework module)

-- types below are going to be instances of formula, somehow

data Atom = NP | N | S

data Prod a b = a :*: b
data LDiv a b = a :\\ b
data RDiv a b = a :// b
data Sum  a b = a :+: b
data LSub a b = a :-\ b
data RSub a b = a :-/ b
