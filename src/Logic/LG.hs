module Logic.LG where

{-
    This LoLa-related Haskell sourcefile is a *stub*.
    You can help by expanding it.
-}

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
