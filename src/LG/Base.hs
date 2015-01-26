module LG.Base where

type Name = String
type Identifier = Int

data Occurrence a = Identifier :@ a deriving (Eq, Show)

abstract :: Occurrence a -> a
abstract (_ :@ x) = x

data Formula = P PositiveFormula | N NegativeFormula deriving (Eq, Show)

data PositiveFormula = AtomP Name
                     | Formula :<×>: Formula
                     | Formula :<\>: Formula
                     | Formula :</>: Formula
                     deriving (Eq, Show)

data NegativeFormula = AtomN Name
                     | Formula  :\:  Formula
                     | Formula  :/:  Formula
                     | Formula :<+>: Formula
                     deriving (Eq, Show)