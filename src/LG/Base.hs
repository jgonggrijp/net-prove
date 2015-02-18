module LG.Base where

type Name = String
type Identifier = Int

data Occurrence a = Identifier :@ a deriving (Eq, Ord)

abstract :: Occurrence a -> a
abstract (_ :@ x) = x

data Formula = P PositiveFormula | N NegativeFormula deriving (Eq, Ord)

data PositiveFormula = AtomP Name
                     | Formula :<×>: Formula
                     | Formula :<\>: Formula
                     | Formula :</>: Formula
                     deriving (Eq, Ord)

data NegativeFormula = AtomN Name
                     | Formula  :\:  Formula
                     | Formula  :/:  Formula
                     | Formula :<+>: Formula
                     deriving (Eq, Ord)

instance Show a => Show (Occurrence a) where
  show (k :@ a) = show k ++ " @ " ++ show a

instance Show Formula where
  show (P f) = show f
  show (N f) = show f

instance Show PositiveFormula where
  show (AtomP   f) = f ++ "⁺"
  show (f :<×>: e) = "(" ++ show f ++ " <×> "  ++ show e ++ ")"
  show (f :<\>: e) = "(" ++ show f ++ " <\\> " ++ show e ++ ")"
  show (f :</>: e) = "(" ++ show f ++ " </> "  ++ show e ++ ")"

instance Show NegativeFormula where
  show (AtomN   f) = f ++ "⁻"
  show (f :<+>: e) = "(" ++ show f ++ " <+> " ++ show e ++ ")"
  show (f  :\:  e) = "(" ++ show f ++  " \\ " ++ show e ++ ")"
  show (f  :/:  e) = "(" ++ show f ++  " / "  ++ show e ++ ")"
