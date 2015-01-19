module LG.Graph where

import LG.Base

data Term = V ValueTerm | E ContextTerm | C CommandTerm deriving (Eq, Show)

data NodeTerm = Va ValueTerm' | Ev ContextTerm' deriving (Eq, Show)

data ValueTerm'   = Variable Name
                  | ValueTerm   :<×> ValueTerm
                  | ContextTerm :<\> ValueTerm
                  | ValueTerm   :</> ContextTerm
                  deriving (Eq, Show)

data ValueTerm    = V' ValueTerm'
                  | Mu Name CommandTerm
                  deriving (Eq, Show)

data ContextTerm' = Covariable Name
                  | ValueTerm    :\  ContextTerm
                  | ContextTerm  :/  ValueTerm
                  | ContextTerm :<+> ContextTerm
                  deriving (Eq, Show)

data ContextTerm  = E' ContextTerm'
                  | Comu Name CommandTerm
                  deriving (Eq, Show)

data CommandTerm  = Cut Name Name Name CommandTerm  -- (first second) / third
                  | ValueTerm' :⌈ Name              -- Command right
                  | Name       :⌉ ContextTerm'      -- Command left
                  deriving (Eq, Show)
