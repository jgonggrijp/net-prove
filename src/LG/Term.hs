module LG.Term where

import LG.Base

data Term = V ValueTerm | E ContextTerm | C CommandTerm deriving (Eq, Ord)

data NodeTerm = Va ValueTerm' | Ev ContextTerm' deriving (Eq, Ord)

data ValueTerm'   = Variable Name
                  | ValueTerm   :<×> ValueTerm
                  | ContextTerm :<\> ValueTerm
                  | ValueTerm   :</> ContextTerm
                  deriving (Eq, Ord)

data ValueTerm    = V' ValueTerm'
                  | Mu Name CommandTerm
                  deriving (Eq, Ord)

data ContextTerm' = Covariable Name
                  | ValueTerm    :\  ContextTerm
                  | ContextTerm  :/  ValueTerm
                  | ContextTerm :<+> ContextTerm
                  deriving (Eq, Ord)

data ContextTerm  = E' ContextTerm'
                  | Comu Name CommandTerm
                  deriving (Eq, Ord)

data CommandTerm  = Cut Name Name Name CommandTerm  -- (first second) / third
                  | ValueTerm' :⌈ Name              -- Command right
                  | Name       :⌉ ContextTerm'      -- Command left
                  deriving (Eq, Ord)

fromNodeTerm :: NodeTerm -> Term
fromNodeTerm (Va t) = V (V' t)
fromNodeTerm (Ev t) = E (E' t)

class Substitutable a where
    substitute :: ValidSubstitution b => b -> b -> a -> a
    --substitute x for y in z

class ValidSubstitution a where
    asValue    :: a -> Maybe ValueTerm
    asContext  :: a -> Maybe ContextTerm
    asValue   _ = Nothing
    asContext _ = Nothing

instance ValidSubstitution ValueTerm where
    asValue x = Just x

instance ValidSubstitution ContextTerm where
    asContext x = Just x

instance Substitutable Term where
    substitute x y (V z) = V $ substitute x y z
    substitute x y (E z) = E $ substitute x y z
    substitute x y (C z) = C $ substitute x y z

instance Substitutable ValueTerm where
    -- the following matcher enables substitution of a mu binding
    -- for a variable
    substitute x y z@(V' (Variable s)) = case (asValue x, asValue y) of
        (Just x', Just (V' (Variable t))) -> if s == t then x' else z
        _ -> z
    substitute x y (Mu s z)            = Mu s $ substitute x y z
    substitute x y (V' z)              = V'   $ substitute x y z

instance Substitutable ValueTerm' where
    substitute x y (v :<×> w)     = substitute x y v :<×> substitute x y w
    substitute x y (v :<\> w)     = substitute x y v :<\> substitute x y w
    substitute x y (v :</> w)     = substitute x y v :</> substitute x y w
    -- given instance Substitutable ValueTerm, the following matcher
    -- can only apply directly after recursion into (z' :⌈ s')
    substitute x y z@(Variable s) = case (asValue x, asValue y) of
        (Just (V' x'), Just (V' (Variable t))) -> if s == t then x' else z
        _ -> z

instance Substitutable ContextTerm where
    substitute x y z@(E' (Covariable s)) = case (asContext x, asContext y) of
        (Just x', Just (E' (Covariable t))) -> if s == t then x' else z
        _ -> z
    substitute x y (E' z)                = E'     $ substitute x y z
    substitute x y (Comu s z)            = Comu s $ substitute x y z

-- notes for instances ValueTerm, ValueTerm' also apply here
instance Substitutable ContextTerm' where
    substitute x y (v  :\  w)       = substitute x y v  :\  substitute x y w
    substitute x y (v  :/  w)       = substitute x y v  :/  substitute x y w
    substitute x y (v :<+> w)       = substitute x y v :<+> substitute x y w
    substitute x y z@(Covariable s) = case (asContext x, asContext y) of
        (Just (E' x'), Just (E' (Covariable t))) -> if s == t then x' else z
        _ -> z

instance Substitutable CommandTerm where
    substitute x y (Cut s t u z) = Cut s t u $ substitute x y z
    substitute x y (z :⌈ s)      = substitute x y z :⌈ s
    substitute x y (s :⌉ z)      = s :⌉ substitute x y z

isSubtermOf :: Term -> Term -> Bool
t1 `isSubtermOf` t2 = t1 == t2 || case t2 of
    (V (V' (Variable _))) -> False
    (V (V' (t3 :<×> t4))) -> t1 `isSubtermOf` (V t3) || t1 `isSubtermOf` (V t4)
    (V (V' (t3 :<\> t4))) -> t1 `isSubtermOf` (E t3) || t1 `isSubtermOf` (V t4)
    (V (V' (t3 :</> t4))) -> t1 `isSubtermOf` (V t3) || t1 `isSubtermOf` (E t4)
    (V (Mu _ t3)) -> t1 `isSubtermOf` (C t3)
    (E (E' (Covariable _))) -> False
    (E (E' (t3  :\  t4))) -> t1 `isSubtermOf` (V t3) || t1 `isSubtermOf` (E t4)
    (E (E' (t3  :/  t4))) -> t1 `isSubtermOf` (E t3) || t1 `isSubtermOf` (V t4)
    (E (E' (t3 :<+> t4))) -> t1 `isSubtermOf` (E t3) || t1 `isSubtermOf` (E t4)
    (E (Comu _ t3)) -> t1 `isSubtermOf` (C t3)
    (C (t3 :⌈ n )) -> case t1 of
        (E (E' (Covariable n'))) -> n == n' || t1 `isSubtermOf` (V (V' t3))
        _                        ->            t1 `isSubtermOf` (V (V' t3))
    (C (n  :⌉ t3)) -> case t1 of
        (V (V' (Variable n'))) -> n == n' || t1 `isSubtermOf` (E (E' t3))
        _                      ->            t1 `isSubtermOf` (E (E' t3))
    (C (Cut _ _ n t3)) -> case t1 of
        (V (V' (Variable   n'))) -> n == n' || t1 `isSubtermOf` (C t3)
        (E (E' (Covariable n'))) -> n == n' || t1 `isSubtermOf` (C t3)
        _                        ->            t1 `isSubtermOf` (C t3)
        -- (slightly too permissive)

instance Show Term where
    show (V m) = show m
    show (E m) = show m
    show (C m) = show m

instance Show NodeTerm where
    show (Va m) = show m
    show (Ev m) = show m

instance Show ValueTerm where
    show (V' m) = show m
    show (Mu v m) = "µ" ++ v ++ "." ++ show m

instance Show ValueTerm' where
    show (Variable v) = v
    show (m :<×> n) = "(" ++ show m ++ " <×> " ++ show n ++ ")"
    show (m :<\> n) = "(" ++ show m ++ " <\\> " ++ show n ++ ")"
    show (m :</> n) = "(" ++ show m ++ " </> " ++ show n ++ ")"

instance Show ContextTerm where
    show (E' m) = show m
    show (Comu v m) = "µ̃" ++ v ++ "." ++ show m

instance Show ContextTerm' where
    show (Covariable v) = v
    show (m  :\  n) = "(" ++ show m ++ " \\ " ++ show n ++ ")"
    show (m  :/  n) = "(" ++ show m ++ " / " ++ show n ++ ")"
    show (m :<+> n) = "(" ++ show m ++ " <+> " ++ show n ++ ")"

instance Show CommandTerm where
    show (m :⌈ v) = "〈" ++ show m ++ " ⌈ " ++ v ++ "〉"
    show (v :⌉ m) = "〈" ++ v ++ " ⌉ " ++ show m ++ "〉"
    show (Cut t u v m) = "(" ++ t ++ " " ++ u ++ ")÷" ++ v ++ "." ++ show m
