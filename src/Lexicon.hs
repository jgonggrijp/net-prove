module Lexicon where
    import LG.Base
    import LG.Term
    import Data.Maybe

    data Entry = LexEntry {
      term    :: NodeTerm,
      formula :: Formula
    } deriving (Show)

    -- Returns the lexical entries to which the given strings map. We assume for simplicity that one word maps to at most one lexical entry.
    entries :: [String] -> Maybe [Entry]
    entries []     = Just []
    entries (x:xs) = case Lexicon.lookup x of
      Just x' -> entries xs >>= Just . (x':)
      Nothing -> Nothing

--    entries xs >>= (Lexicon.lookup x:)

    -- Some often used formulae
    npP   = P (AtomP "np")
    nP    = P (AtomP "n")
    sP    = P (AtomP "s")
    sN    = N (AtomN "s")
    det   = N (npP :/: nP)
    tv    = N (N (npP :\: sN) :/: npP)
    sub   = P ((N (npP:/:nP)):<×>: nP)

    -- Utility functions for creating atomic terms
    va name = Va (Variable name)
    ev name = Ev (Covariable name)

    -- Example lexicon
    lookup "Mary"  = Just $ LexEntry (va "m")     npP
    lookup "likes" = Just $ LexEntry (va "likes") tv
    lookup "John"  = Just $ LexEntry (va "j")     npP
    lookup "the"   = Just $ LexEntry (va "the")   det
    lookup "horse" = Just $ LexEntry (va "horse") nP

    lookup "s"     = Just $ LexEntry (ev "s")     sN

    -- Fig 15
    lookup "figure15" =  Just $ LexEntry (va "f")  f
      where f = P( N ( P (AtomP "a"):/:P (AtomP "b")):<×>: (P (AtomP "b")))

    -- Fig 18
    lookup "sub"   = Just $ LexEntry (va "sub")   sub
    lookup "tv"    = Just $ LexEntry (va "tv")    tv
    lookup "det"   = Just $ LexEntry (va "det")   det
    lookup "noun"  = Just $ LexEntry (va "noun")  nP

    lookup "every"   = Just $ LexEntry (va "every")   (N $ (N $ sN :/: (N $ npP :\: sN)) :/: nP)
    lookup "barber"  = Just $ LexEntry (va "barber")  nP
    lookup "shaves"  = Just $ LexEntry (va "shaves")  (N $ npP :\: (N $ sN :/: npP))
    lookup "himself" = Just $ LexEntry (va "himself") (N $ (N $ (N $ npP :\: sN) :/: npP) :\: (N $ npP :\: sN))

    lookup _ = Nothing
