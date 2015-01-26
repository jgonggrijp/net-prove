module Lexicon where
    import LG.Graph
    import LG.Base
    import LG.Term

    data Entry = LexEntry {
      term    :: NodeTerm,
      formula :: Formula
    }

    -- Returns the lexical entries to which the given strings map. We assume for simplicity that one word maps to at most one lexical entry.
    entries :: [String] -> [Entry]
    entries words = (map Lexicon.lookup) words

    -- Some often used formulae
    npP   = P (AtomP "np")
    nP    = P (AtomP "n")
    sP    = P (AtomP "s")
    sN    = N (AtomN "s")
    det   = N (npP :/: nP)
    tv    = N (N (npP :\: sP) :/: npP)
    sub   = P ((N (npP:/:nP)):<×>: nP)

    -- Utility functions for creating atomic terms
    va name = Va (Variable name)
    ev name = Ev (Covariable name)

    -- Example lexicon
    lookup "Mary"  = LexEntry (va "m")     npP
    lookup "likes" = LexEntry (va "likes") tv
    lookup "John"  = LexEntry (va "j")     npP
    lookup "the"   = LexEntry (va "the")   det
    lookup "horse" = LexEntry (va "horse") nP

    lookup "s"     = LexEntry (ev "s")     sN

    -- Fig 15
    lookup "figure15" =  LexEntry (va "f")  f
      where f = P( N ( P (AtomP "a"):/:P (AtomP "b")):<×>: (P (AtomP "b")))

    -- Fig 18
    lookup "sub"   = LexEntry (va "sub")   sub
    lookup "tv"    = LexEntry (va "tv")    tv
    lookup "det"   = LexEntry (va "det")   det
    lookup "noun"  = LexEntry (va "noun")  nP