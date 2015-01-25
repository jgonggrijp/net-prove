module Lexicon where
    import LG.Graph

    data Entry = LexEntry {
      term    :: NodeTerm,
      formula :: Formula
    }

    entries :: [String] -> [Entry]
    entries words = (map Lexicon.lookup) words

    npP   = P (AtomP "np")
    nP    = P (AtomP "n")
    sP    = P (AtomP "s")
    sN    = N (AtomN "s")
    det   = N (npP :/: nP)
    tv    = N (N (npP :\: sP) :/: npP)
    sub   = P ((N (npP:/:nP)):<×>: nP)

    va name = Va (Variable name)
    ev name = Ev (Covariable name)

    lookup "Mary"  = LexEntry (va "m")     npP
    lookup "likes" = LexEntry (va "likes") tv
    lookup "John"  = LexEntry (va "j")     npP
    lookup "the"   = LexEntry (va "the")   det
    lookup "horse" = LexEntry (va "horse") nP

    -- Fig 15
    lookup "figure15" =  LexEntry (va "f")  f
      where f = P( N ( P (AtomP "a"):/:P (AtomP "b")):<×>: (P (AtomP "b")))

    -- Fig 18
    lookup "sub"   = LexEntry (va "sub")   sub
    lookup "tv"    = LexEntry (va "tv")    tv
    lookup "det"   = LexEntry (va "det")   det
    lookup "noun"  = LexEntry (va "noun")  nP

    lookup "s"     = LexEntry (ev "s")     sN