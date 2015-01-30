module LG.TestGraph where

import qualified Data.Map as Map

import LG.Base
import LG.Term
import LG.Graph

{-
    The following builds the example graph in fig. 18
    from Moortgat & Moot 2012, p. 28.

    The purpose of exposing all intermediate building blocks is to aid
    in testing. Keep in mind that this module introduces lots of
    variables with short names, though.
-}

-- base formulae
np      = P (AtomP "np")
n       = P (AtomP "n")
s       = N (AtomN "s")
np_n    = N (np :/: n)
np_n_n  = P (np_n :<×>: n)
np_s    = N (np :\: s)
np_s_np = N (np_s :/: np)

-- base terms
det   = Variable "det"
noun  = Variable "noun"
tv    = Variable "tv"
subj  = Variable "subj"
x     = Variable "x"
x'    = Variable "x'"
y     = Variable "y"
y'    = Variable "y'"
z     = Variable "z"
z'    = Variable "z'"
alpha = Covariable "α"
beta  = Covariable "β"
beta' = Covariable "β'"
gamma = Covariable "γ"

-- node and link descriptions
-- #:           id of a node
-- f#:          formula for given id
-- t#:          term for given id
-- c#u, c#d:    upwards, downwards tentacle for given id
-- k##(#):      link between the given ids
-- n#:          NodeInfo for the given id
f1      = np_n
t1      = Va det
c1d     = Active 1
f2      = n
t2      = Va noun
c2d     = Active 2
f3      = np_n
t3      = Ev (E' alpha :/ V' noun)
c3u     = Active 3
c3d     = MainT 3
k13     = c1d :|: c3u
n1      = Node f1 t1 (Just k13) Nothing

f4      = np
t4      = Ev alpha
c4d     = Active 4
c4u     = Active 4
k234    = [c3d, c2d] :○: [c4u]
n2      = Node f2 t2 (Just k234) Nothing
n3      = Node f3 t3 (Just k234) (Just k13)

f5      = np
t5      = Va y
c5d     = Active 5
c5u     = Active 5
k45     = c4d :|: c5u
n4      = Node f4 t4 (Just k45) (Just k234)

f6      = np_s_np
t6      = Va tv
c6d     = Active 6
f7      = np_s_np
t7      = Ev (E' beta' :/ V' y)
c7u     = Active 7
c7d     = MainT 7
k67     = c6d :|: c7u
n6      = Node f6 t6 (Just k67) Nothing

f8'     = np_s
t8'     = Ev beta'
c8'u    = Active 80
c8'd    = Active 80
k578    = [c7d, c5d] :○: [c8'u]
n5      = Node f5 t5 (Just k578) (Just k45)
n7      = Node f7 t7 (Just k578) (Just k67)

f8      = np_s
t8      = Ev (V' x :\ E' beta)
c8u     = Active 8
c8d     = MainT 8
k88'    = c8'd :|: c8u
n8'     = Node f8' t8' (Just k88') (Just k578)

f9      = s
t9      = Ev beta
c9d     = Active 9
c9u     = Active 9
f10     = s
t10     = Va x'
c10u    = Active 10
k910    = c9d :|: c10u
n10     = Node f10 t10 Nothing (Just k910)

f11     = np
t11     = Va x
c11d    = Active 11
c11u    = Active 11
k8911   = [c11d, c8d] :○: [c9u]
n8      = Node f8 t8 (Just k8911) (Just k88')
n9      = Node f9 t9 (Just k910) (Just k8911)

f12     = np
t12     = Ev gamma
c12d    = Active 12
c12u    = Active 12
k1112   = c12d :|: c11u
n11     = Node f11 t11 (Just k8911) (Just k1112)

f13     = np_n
t13     = Ev (E' gamma :/ V' z')
c13u    = Active 13
c13d    = MainT 13
f14     = n
t14     = Va z'
c14d    = Active 14
c14u    = Active 14
k121314 = [c13d, c14d] :○: [c12u]
n12     = Node f12 t12 (Just k1112) (Just k121314)

f14'    = n
t14'    = Va z
c14'u   = Active 140
c14'd   = Active 140
k1414'  = c14'd :|: c14u
n14     = Node f14 t14 (Just k121314) (Just k1414')

f15     = np_n
t15     = Va y'
c15d    = Active 15
c15u    = Active 15
k1315   = c15d :|: c13u
n13     = Node f13 t13 (Just k121314) (Just k1315)

f16     = np_n_n
t16     = Va subj
c16d    = MainT 16
k141516 = [c16d] :●: [c15u, c14'u]
n14'    = Node f14' t14' (Just k1414') (Just k141516)
n15     = Node f15 t15 (Just k1315) (Just k141516)
n16     = Node f16 t16 (Just k141516) Nothing

-- finally, the graph
testGraph :: CompositionGraph
testGraph = Map.fromList [ (1, n1)
                         , (2, n2)
                         , (3, n3)
                         , (4, n4)
                         , (5, n5)
                         , (6, n6)
                         , (7, n7)
                         , (8, n8)
                         , (80, n8')
                         , (9, n9)
                         , (10, n10)
                         , (11, n11)
                         , (12, n12)
                         , (13, n13)
                         , (14, n14)
                         , (140, n14')
                         , (15, n15)
                         , (16, n16)
                         ]
