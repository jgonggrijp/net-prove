module Logic.LG where
import qualified Logic.Link as Link

-- Formula language of Lambek Grishin calculus (LG); see Moortgat & Moot 2012, p. 1-2
data Formula a = Atom a |         -- NP, S, etc.
  (:*:) (Formula a) (Formula a) | -- ⊗ (Prod)
  (:\\) (Formula a) (Formula a) | -- \ (LDiv)
  (://) (Formula a) (Formula a) | -- / (RDiv)
  (:+:) (Formula a) (Formula a) | -- ⊕ (Sum)
  (:-\) (Formula a) (Formula a) | -- ⃠ (LSub)
  (:-/) (Formula a) (Formula a)   -- ⊘ (RSub)
  deriving (Eq, Ord)
instance (Show a) => Show (Formula a) where
  show (Atom a) = show a
  show (a :// b) = "("++(show a) ++ " /" ++ (show b) ++ ")" -- /
  show (a :*: b) = "("++(show a) ++ " [x] " ++ (show b) ++ ")" -- ⊗
  show (a :\\ b) = "("++(show a) ++ "\\ " ++ (show b) ++ ")" -- \
  show (a :-/ b) = "("++(show a) ++ " [/]" ++ (show b) ++ ")" -- ⊘
  show (a :+: b) = "("++(show a) ++ " [+] " ++ (show b) ++ ")" -- ⊕
  show (a :-\ b) = "("++(show a) ++ "[\\] " ++ (show b) ++ ")" -- ⃠

-- Rules for creating Links from complex formulae. See also M&M 2012, p6
--- Hypothesis
unfoldHypothesis :: (Eq a) => Formula a -> Link.Link (Formula a)
---- Fusion connectives (Hypothesis)
unfoldHypothesis (a :// b) = Link.constructLink Link.Tensor [a :// b, b] [a] (a :// b) -- L/
unfoldHypothesis (a :*: b) = Link.constructLink Link.CoTensor [a :*: b] [a, b] (a :*: b) -- L⊗
unfoldHypothesis (b :\\ a) = Link.constructLink Link.Tensor [b :\\ a, b] [a] (b :\\ a) -- L\
---- Fission connectives (Hypothesis)
unfoldHypothesis (a :-/ b) = Link.constructLink Link.CoTensor [a :-/ b, b] [a] (a :-/ b) -- L⊘
unfoldHypothesis (a :+: b) = Link.constructLink Link.Tensor [a :+: b] [a, b] (a :+: b) -- L⊕
unfoldHypothesis (b :-\ a) = Link.constructLink Link.CoTensor [b, b :\\ a] [a] (b :\\ a) -- L⃠
---
--- Conclusion
unfoldConclusion :: (Eq a) => Formula a -> Link.Link (Formula a)
---- Fusion connectives (Conclusion)
unfoldConclusion (a :// b) = Link.constructLink Link.CoTensor [a] [a :// b, b] (a :// b) -- R/
unfoldConclusion (a :*: b) = Link.constructLink Link.Tensor [a, b] [a :*: b] (a :*: b) -- R⊗
unfoldConclusion (b :\\ a) = Link.constructLink Link.CoTensor [a] [b, b :\\ a] (b :\\ a) -- R\
---- Fission connectives (Conclusion)
unfoldConclusion (a :-/ b) = Link.constructLink Link.Tensor [a] [a :-/ b, b] (a :-/ b) -- R⊘
unfoldConclusion (a :+: b) = Link.constructLink Link.CoTensor [a, b] [a :+: b] (a :+: b) -- R⊕
unfoldConclusion (b :-\ a) = Link.constructLink Link.Tensor [a] [b, b :-\ a] (b :-\ a) -- R⃠
---
--- Examples
unfoldExamples = [
  unfoldHypothesis ((Atom "A") :// (Atom "B")), -- L/
  unfoldHypothesis ((Atom "A") :*: (Atom "B")), -- L⊗
  unfoldHypothesis ((Atom "B") :\\ (Atom "A")), -- L\
  unfoldHypothesis ((Atom "A") :-/ (Atom "B")), -- L⊘
  unfoldHypothesis ((Atom "A") :+: (Atom "B")), -- L⊕
  unfoldHypothesis ((Atom "B") :-\ (Atom "A")), -- L⃠
  unfoldConclusion ((Atom "A") :// (Atom "B")), -- R/
  unfoldConclusion ((Atom "A") :*: (Atom "B")), -- R⊗
  unfoldConclusion ((Atom "B") :\\ (Atom "A")), -- R\
  unfoldConclusion ((Atom "A") :-/ (Atom "B")), -- R⊘
  unfoldConclusion ((Atom "A") :+: (Atom "B")), -- R⊕
  unfoldConclusion ((Atom "B") :-\ (Atom "A"))] -- R⃠

