/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_15

public section

/- Exercise 7.13. The source asks the reader to prove Proposition 7.15. In
this repository, Proposition 7.15 is already formalized as the four
source-facing Chapter 7 clauses below, so this exercise is recorded by direct
reuse of that existing surface rather than by introducing an exercise-specific
wrapper theorem.
-/
#check TsvdEstimation.backwardDiffNonpos
#check TsvdEstimation.forwardDiffNonneg
#check TsvdEstimation.optimalIndexLowerBound
#check TsvdEstimation.optimalIndexUpperBound
