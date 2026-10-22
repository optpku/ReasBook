/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_8

public section

/- Exercise 7.11. The source asks the reader to prove Proposition 7.8. In this
repository, Proposition 7.8 is already formalized by the two source-facing
Chapter 7 spectral-sum theorems below, phrased in the named source objects
`Aα`, `pα`, and `rα`, so this exercise is recorded by direct reuse of that
existing surface rather than by an exercise-specific wrapper theorem.
-/
#check FilterRegularization.expectedPredictiveRisk_pα_eq_spectralSum
#check FilterRegularization.expectedResidualRisk_rα_eq_spectralSum
