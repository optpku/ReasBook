/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Example_4_26.MapEstimator

public section

/- Exercise 4.11.

In the isotropic covariance case, the Chapter 4 identity `(4.22)` is already formalized in
its canonical owner module as
`LinearGaussian.precisionEstimator_eq_tikhonovReconstruction`. This exercise is therefore
direct source-facing reuse of that theorem.
-/

#check LinearGaussian.precisionEstimator_eq_tikhonovReconstruction
