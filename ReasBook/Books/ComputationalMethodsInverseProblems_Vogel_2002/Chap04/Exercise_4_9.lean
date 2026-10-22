/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Example_4_26.MapEstimator

public section

/- Exercise 4.9.

The Chapter 4 MAP-estimator statement already exists in the local API, in its
canonical owner module, as `LinearGaussian.isMapEstimator_precisionEstimator`.
This exercise is therefore direct source-facing reuse of that theorem.
-/

#check LinearGaussian.isMapEstimator_precisionEstimator
