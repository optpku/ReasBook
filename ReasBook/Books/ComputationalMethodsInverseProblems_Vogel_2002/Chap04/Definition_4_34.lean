/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_34.MinimumVarianceLinear

public section

/- Definition 4.34. The minimum variance linear estimator of `X` from `Z` is formalized by
`ProbabilityTheory.MinimumVarianceLinear.IsEstimator`, with
`ProbabilityTheory.MinimumVarianceLinear.isEstimator_iff` exposing the optimal-coefficient view
under the finite-second-moment hypotheses. -/
#check ProbabilityTheory.MinimumVarianceLinear.IsEstimator
#check ProbabilityTheory.MinimumVarianceLinear.isEstimator_iff
