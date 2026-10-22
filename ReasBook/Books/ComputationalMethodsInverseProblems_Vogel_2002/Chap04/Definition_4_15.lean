/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_15.Likelihood

public section

/- Definition 4.15 (1). For fixed observed data `d`, the likelihood function
`L(θ) = p_X(d; θ)` is formalized by `ProbabilityTheory.likelihood`, with
`ProbabilityTheory.likelihood_apply` exposing the pointwise formula. -/
#check ProbabilityTheory.likelihood
#check ProbabilityTheory.likelihood_apply

/- Definition 4.15 (2). A maximum likelihood estimator is formalized by the unrestricted
maximizer predicate `ProbabilityTheory.IsMLE`, and `ProbabilityTheory.isMLE_iff` exposes the
underlying `IsMaxOn ... Set.univ` statement. -/
#check ProbabilityTheory.IsMLE
#check ProbabilityTheory.isMLE_iff

/- Definition 4.15 (3). The log-likelihood `ℓ(θ) = log p_X(d; θ)` is formalized by
`ProbabilityTheory.logLikelihood`, and the source maximizer reformulation is captured by
`ProbabilityTheory.isMLE_iff_isMaxOn_logLikelihood` with the explicit positivity hypothesis
needed for `Real.log`. -/
#check ProbabilityTheory.logLikelihood
#check ProbabilityTheory.logLikelihood_apply
#check ProbabilityTheory.isMLE_iff_isMaxOn_logLikelihood
