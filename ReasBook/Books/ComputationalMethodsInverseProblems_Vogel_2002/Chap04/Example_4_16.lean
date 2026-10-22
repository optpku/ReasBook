/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Example_4_16.GaussianMean

public section

/- Example 4.16. The Gaussian-mean negative log-likelihood for a single observation is the
source-facing owner `GaussianMean.negLogLikelihood`. -/

#check GaussianMean.negLogLikelihood

/- Example 4.16. A Gaussian mean maximum-likelihood estimator is the source-facing predicate
`GaussianMean.IsMeanMLE`. -/

#check GaussianMean.IsMeanMLE

/- Example 4.16. For positive-definite covariance, the observed vector is the Gaussian mean
maximum-likelihood estimator. -/

#check GaussianMean.isMeanMLE_observation

/- Example 4.16. For positive-definite covariance, every Gaussian mean maximum-likelihood
estimator is equal to the observed vector. -/

#check GaussianMean.eq_observation_of_isMeanMLE
