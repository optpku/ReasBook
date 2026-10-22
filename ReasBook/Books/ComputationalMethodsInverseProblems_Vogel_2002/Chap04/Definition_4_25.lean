/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_25.MAPEstimator

public section

/- Definition 4.25 (1). In the discrete Bayes-rule context, the first marginal PMF of `X`
is the prior, formalized by the pointwise formula `ProbabilityTheory.JointPmf.fstMarginal_apply`.
-/
#check ProbabilityTheory.JointPmf.fstMarginal_apply

/- Definition 4.25 (2). The a posteriori PMF of `X` given the observation `Y = y` is
formalized by `ProbabilityTheory.JointPmf.condFstGivenSnd_apply`, with the nonvanishing
denominator hypothesis carried explicitly.
-/
#check ProbabilityTheory.JointPmf.condFstGivenSnd_apply

/- Definition 4.25 (3). A maximum a posteriori estimator is formalized by the posterior
maximizer predicate `ProbabilityTheory.JointPmf.IsMAPEstimator`.
-/
#check ProbabilityTheory.JointPmf.IsMAPEstimator
