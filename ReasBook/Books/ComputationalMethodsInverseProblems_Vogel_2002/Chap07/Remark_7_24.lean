/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_11
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_21.ExpectedError
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_23.PredictiveRisk

public section

/-!
Remark 7.24 (predictive versus estimation saturation thresholds).

This item is kept source-faithful as a blocker-style bridge to the existing
Chapter 7 owners rather than as standalone arithmetic threshold lemmas. The
predictive side is already encoded by `TikhonovPredictiveRisk.betaPred` for the
predictive-risk objective `(7.86)`, while the estimation side is encoded by
`TikhonovEstimation.expectedObjective`,
`TikhonovEstimation.IsCriticalBenchmark`, and
`TikhonovEstimation.saturatedParameterBenchmark` for `(7.80)`. The source-term
comparison referred to in the remark is already exposed through the
`K.adjoint.range` bridge from `Remark_7_11` together with the
`K* K`-weighted term `TikhonovEstimation.adjointCompSourceNormSq`.
-/

/- Remark 7.24. The present Chapter 7 development records this remark by direct
reuse of the predictive benchmark owner, the estimation benchmark owners, and
the Remark 7.11 source-condition bridge. -/

#check TikhonovPredictiveRisk.betaPred

#check TikhonovEstimation.expectedObjective

#check TikhonovEstimation.IsCriticalBenchmark

#check TikhonovEstimation.nonsaturatedParameterBenchmark

#check TikhonovEstimation.saturatedParameterBenchmark

#check TikhonovEstimation.adjointCompSourceNormSq

#check
  ContinuousLinearMap.SingularSystem.adjoint_mem_range_iff_weightedSourceSeriesSummable
