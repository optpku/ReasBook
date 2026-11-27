/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Exercise_1_11.Operator
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Exercise_1_11.Regularity
public import Mathlib.Analysis.InnerProductSpace.Adjoint

public section

noncomputable section

namespace Fredholm1D

/-- Exercise 1.11. For the continuous Fredholm operator `(1.1)` with the Gaussian kernel,
the source condition `fTrue = K^* z` with `z ∈ L²(0, 1)` forces the true solution to be
smooth: `fTrue` admits a globally `C^∞` representative.

The Gaussian `L²(0, 1)` blur is self-adjoint (`gaussianBlurL2_adjoint_eq`), so the source
condition is the same as asking `fTrue` to be in the range of the smoothing operator
`gaussianBlurL2`, whose values are smooth (`gaussianBlurL2_hasSmoothRepresentative`). -/
theorem sourceCondition_hasSmoothRepresentative (C γ : ℝ)
    (fTrue z : MeasureTheory.Lp ℝ 2 unitIntervalMeasure)
    (h_source : fTrue = ContinuousLinearMap.adjoint (gaussianBlurL2 C γ) z) :
    HasContDiffRepresentativeOn unitIntervalMeasure Set.univ fTrue := by
  -- Rewrite the source condition through self-adjointness, then apply smoothing.
  rw [h_source, gaussianBlurL2_adjoint_eq]
  exact gaussianBlurL2_hasSmoothRepresentative C γ z

end Fredholm1D
