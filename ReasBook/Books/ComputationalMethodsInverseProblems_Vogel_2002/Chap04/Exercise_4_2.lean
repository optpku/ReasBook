/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Exercise_4_2.Covariance

public section

universe u v

namespace ProbabilityTheory

/-- Exercise 4.2. If a real-valued random vector has independent
components and finite second moments, then its covariance matrix
`fun i j ↦ cov[X i, X j; μ]` is diagonal. -/
theorem isDiag_covarianceMatrix_of_iIndepFun
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} {X : ι → Ω → ℝ} (h_indep : iIndepFun X μ)
    (h_memLp : ∀ i, MeasureTheory.MemLp (X i) 2 μ) :
    Matrix.IsDiag (fun i j ↦ cov[X i, X j; μ]) := by
  intro i j hij
  exact h_indep.covariance_eq_zero h_memLp hij

end ProbabilityTheory
