/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_27.SecondMoment
public import Mathlib.LinearAlgebra.Matrix.Trace

public section

noncomputable section

namespace ProbabilityTheory

universe u v

/-- A finite-measure companion to Proposition 4.29 on the source-facing owner
`secondMomentMatrix μ X`. -/
theorem integral_sqNorm_eq_trace_secondMomentMatrix
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω] [Fintype ι]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsFiniteMeasure μ]
    {X : Ω → EuclideanSpace ℝ ι} (hX : MeasureTheory.MemLp X 2 μ) :
    ∫ ω, ‖X ω‖ ^ 2 ∂μ = Matrix.trace (secondMomentMatrix μ X) := by
  classical
  -- Extract the scalar `L²` control for each coordinate of the random vector.
  have hXcoord : ∀ i, MeasureTheory.MemLp (fun ω ↦ X ω i) 2 μ :=
    MeasureTheory.memLp_piLp_iff.mp hX
  -- Each coordinate square is integrable, so the finite sum may pass through the integral.
  have hCoordSq : ∀ i, MeasureTheory.Integrable (fun ω ↦ (X ω i) ^ 2) μ := by
    intro i
    simpa [Real.norm_eq_abs, sq_abs] using (hXcoord i).integrable_norm_pow'
  -- Normalize both sides to the same sum of coordinatewise second moments.
  calc
    ∫ ω, ‖X ω‖ ^ 2 ∂μ = ∫ ω, ∑ i, (X ω i) ^ 2 ∂μ := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with ω
      simp [EuclideanSpace.real_norm_sq_eq]
    _ = ∑ i, ∫ ω, (X ω i) ^ 2 ∂μ := by
      simpa using
        (MeasureTheory.integral_finsetSum (s := Finset.univ)
          (f := fun i ω ↦ (X ω i) ^ 2) fun i _ ↦ hCoordSq i)
    _ = Matrix.trace (secondMomentMatrix μ X) := by
      symm
      simp [Matrix.trace, ProbabilityTheory.secondMomentMatrix_apply, pow_two]

/-- Proposition 4.29. If a finite real random vector has finite expected squared components, then
the expected squared Euclidean norm of `X` equals the trace of its uncentered second-moment matrix
`secondMomentMatrix μ X`. This is the probability-measure specialization of
`integral_sqNorm_eq_trace_secondMomentMatrix`. -/
theorem expected_sqNorm_eq_trace_secondMomentMatrix
    {Ω : Type u} {ι : Type v} [MeasurableSpace Ω] [Fintype ι]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → EuclideanSpace ℝ ι} (hX : MeasureTheory.MemLp X 2 μ) :
    ∫ ω, ‖X ω‖ ^ 2 ∂μ = Matrix.trace (secondMomentMatrix μ X) :=
  integral_sqNorm_eq_trace_secondMomentMatrix hX

end ProbabilityTheory
