/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Probability.CDF
public import Mathlib.Probability.Density
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.IdentDistrib
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Definition_4_2.DiscreteRandomVariable

public section

noncomputable section

open scoped BigOperators ProbabilityTheory

namespace ProbabilityTheory

universe u

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : MeasureTheory.Measure Ω}

/-- The expectation `μ[X]` of a real random variable is the integral of `x` against its law
`MeasureTheory.Measure.map X μ`. -/
theorem expectation_eq_integral_map
    {X : Ω → ℝ} (hX : Measurable X) :
    μ[X] = ∫ x, x ∂(MeasureTheory.Measure.map X μ) := by
  simpa using
    (MeasureTheory.integral_map hX.aemeasurable aestronglyMeasurable_id).symm

section

variable [MeasureTheory.IsProbabilityMeasure μ]

/-- The measure attached to the cumulative distribution function of the law of a measurable real
random variable is the law itself. -/
theorem cdf_measure_map_eq
    {X : Ω → ℝ} (hX : Measurable X) :
    (ProbabilityTheory.cdf (MeasureTheory.Measure.map X μ)).measure =
      MeasureTheory.Measure.map X μ := by
  simpa using
    (@ProbabilityTheory.measure_cdf (MeasureTheory.Measure.map X μ)
      (MeasureTheory.Measure.isProbabilityMeasure_map hX.aemeasurable))

/-- Definition 4.4 (1). The expectation `μ[X]` of a real random variable agrees with the integral
of `x` against the measure attached to the cumulative distribution function of its law. -/
theorem expectation_eq_integral_cdfMeasure
    {X : Ω → ℝ} (hX : Measurable X) :
    μ[X] = ∫ x, x ∂(ProbabilityTheory.cdf (MeasureTheory.Measure.map X μ)).measure := by
  rw [cdf_measure_map_eq hX]
  exact expectation_eq_integral_map hX

end

section

variable [MeasureTheory.IsProbabilityMeasure μ]

/-- Definition 4.4 (2). For a continuous real random variable, the expectation agrees with the
integral of `x` against its probability density function with respect to volume. -/
theorem expectation_eq_integral_pdf
    {X : Ω → ℝ} [MeasureTheory.HasPDF X μ] :
    μ[X] = ∫ x, x * (MeasureTheory.pdf X μ MeasureTheory.volume x).toReal := by
  symm
  simpa using
    (MeasureTheory.pdf.integral_mul_eq_integral :
      ∫ x, x * (MeasureTheory.pdf X μ MeasureTheory.volume x).toReal = μ[X])

/- The law-level density identity underlying Definition 4.4 (2) is the canonical measure-theoretic
statement `MeasureTheory.Measure.map X μ = MeasureTheory.volume.withDensity
  (MeasureTheory.pdf X μ MeasureTheory.volume)`. -/
#check MeasureTheory.map_eq_withDensity_pdf

end

/-- Definition 4.4 (3). For a discrete real random variable, the expectation is the weighted sum
of its point masses. -/
theorem expectation_eq_tsum_discretePmf
    {X : Ω → ℝ} (h_disc : ProbabilityTheory.IsDiscreteRandomVariable μ X)
    (h_int : MeasureTheory.Integrable X μ) :
    μ[X] = ∑' x : ℝ, x * ((ProbabilityTheory.discretePmf h_disc) x).toReal := by
  have h_ident :
      ProbabilityTheory.IdentDistrib X id μ (ProbabilityTheory.discretePmf h_disc).toMeasure :=
    (ProbabilityTheory.discretePmf_spec h_disc).identDistrib ProbabilityTheory.HasLaw.id
  have h_int_pmf :
      MeasureTheory.Integrable id (ProbabilityTheory.discretePmf h_disc).toMeasure :=
    h_ident.integrable_iff.mp h_int
  rw [(ProbabilityTheory.discretePmf_spec h_disc).integral_eq]
  simpa [smul_eq_mul, mul_comm] using
    PMF.integral_eq_tsum (ProbabilityTheory.discretePmf h_disc) id h_int_pmf

/-- Definition 4.4 (4). Expectation is linear on real random variables. -/
theorem expectation_add_smul
    (a b : ℝ) {X Y : Ω → ℝ}
    (hX : MeasureTheory.Integrable X μ) (hY : MeasureTheory.Integrable Y μ) :
    μ[a • X + b • Y] = a • μ[X] + b • μ[Y] := by
  have hX_smul : ∫ x, (a • X) x ∂μ = a • μ[X] := by
    simpa using hX.integral_smul a
  have hY_smul : ∫ x, (b • Y) x ∂μ = b • μ[Y] := by
    simpa using hY.integral_smul b
  have h_add :
      ∫ x, (a • X) x + (b • Y) x ∂μ = a • μ[X] + b • μ[Y] := by
    rw [MeasureTheory.integral_add (hX.smul a) (hY.smul b), hX_smul, hY_smul]
  simpa using h_add

/-- Expectation of the sum of two integrable real random variables is the sum of their
expectations. -/
theorem expectation_add
    {X Y : Ω → ℝ} (hX : MeasureTheory.Integrable X μ) (hY : MeasureTheory.Integrable Y μ) :
    μ[X + Y] = μ[X] + μ[Y] := by
  simpa using MeasureTheory.integral_add hX hY

/-- Expectation of a scalar multiple of an integrable real random variable scales by the same
scalar. -/
theorem expectation_smul
    (a : ℝ) {X : Ω → ℝ} (hX : MeasureTheory.Integrable X μ) :
    μ[a • X] = a • μ[X] := by
  simpa using hX.integral_smul a

end

end ProbabilityTheory
