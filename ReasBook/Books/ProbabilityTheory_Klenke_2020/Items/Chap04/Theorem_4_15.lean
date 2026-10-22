/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/- Theorem 4.15: the canonical density-measure integrability criterion is
`MeasureTheory.integrable_withDensity_iff_integrable_smul`. For real-valued functions,
scalar multiplication is ordinary multiplication, giving the textbook formulation below. -/
recall integrable_withDensity_iff_integrable_smul

/-- Theorem 4.15 companion: for real-valued `g`, integrability with respect to the density measure
`μ.withDensity f` is equivalent to integrability of the product `g f` with respect to `μ`. -/
theorem integrable_withDensity_iff_integrable_mul {f : Ω → NNReal} (hf : Measurable f)
    {g : Ω → ℝ} :
    Integrable g (μ.withDensity fun ω ↦ f ω) ↔ Integrable (fun ω ↦ g ω * (f ω : ℝ)) μ := by
  have h : Integrable g (μ.withDensity fun ω ↦ f ω) ↔
      Integrable (fun ω ↦ f ω • g ω) μ :=
    integrable_withDensity_iff_integrable_smul hf
  simpa [NNReal.smul_def, mul_comm] using h

/- Theorem 4.15 companion: the canonical identity for integration against a density measure is
`MeasureTheory.integral_withDensity_eq_integral_smul`. -/
recall integral_withDensity_eq_integral_smul

/-- Theorem 4.15 companion: in the real-valued case, the density integral is the integral of the
product with the density. -/
theorem integral_withDensity_eq_integral_mul {f : Ω → NNReal} (hf : Measurable f) (g : Ω → ℝ) :
    ∫ ω, g ω ∂(μ.withDensity fun ω ↦ f ω) = ∫ ω, g ω * (f ω : ℝ) ∂μ := by
  have h :
      ∫ ω, g ω ∂(μ.withDensity fun ω ↦ f ω) = ∫ ω, f ω • g ω ∂μ :=
    integral_withDensity_eq_integral_smul hf g
  simpa [NNReal.smul_def, mul_comm] using h
