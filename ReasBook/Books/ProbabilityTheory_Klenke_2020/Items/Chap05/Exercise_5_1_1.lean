/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

noncomputable section

-- Proof sketch: upgrade the explicit density law to the canonical `HasPDF` statement, rewrite the
-- canonical pdf as `f` almost everywhere using `eq_of_map_eq_withDensity`, and then invoke the
-- owner LOTUS theorem `pdf.integral_mul_eq_integral`.
/-- Exercise 5.1.1 in textbook density form: if the law of `X` is `volume.withDensity f`, then its
expectation is the Lebesgue integral of `x ↦ x f(x)`. -/
theorem expectation_eq_integral_mul_density {X : Ω → ℝ} {f : ℝ → ℝ≥0}
    (hf : Measurable f)
    (hX_law : HasLaw X ((volume : Measure ℝ).withDensity (fun x ↦ (f x : ℝ≥0∞))) P) :
    P[X] = ∫ x, x * (f x : ℝ) ∂(volume : Measure ℝ) := by
  haveI : HasPDF X P :=
    hasPDF_of_map_eq_withDensity hX_law.aemeasurable
      (fun x : ℝ ↦ (f x : ℝ≥0∞)) hf.aemeasurable.coe_nnreal_ennreal hX_law.map_eq
  have hpdf : pdf X P volume =ᵐ[volume] fun x ↦ (f x : ℝ≥0∞) :=
    (pdf.eq_of_map_eq_withDensity (fun x : ℝ ↦ (f x : ℝ≥0∞))
      hf.aemeasurable.coe_nnreal_ennreal).1 hX_law.map_eq
  have hlotus :
      ∫ x : ℝ, x * (pdf X P volume x).toReal ∂(volume : Measure ℝ) = ∫ ω, X ω ∂P :=
    pdf.integral_mul_eq_integral
  calc
    P[X] = ∫ x, x * (pdf X P volume x).toReal ∂(volume : Measure ℝ) :=
      by simpa using hlotus.symm
    _ = ∫ x, x * (f x : ℝ) ∂(volume : Measure ℝ) := by
      refine integral_congr_ae ?_
      filter_upwards [hpdf] with x hx
      simp [hx]
