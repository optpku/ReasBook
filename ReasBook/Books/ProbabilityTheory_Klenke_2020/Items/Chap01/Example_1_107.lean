/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped NNReal

noncomputable section

/- Example 1.107 (1): Item (i). The textbook density
`x ↦ θ ^ r / Γ(r) * x^(r - 1) * exp (-θ * x)` is the canonical mathlib measure
`ProbabilityTheory.gammaMeasure r θ`. This is mathlib's Gamma distribution with shape `r` and
rate `θ`; the source text calls `θ` a scale parameter. -/
recall ProbabilityTheory.gammaMeasure

/- For positive parameters, the canonical Gamma measure is a probability measure. -/
recall ProbabilityTheory.isProbabilityMeasure_gammaMeasure

/- Example 1.107 (2): Item (ii). The textbook Beta density is the canonical mathlib measure
`ProbabilityTheory.betaMeasure r s`. -/
recall ProbabilityTheory.betaMeasure

/- For positive parameters, the canonical Beta measure is a probability measure. -/
recall ProbabilityTheory.isProbabilityMeasureBeta

/-- Example 1.107 (3): Item (iii). For `a > 0`, the textbook centered Cauchy density is the
canonical mathlib measure `ProbabilityTheory.cauchyMeasure 0 (Real.toNNReal a)`. -/
theorem cauchyMeasure_eq_withDensity_of_pos {a : ℝ} (ha : 0 < a) :
    cauchyMeasure 0 (Real.toNNReal a) = volume.withDensity (cauchyPDF 0 (Real.toNNReal a)) := by
  apply cauchyMeasure_of_scale_ne_zero
  rw [Ne, Real.toNNReal_eq_zero]
  linarith

/- At zero scale, the canonical centered Cauchy measure degenerates to `Measure.dirac 0`. -/
recall ProbabilityTheory.cauchyMeasure_zero_scale

/-- For every positive textbook parameter `a`, the centered Cauchy distribution is a probability
measure. -/
theorem cauchyMeasure_isProbabilityMeasure_of_pos {a : ℝ} (ha : 0 < a) :
    IsProbabilityMeasure (cauchyMeasure 0 (Real.toNNReal a)) := by
  simpa [Real.toNNReal_of_nonneg (le_of_lt ha)] using
    (inferInstance : IsProbabilityMeasure (cauchyMeasure 0 (Real.toNNReal a)))
