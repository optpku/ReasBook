/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω}

/- Theorem 4.8 (1): a measurable nonnegative extended-real function has zero lower Lebesgue
integral if and only if it vanishes almost everywhere. -/
recall MeasureTheory.lintegral_eq_zero_iff

/- The canonical mathlib form of Theorem 4.8 (2) assumes only that the lower integral is not
equal to `∞`. -/
recall MeasureTheory.ae_lt_top

/-- Theorem 4.8: if a measurable map `f : Ω → [0, ∞]` has finite lower Lebesgue integral,
then `f` is finite almost everywhere. -/
theorem ae_lt_top_of_lintegral_lt_top {f : Ω → ℝ≥0∞} (hf : Measurable f)
    (hfin : (∫⁻ ω, f ω ∂μ) < ∞) : ∀ᵐ ω ∂μ, f ω < ∞ :=
  ae_lt_top hf hfin.ne
