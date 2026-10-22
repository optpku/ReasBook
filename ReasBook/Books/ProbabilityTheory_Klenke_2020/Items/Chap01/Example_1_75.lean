/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

variable {n : ℕ} {A B : Set (EuclideanSpace ℝ (Fin n))}

/-- Example 1.75: On a measurable set `A ⊆ ℝ^n`, the conditioned Lebesgue measure `volume[|A]`
is the usual uniform distribution on `A`; in particular, on any subset `B ⊆ A` it evaluates to
`volume B / volume A`. -/
theorem volume_cond_apply_of_subset
    (hA : MeasurableSet A) (hBA : B ⊆ A) :
    volume[|A] B = volume B / volume A := by
  simpa [ENNReal.div_eq_inv_mul, Set.inter_eq_right.2 hBA] using
    (cond_apply hA (volume : Measure (EuclideanSpace ℝ (Fin n))) B)

/-- The uniform distribution on a set of positive finite Lebesgue measure is a probability
measure. -/
theorem volume_cond_isProbabilityMeasure
    (hA_pos : 0 < volume A) (hA_finite : volume A ≠ ⊤) :
    IsProbabilityMeasure (volume[|A] : Measure (EuclideanSpace ℝ (Fin n))) :=
  cond_isProbabilityMeasure_of_finite hA_pos.ne' hA_finite
