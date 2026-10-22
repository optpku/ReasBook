/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory unitInterval
open unitInterval

noncomputable section

namespace ProbabilityTheory

section GeneralClaim

/- Remark 17.50 (i) is source-facing only: the uniqueness-up-to-scale statement for nonzero
invariant measures of an irreducible recurrent chain is deferred to Exercise 17.6.6 in the text.
This file keeps the formalization local to the explicit measures from part (ii). -/

end GeneralClaim

section BiasedWalk

/-- The geometric weighted counting measure on `ℤ` with singleton masses
`(r / (1 - r)) ^ x`, used as the second explicit measure in Remark 17.50. -/
def biasedSimpleRandomWalkGeometricInvariantMeasure (r : I) : Measure ℤ :=
  Measure.count.withDensity
    (fun x : ℤ ↦ ENNReal.ofReal ((((r : ℝ) / (1 - (r : ℝ))) : ℝ) ^ x))

/-- For Remark 17.50, the geometric weighted counting measure has singleton mass
`(r / (1 - r)) ^ x` at `{x}`. -/
theorem biasedSimpleRandomWalkGeometricInvariantMeasure_apply_singleton
    (r : I) (x : ℤ) :
    biasedSimpleRandomWalkGeometricInvariantMeasure r {x} =
      ENNReal.ofReal ((((r : ℝ) / (1 - (r : ℝ))) : ℝ) ^ x) := by
  -- Proof comment: on the discrete space `ℤ`, `withDensity` over counting measure evaluates to
  -- the density on singleton sets.
  rw [biasedSimpleRandomWalkGeometricInvariantMeasure]
  rw [withDensity_apply _ (measurableSet_singleton x)]
  simp

/-- Helper for Remark 17.50: at the symmetric parameter `r = 1 / 2`, the geometric weighted
counting density is constantly `1`. -/
lemma biasedSimpleRandomWalkGeometricDensity_eq_one_of_eq_half
    {r : I} (hr : (r : ℝ) = 1 / 2) :
    (fun x : ℤ ↦ ENNReal.ofReal ((((r : ℝ) / (1 - (r : ℝ))) : ℝ) ^ x)) = 1 := by
  funext x
  rw [hr]
  have hratio : ((((1 : ℝ) / 2) / (1 - (1 : ℝ) / 2)) : ℝ) = 1 := by
    norm_num
  rw [hratio]
  simp

/-- Helper for Remark 17.50: at the symmetric parameter `r = 1 / 2`, the geometric weighted
counting measure agrees with counting measure. -/
lemma biasedSimpleRandomWalkGeometricInvariantMeasure_eq_count_of_eq_half
    {r : I} (hr : (r : ℝ) = 1 / 2) :
    biasedSimpleRandomWalkGeometricInvariantMeasure r = (Measure.count : Measure ℤ) := by
  -- Proof comment: when `r = 1 / 2`, the geometric density is constantly `1`.
  rw [biasedSimpleRandomWalkGeometricInvariantMeasure,
    biasedSimpleRandomWalkGeometricDensity_eq_one_of_eq_half hr]
  exact withDensity_one (μ := (Measure.count : Measure ℤ))

/-- For Remark 17.50 (ii), in the asymmetric case `r ≠ 1 / 2`, the geometric weighted counting
measure is different from counting measure, since their singleton masses at `1` differ. -/
theorem biasedSimpleRandomWalkGeometricInvariantMeasure_ne_count
    (r : I) (hr0 : 0 < (r : ℝ)) (hr1 : (r : ℝ) < 1) (hrne : (r : ℝ) ≠ 1 / 2) :
    biasedSimpleRandomWalkGeometricInvariantMeasure r ≠ (Measure.count : Measure ℤ) := by
  intro hμ
  have hone :
      biasedSimpleRandomWalkGeometricInvariantMeasure r ({1} : Set ℤ) =
        (Measure.count : Measure ℤ) ({1} : Set ℤ) := by
    simp [hμ]
  rw [biasedSimpleRandomWalkGeometricInvariantMeasure_apply_singleton] at hone
  have hden_pos : 0 < 1 - (r : ℝ) := by
    linarith
  have hratio_nonneg : 0 ≤ (((r : ℝ) / (1 - (r : ℝ))) : ℝ) := by
    positivity
  have hone_real : max (((r : ℝ) / (1 - (r : ℝ))) : ℝ) 0 = 1 := by
    simpa using congrArg ENNReal.toReal hone
  have hone_ratio : (((r : ℝ) / (1 - (r : ℝ))) : ℝ) = 1 := by
    simpa [max_eq_left hratio_nonneg] using hone_real
  have hden : 1 - (r : ℝ) ≠ 0 := by
    linarith
  have hr_half : (r : ℝ) = 1 / 2 := by
    -- Proof comment: cross-multiplying the singleton-mass identity identifies the symmetric case.
    field_simp [hden] at hone_ratio
    linarith
  exact hrne hr_half

/-- Remark 17.50 (ii): for the biased nearest-neighbor walk on `ℤ`, the geometric invariant
measure differs from counting measure exactly in the asymmetric case `r ≠ 1 / 2`. -/
theorem biasedSimpleRandomWalk_invariantMeasure_iff
    (r : I) (hr0 : 0 < (r : ℝ)) (hr1 : (r : ℝ) < 1) :
    biasedSimpleRandomWalkGeometricInvariantMeasure r ≠ (Measure.count : Measure ℤ) ↔
      (r : ℝ) ≠ 1 / 2 := by
  constructor
  · intro hne hr
    -- Proof comment: the symmetric parameter makes the geometric weights constant, so the two
    -- explicit invariant measures coincide.
    exact hne (biasedSimpleRandomWalkGeometricInvariantMeasure_eq_count_of_eq_half hr)
  · intro hrne
    exact biasedSimpleRandomWalkGeometricInvariantMeasure_ne_count r hr0 hr1 hrne

end BiasedWalk

end ProbabilityTheory
