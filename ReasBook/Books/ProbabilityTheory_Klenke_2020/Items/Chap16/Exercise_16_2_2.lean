/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap16.Corollary_16_11

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

/-- The textbook density `x ↦ (1 - cos x) / (π x^2)`. -/
noncomputable def cosineDensity (x : ℝ) : ℝ :=
  (1 - Real.cos x) / (Real.pi * x ^ 2)

/-- The measure on `ℝ` with density `x ↦ (1 - cos x) / (π x^2)` with respect to Lebesgue
measure. -/
noncomputable def cosineDensityMeasure : Measure ℝ :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (cosineDensity x))

/-- Helper for Exercise 16.2.2: `cosineDensity` is the `a = 1` density used in
`triangularCharacteristicMeasure`. -/
lemma cosineDensity_eq_triangularCharacteristicDensity_one (x : ℝ) :
    cosineDensity x = (((1 / Real.pi) * (1 - Real.cos (1 * x))) / (1 * x ^ 2)) := by
  -- Separate the zero denominator case from the field simplification on `x ≠ 0`.
  by_cases hx : x = 0
  · simp [cosineDensity, hx]
  · have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
    -- Clear the nonzero denominators after rewriting the right-hand side into the same shape.
    rw [cosineDensity]
    field_simp [hx2, Real.pi_ne_zero]

/-- Helper for Exercise 16.2.2: `cosineDensityMeasure` is the `a = 1` case of
`triangularCharacteristicMeasure`. -/
lemma cosineDensityMeasure_eq_triangularCharacteristicMeasure_one :
    cosineDensityMeasure = triangularCharacteristicMeasure 1 := by
  -- Identify the two densities pointwise before applying `withDensity`.
  rw [cosineDensityMeasure, triangularCharacteristicMeasure]
  congr with x
  rw [cosineDensity_eq_triangularCharacteristicDensity_one]

/-- Helper for Exercise 16.2.2: the characteristic function of `cosineDensityMeasure` is the
tent function coming from Theorem 15.12 at `a = 1`. -/
lemma charFun_cosineDensityMeasure (t : ℝ) :
    charFun cosineDensityMeasure t = ((max (1 - |t|) 0 : ℝ) : ℂ) := by
  -- Rewrite the measure first, then specialize the Chapter 15 characteristic-function formula.
  rw [cosineDensityMeasure_eq_triangularCharacteristicMeasure_one]
  simpa using charFun_triangularCharacteristicMeasure 1 (by positivity) t

/-- The density measure `cosineDensityMeasure` has total mass `1`. -/
instance cosineDensityMeasure_isProbabilityMeasure :
    IsProbabilityMeasure cosineDensityMeasure := by
  -- Evaluate the characteristic function at `0` to read off the total mass.
  rw [cosineDensityMeasure_eq_triangularCharacteristicMeasure_one]
  rw [MeasureTheory.isProbabilityMeasure_iff_real, ← Complex.ofReal_inj]
  simpa [MeasureTheory.charFun_zero] using
    charFun_triangularCharacteristicMeasure 1 (by positivity) 0

/-- The probability distribution on `ℝ` with density `x ↦ (1 - cos x) / (π x^2)`. -/
noncomputable def cosineDensityProbabilityMeasure : ProbabilityMeasure ℝ :=
  ⟨cosineDensityMeasure, inferInstance⟩

-- Proof sketch: compute the Fourier transform of `cosineDensityMeasure`; it is the triangular
-- function `t ↦ max (1 - |t|) 0`, which vanishes at `t = 1`.
/-- The characteristic function of `cosineDensityProbabilityMeasure` vanishes at `t = 1`. -/
theorem charFun_cosineDensityProbabilityMeasure_one :
    charFun (cosineDensityProbabilityMeasure : Measure ℝ) (1 : ℝ) = 0 := by
  -- Evaluate the tent-function formula at `t = 1` on the underlying measure.
  calc
    charFun (cosineDensityProbabilityMeasure : Measure ℝ) (1 : ℝ) =
        ((max (1 - |(1 : ℝ)|) 0 : ℝ) : ℂ) := by
      simpa [cosineDensityProbabilityMeasure] using charFun_cosineDensityMeasure (1 : ℝ)
    _ = 0 := by norm_num

-- Proof sketch: if the law were infinitely divisible, then Corollary 16.11 would give a Gaussian
-- lower bound on the norm of its characteristic function. Evaluating that bound at `t = 1` shows
-- the characteristic function cannot vanish there, contradicting
-- `charFun_cosineDensityProbabilityMeasure_one`.
/-- Exercise 16.2.2: the probability distribution on `ℝ` with density
`x ↦ (1 - cos x) / (π x^2)` is not infinitely divisible. -/
theorem cosineDensityProbabilityMeasure_not_isInfinitelyDivisible :
    ¬ IsInfinitelyDivisible cosineDensityProbabilityMeasure := by
  intro hμ
  rcases charFun_gaussian_lower_bound_of_isInfinitelyDivisible hμ with ⟨γ, hγ, hbound⟩
  have hgaussPos : 0 < (1 / 2 : ℝ) * Real.exp (-γ * (1 : ℝ) ^ 2) := by
    positivity
  have hnormPos : 0 < ‖charFun (cosineDensityProbabilityMeasure : Measure ℝ) (1 : ℝ)‖ := by
    exact lt_of_lt_of_le hgaussPos (hbound 1)
  have hnonzero : charFun (cosineDensityProbabilityMeasure : Measure ℝ) (1 : ℝ) ≠ 0 := by
    exact norm_ne_zero_iff.mp (ne_of_gt hnormPos)
  exact hnonzero charFun_cosineDensityProbabilityMeasure_one

end MeasureTheory.ProbabilityMeasure
