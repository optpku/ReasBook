/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

universe u

section

variable {Ω : Type u} {n : ℕ}

/-- The normalized finite empirical measure attached to the sample values
`X₁(ω), …, X_{n+1}(ω)`. -/
private noncomputable def empiricalMeasure (X : Fin (n + 1) → Ω → ℝ) (ω : Ω) : Measure ℝ :=
  (((n + 1 : ℕ) : ℝ≥0∞)⁻¹) • ∑ i : Fin (n + 1), Measure.dirac (X i ω)

private theorem empiricalMeasure_isProbabilityMeasure (X : Fin (n + 1) → Ω → ℝ) (ω : Ω) :
    IsProbabilityMeasure (empiricalMeasure X ω) := by
  refine ⟨?_⟩
  have hne : (((n + 1 : ℕ) : ℝ≥0∞)) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have htop : (((n + 1 : ℕ) : ℝ≥0∞)) ≠ ∞ := by
    simp
  simpa [empiricalMeasure] using ENNReal.inv_mul_cancel hne htop

/-- Definition 5.22: For real random variables `X_1, ..., X_{n + 1}`, the empirical distribution
function is the random map sending `ω` to the empirical cdf
`x ↦ (1 / (n + 1)) ∑_{i=1}^{n + 1} 1_{(-∞,x]}(X_i(ω))`, formalized as the average of the
indicator values `if X i ω ≤ x then 1 else 0` over the finite family
`Fin (n + 1) → Ω → ℝ`. -/
noncomputable def empiricalDistributionFunction (X : Fin (n + 1) → Ω → ℝ) : Ω → ℝ → ℝ :=
  fun ω x ↦ cdf (empiricalMeasure X ω) x

/-- The empirical distribution function takes values in the unit interval. -/
theorem empiricalDistributionFunction_mem_Icc (X : Fin (n + 1) → Ω → ℝ) (x : ℝ) (ω : Ω) :
    empiricalDistributionFunction X ω x ∈ Set.Icc (0 : ℝ) 1 := by
  haveI : IsProbabilityMeasure (empiricalMeasure X ω) := empiricalMeasure_isProbabilityMeasure X ω
  constructor
  · simpa [empiricalDistributionFunction] using cdf_nonneg (empiricalMeasure X ω) x
  · simpa [empiricalDistributionFunction] using cdf_le_one (empiricalMeasure X ω) x

/-- The empirical distribution function is the empirical average of the lower-interval indicators.
-/
theorem empiricalDistributionFunction_apply (X : Fin (n + 1) → Ω → ℝ) (ω : Ω) (x : ℝ) :
    empiricalDistributionFunction X ω x =
      (∑ i : Fin (n + 1), if X i ω ≤ x then (1 : ℝ) else 0) / (n + 1 : ℝ) := by
  haveI : IsProbabilityMeasure (empiricalMeasure X ω) := empiricalMeasure_isProbabilityMeasure X ω
  rw [empiricalDistributionFunction, ProbabilityTheory.cdf_eq_real, Measure.real_def, empiricalMeasure,
    Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  have hdirac :
      ((∑ i : Fin (n + 1), Measure.dirac (X i ω)) (Set.Iic x)).toReal =
        ∑ i : Fin (n + 1), if X i ω ≤ x then (1 : ℝ) else 0 := by
    rw [Measure.finset_sum_apply]
    rw [ENNReal.toReal_sum fun i _ ↦ measure_ne_top _ _]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases hix : X i ω ≤ x
    · simp [hix]
    · simp [hix]
  have hnat : (((n + 1 : ℕ) : ℝ≥0∞)).toReal = (n + 1 : ℝ) := by
    simpa using ENNReal.toReal_natCast (n + 1)
  calc
    ((((n + 1 : ℕ) : ℝ≥0∞)⁻¹).toReal) *
        (((∑ i : Fin (n + 1), Measure.dirac (X i ω)) (Set.Iic x)).toReal)
      = (((n + 1 : ℕ) : ℝ≥0∞)⁻¹).toReal *
          ∑ i : Fin (n + 1), if X i ω ≤ x then (1 : ℝ) else 0 := by
        rw [hdirac]
    _ = (n + 1 : ℝ)⁻¹ * ∑ i : Fin (n + 1), if X i ω ≤ x then (1 : ℝ) else 0 := by
      rw [ENNReal.toReal_inv, hnat]
    _ = (∑ i : Fin (n + 1), if X i ω ≤ x then (1 : ℝ) else 0) / (n + 1 : ℝ) := by
      rw [div_eq_mul_inv, mul_comm]

end
