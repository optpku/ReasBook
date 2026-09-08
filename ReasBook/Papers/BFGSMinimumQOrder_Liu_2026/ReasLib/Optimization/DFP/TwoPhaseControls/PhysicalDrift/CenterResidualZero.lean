module

public import Mathlib.Analysis.Normed.Module.Basic

public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Data.Real.Basic

public section

noncomputable section

namespace DFP.TwoLeg.Mixed

/-- Helper for Appendix Lemma A.6: a vector-valued residual with a certified
    zero branch factors through its scalar denominator without unfolding the
    residual construction. -/
theorem smul_inv_factorization_of_zeroBranch
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : ℝ) (v : E) (hzero : d = 0 → v = 0) :
    v = d • (if d = 0 then 0 else d⁻¹ • v) := by
  by_cases hd : d = 0
  · rw [hd, hzero hd]
    simp
  · simp only [hd, if_false]
    rw [smul_smul]
    have hmul : d * d⁻¹ = (1 : ℝ) := by
      exact mul_inv_cancel₀ hd
    rw [hmul, one_smul]

/-- Helper for Appendix Lemma A.6: the scalar form of the zero-branch factorization
    matches the quotient syntax used by the mixed center residual. -/
theorem div_factorization_of_zeroBranch
    (d v : ℝ) (hzero : d = 0 → v = 0) :
    v = d * (if d = 0 then 0 else v / d) := by
  by_cases hd : d = 0
  · rw [hd, hzero hd]
    simp
  · simp only [hd, if_false]
    field_simp

/-- Helper for Appendix Lemma A.6: a cubic residual bound controls the norm of
    the normalized quotient on the nonzero branch. -/
theorem norm_inv_smul_le_of_norm_le_mul_abs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (d : ℝ) (v : E) (C : ℝ)
    (hbound : ‖v‖ ≤ C * |d|) (hd : d ≠ 0) :
    ‖d⁻¹ • v‖ ≤ C := by
  rw [norm_smul, Real.norm_eq_abs, abs_inv]
  have hnonneg : 0 ≤ |d|⁻¹ := inv_nonneg.mpr (abs_nonneg d)
  have hmul : |d|⁻¹ * ‖v‖ ≤ |d|⁻¹ * (C * |d|) := by
    exact mul_le_mul_of_nonneg_left hbound hnonneg
  calc
    |d|⁻¹ * ‖v‖ ≤ |d|⁻¹ * (C * |d|) := hmul
    _ = C := by
      field_simp [abs_ne_zero.mpr hd]

end DFP.TwoLeg.Mixed
