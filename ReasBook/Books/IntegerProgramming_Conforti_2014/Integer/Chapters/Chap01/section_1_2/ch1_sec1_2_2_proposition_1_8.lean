module

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

public import Mathlib.Data.Real.Basic

public section

section Proposition18

/-- Rewriting the tableau row of Proposition 1.8 isolates the Gomory-cut left-hand side
as the affine expression `(11 / 8) - x1 + x5`. -/
theorem tableauRowCut_eq_rowRhs
    (x1 : ℤ) (x4 x5 : ℝ)
    (hrow : (x1 : ℝ) + (1 / 8 : ℝ) * x4 - (1 / 4 : ℝ) * x5 = (11 / 8 : ℝ)) :
    (1 / 8 : ℝ) * x4 + (3 / 4 : ℝ) * x5 = (11 / 8 : ℝ) - (x1 : ℝ) + x5 := by
  have hrow' : (1 / 8 : ℝ) * x4 - (1 / 4 : ℝ) * x5 = (11 / 8 : ℝ) - (x1 : ℝ) := by
    linarith
  calc
    (1 / 8 : ℝ) * x4 + (3 / 4 : ℝ) * x5 = (1 / 8 : ℝ) * x4 - (1 / 4 : ℝ) * x5 + x5 := by
      ring
    _ = (11 / 8 : ℝ) - (x1 : ℝ) + x5 := by rw [hrow']

/-- Proposition 1.8 (1). If `x4 ≥ 0`, `x5 ≥ 0`, `x1 ∈ ℤ`, and
`(x1 : ℝ) + (1 / 8 : ℝ) * x4 - (1 / 4 : ℝ) * x5 = (11 / 8 : ℝ)`, then
`(1 / 8 : ℝ) * x4 + (3 / 4 : ℝ) * x5 ≥ (3 / 8 : ℝ)`. -/
theorem tableauRowCutValid
    (x1 : ℤ) (x4 x5 : ℝ)
    (hx4_nonneg : 0 ≤ x4)
    (hx5_nonneg : 0 ≤ x5)
    (hrow : (x1 : ℝ) + (1 / 8 : ℝ) * x4 - (1 / 4 : ℝ) * x5 = (11 / 8 : ℝ)) :
    (1 / 8 : ℝ) * x4 + (3 / 4 : ℝ) * x5 ≥ (3 / 8 : ℝ) := by
  have hcut_eq := tableauRowCut_eq_rowRhs x1 x4 x5 hrow
  have hx1_cases : x1 ≤ 1 ∨ 1 < x1 := le_or_gt x1 1
  cases hx1_cases with
  | inl hx1_le =>
      have hx1_le' : (x1 : ℝ) ≤ 1 := by
        exact_mod_cast hx1_le
      have hbound : (3 / 8 : ℝ) ≤ (11 / 8 : ℝ) - (x1 : ℝ) + x5 := by
        have hbase : (3 / 8 : ℝ) ≤ (11 / 8 : ℝ) - (x1 : ℝ) := by
          linarith
        exact le_trans hbase (le_add_of_nonneg_right hx5_nonneg)
      rw [hcut_eq]
      exact hbound
  | inr hx1_gt =>
      have hx1_ge : (2 : ℤ) ≤ x1 := by
        simpa using (Int.add_one_le_iff.mpr hx1_gt)
      have hx1_ge' : (2 : ℝ) ≤ (x1 : ℝ) := by
        exact_mod_cast hx1_ge
      have hx5_lower : 4 * (x1 : ℝ) - (11 / 2 : ℝ) ≤ x5 := by
        have hrow_ineq : (x1 : ℝ) - (1 / 4 : ℝ) * x5 ≤ (11 / 8 : ℝ) := by
          linarith
        linarith
      have hbound : (3 / 8 : ℝ) ≤ (11 / 8 : ℝ) - (x1 : ℝ) + x5 := by
        linarith
      rw [hcut_eq]
      exact hbound

/-- Under the source substitutions for `x4` and `x5`, the Gomory cut left-hand side simplifies
to the affine expression `35 / 8 - x1 - x2`. -/
theorem tableauRowCut_eq_afterSubstitution
    (x1 x2 x4 x5 : ℝ)
    (hx4 : x4 = 17 - 8 * x1 - 2 * x2)
    (hx5 : x5 = 3 - x2) :
    (1 / 8 : ℝ) * x4 + (3 / 4 : ℝ) * x5 = (35 / 8 : ℝ) - x1 - x2 := by
  rw [hx4, hx5]
  ring

/-- Proposition 1.8 (2). If `x4 = 17 - 8 * x1 - 2 * x2` and `x5 = 3 - x2`, then
`(1 / 8 : ℝ) * x4 + (3 / 4 : ℝ) * x5 ≥ (3 / 8 : ℝ)` is equivalent to `x1 + x2 ≤ 4`. -/
theorem tableauRowCutIffOriginalBound
    (x1 x2 x4 x5 : ℝ)
    (hx4 : x4 = 17 - 8 * x1 - 2 * x2)
    (hx5 : x5 = 3 - x2) :
    ((1 / 8 : ℝ) * x4 + (3 / 4 : ℝ) * x5 ≥ (3 / 8 : ℝ) ↔ x1 + x2 ≤ 4) := by
  have hcut_eq := tableauRowCut_eq_afterSubstitution x1 x2 x4 x5 hx4 hx5
  constructor
  · intro h
    rw [hcut_eq] at h
    linarith
  · intro h
    rw [hcut_eq]
    linarith

end Proposition18
