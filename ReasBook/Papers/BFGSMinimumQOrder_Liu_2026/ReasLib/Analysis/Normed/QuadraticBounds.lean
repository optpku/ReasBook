module

public import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Quadratic bounds derived from norm intervals

This module packages elementary interval arithmetic for quantities controlled
by the norm of a vector.  The results are independent of any optimization
algorithm.
-/

public section

/-- Squaring a nonnegative norm interval preserves its endpoint ordering. -/
theorem normSq_mem_Icc_of_norm_mem_Icc
    {E : Type*} [SeminormedAddCommGroup E]
    {s : E} {r c C : ℝ}
    (hr : 0 ≤ r) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hstep : ‖s‖ ∈ Set.Icc (c * r) (C * r)) :
    ‖s‖ ^ 2 ∈ Set.Icc ((c * r) ^ 2) ((C * r) ^ 2) := by
  have hcr : 0 ≤ c * r := mul_nonneg hc hr
  have hCr : 0 ≤ C * r := mul_nonneg hC hr
  constructor
  · nlinarith [hstep.1, norm_nonneg s]
  · nlinarith [hstep.2, norm_nonneg s]

/-- A norm interval and a quadratic comparison in that norm give a quadratic
interval at the underlying scale. -/
theorem quadraticQuantity_mem_Icc_of_norm_mem_Icc
    {E : Type*} [SeminormedAddCommGroup E]
    {s : E} {r c C α β q : ℝ}
    (hr : 0 ≤ r) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hstep : ‖s‖ ∈ Set.Icc (c * r) (C * r))
    (hquadratic : q ∈ Set.Icc (α * ‖s‖ ^ 2) (β * ‖s‖ ^ 2)) :
    q ∈ Set.Icc ((α * c ^ 2) * r ^ 2) ((β * C ^ 2) * r ^ 2) := by
  have hsquare := normSq_mem_Icc_of_norm_mem_Icc hr hc hC hstep
  constructor
  · calc
      (α * c ^ 2) * r ^ 2 = α * (c * r) ^ 2 := by ring
      _ ≤ α * ‖s‖ ^ 2 := mul_le_mul_of_nonneg_left hsquare.1 hα
      _ ≤ q := hquadratic.1
  · calc
      q ≤ β * ‖s‖ ^ 2 := hquadratic.2
      _ ≤ β * (C * r) ^ 2 := mul_le_mul_of_nonneg_left hsquare.2 hβ
      _ = (β * C ^ 2) * r ^ 2 := by ring

/-- Separate positive norm and decrease intervals give a uniform interval for
their squared-norm-to-decrease ratio. -/
theorem squaredNorm_div_mem_Icc_of_norm_mem_Icc
    {E : Type*} [SeminormedAddCommGroup E]
    {s : E} {r c C cq CQ q : ℝ}
    (hr : 0 < r) (hc : 0 ≤ c) (hC : 0 ≤ C)
    (hcq : 0 < cq) (hCQ : 0 < CQ)
    (hstep : ‖s‖ ∈ Set.Icc (c * r) (C * r))
    (hdecrease : q ∈ Set.Icc (cq * r ^ 2) (CQ * r ^ 2)) :
    ‖s‖ ^ 2 / q ∈ Set.Icc (c ^ 2 / CQ) (C ^ 2 / cq) := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  have hq : 0 < q := lt_of_lt_of_le (mul_pos hcq hr2) hdecrease.1
  have hcr : 0 ≤ c * r := mul_nonneg hc hr.le
  have hCr : 0 ≤ C * r := mul_nonneg hC hr.le
  have hnormSqLower : (c * r) ^ 2 ≤ ‖s‖ ^ 2 := by
    nlinarith [hstep.1, norm_nonneg s]
  have hnormSqUpper : ‖s‖ ^ 2 ≤ (C * r) ^ 2 := by
    nlinarith [hstep.2, norm_nonneg s]
  have hlowCoeff : 0 ≤ c ^ 2 / CQ := div_nonneg (sq_nonneg c) hCQ.le
  have hhighCoeff : 0 ≤ C ^ 2 / cq := div_nonneg (sq_nonneg C) hcq.le
  constructor
  · apply (le_div_iff₀ hq).2
    calc
      (c ^ 2 / CQ) * q ≤ (c ^ 2 / CQ) * (CQ * r ^ 2) :=
        mul_le_mul_of_nonneg_left hdecrease.2 hlowCoeff
      _ = (c * r) ^ 2 := by
        field_simp [ne_of_gt hCQ]
      _ ≤ ‖s‖ ^ 2 := hnormSqLower
  · apply (div_le_iff₀ hq).2
    calc
      ‖s‖ ^ 2 ≤ (C * r) ^ 2 := hnormSqUpper
      _ = (C ^ 2 / cq) * (cq * r ^ 2) := by
        field_simp [ne_of_gt hcq]
      _ ≤ (C ^ 2 / cq) * q :=
        mul_le_mul_of_nonneg_left hdecrease.1 hhighCoeff
