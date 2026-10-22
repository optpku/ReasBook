/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Definition_10_27

-- Declarations for this item will be appended below by the statement pipeline.

open ERealFunction

-- Proof sketch: an affine real-valued map on a real vector space is convex on every convex set; in
-- particular, on `Set.univ` the Jensen inequality is an equality for `x ↦ νx`.
/-- Example 10.32 (1): the linear function `x ↦ ν x` on `ℝ` is convex on the whole line. -/
theorem convexOn_univ_real_smul (ν : ℝ) :
    ConvexOn ℝ Set.univ (fun x : ℝ ↦ ν • x) := by
  simpa [smul_eq_mul] using ((LinearMap.mul ℝ ℝ) ν).convexOn convex_univ

-- Proof sketch: test the strict Jensen inequality at two distinct points, for instance `0` and
-- `1`, where `x ↦ νx` is affine and therefore attains equality along every convex combination.
/-- Example 10.32 (2): the linear function `x ↦ ν x` on `ℝ` is not strictly convex. -/
theorem not_strictConvexOn_univ_real_smul (ν : ℝ) :
    ¬ StrictConvexOn ℝ Set.univ (fun x : ℝ ↦ ν • x) := by
  intro h
  have hlt :=
    h.2 (by simp : (0 : ℝ) ∈ Set.univ) (by simp : (1 : ℝ) ∈ Set.univ)
      (by norm_num : (0 : ℝ) ≠ 1) (by norm_num : 0 < (1 / 2 : ℝ))
      (by norm_num : 0 < (1 / 2 : ℝ)) (by norm_num : (1 / 2 : ℝ) + (1 / 2 : ℝ) = 1)
  have hlt' := hlt
  simp [smul_eq_mul, div_eq_mul_inv, mul_comm] at hlt'

-- Proof sketch: for `x ≤ y`, compute
-- `ν (αx + (1 - α)y) = max (νx) (νy) - α * ν * |x - y|`, then use `α ≤ 1` to bound this by
-- `max (νx) (νy) - α * (1 - α) * ν * |x - y|`; rewrite the estimate in the `UniformlyQuasiconvex`
-- form for the `EReal`-valued lift of `x ↦ νx`.
/-- Example 10.32 (3): for `ν > 0`, the function `x ↦ ν x`, viewed as `EReal`-valued, is uniformly
quasiconvex with modulus `t ↦ ν t`. -/
theorem uniformlyQuasiconvex_real_smul (ν : ℝ) (hν : 0 < ν) :
    UniformlyQuasiconvex
      (fun x : ℝ ↦ ((ν • x : ℝ) : EReal))
      (fun t : NNReal ↦ (ν * (t : ℝ) : EReal)) := by
  rw [UniformlyQuasiconvex]
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro x
      simpa [smul_eq_mul, EReal.coe_mul] using (EReal.coe_ne_bot (ν * x))
    · refine ⟨0, ?_⟩
      rw [mem_dom_iff]
      exact EReal.coe_lt_top (ν * 0)
  · intro r s hrs
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hrs) (by exact_mod_cast hν.le)
  · intro r
    constructor
    · intro hr
      have hr' : ν * (r : ℝ) = 0 := by
        exact_mod_cast hr
      have : (r : ℝ) = 0 := (mul_eq_zero.mp hr').resolve_left hν.ne'
      exact_mod_cast this
    · rintro rfl
      simp
  · intro x y hx hy α hα0 hα1
    by_cases hxy : x ≤ y
    · have hyx_nonneg : 0 ≤ y - x := sub_nonneg.mpr hxy
      have habs : |x - y| = y - x := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          abs_of_nonpos (sub_nonpos.mpr hxy)
      have hmain :
          ν * (α * x + (1 - α) * y) + α * (1 - α) * (ν * (y - x)) ≤ max (ν * x) (ν * y) := by
        calc
          ν * (α * x + (1 - α) * y) + α * (1 - α) * (ν * (y - x))
              ≤ ν * (α * x + (1 - α) * y) + α * (ν * (y - x)) := by
                gcongr
                nlinarith [hα0, hα1]
          _ = ν * y := by ring
          _ = max (ν * x) (ν * y) := by
            rw [max_eq_right]
            gcongr
      have hgoal' :
          (↑(ν * (α * x + (1 - α) * y) + α * (1 - α) * (ν * (y - x))) : EReal) ≤
            ↑(max (ν * x) (ν * y)) := by
        exact_mod_cast hmain
      have hgoal'' :
          (↑(ν * (α * x + (1 - α) * y) + α * (1 - α) * (ν * (y - x))) : EReal) ≤
            max ((ν * x : ℝ) : EReal) ((ν * y : ℝ) : EReal) := by
        simpa only using hgoal'
      simpa [smul_eq_mul, Real.norm_eq_abs, habs, EReal.coe_add, EReal.coe_mul,
        mul_assoc, mul_left_comm, mul_comm] using hgoal''
    · have hyx : y ≤ x := le_of_not_ge hxy
      have hxy_nonneg : 0 ≤ x - y := sub_nonneg.mpr hyx
      have habs : |x - y| = x - y := abs_of_nonneg hxy_nonneg
      have hmain :
          ν * (α * x + (1 - α) * y) + α * (1 - α) * (ν * (x - y)) ≤ max (ν * x) (ν * y) := by
        calc
          ν * (α * x + (1 - α) * y) + α * (1 - α) * (ν * (x - y))
              ≤ ν * (α * x + (1 - α) * y) + (1 - α) * (ν * (x - y)) := by
                gcongr
                nlinarith [hα0, hα1]
          _ = ν * x := by ring
          _ = max (ν * x) (ν * y) := by
            rw [max_eq_left]
            gcongr
      have hgoal' :
          (↑(ν * (α * x + (1 - α) * y) + α * (1 - α) * (ν * (x - y))) : EReal) ≤
            ↑(max (ν * x) (ν * y)) := by
        exact_mod_cast hmain
      have hgoal'' :
          (↑(ν * (α * x + (1 - α) * y) + α * (1 - α) * (ν * (x - y))) : EReal) ≤
            max ((ν * x : ℝ) : EReal) ((ν * y : ℝ) : EReal) := by
        simpa only using hgoal'
      simpa [smul_eq_mul, Real.norm_eq_abs, habs, EReal.coe_add, EReal.coe_mul,
        mul_assoc, mul_left_comm, mul_comm] using hgoal''
