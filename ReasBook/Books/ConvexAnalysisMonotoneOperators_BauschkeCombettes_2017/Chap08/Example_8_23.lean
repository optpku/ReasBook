/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section StrictConvex

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [StrictConvexSpace ℝ H]

-- Proof sketch: combine the strict convexity of `t ↦ t ^ p` on `[0,+∞)` from
-- `strictConvexOn_rpow hp` with the strict convexity of the norm geometry encoded by
-- `StrictConvexSpace`; equivalently, this is the `ψ(t) = p * t ^ (p - 1)` radial-integral
-- specialization of Example 8.22.
/-- Example 8.23 (1): for `p > 1`, the function `x ↦ ‖x‖ ^ p` is strictly convex on the whole
space of a strictly convex real normed space. -/
theorem strictConvexOn_norm_rpow (p : ℝ) (hp : 1 < p) :
    StrictConvexOn ℝ Set.univ (fun x : H ↦ ‖x‖ ^ p) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ hxy a b ha hb hab
  by_cases hnorm : ‖x‖ = ‖y‖
  · have hlt_norm : ‖a • x + b • y‖ < ‖x‖ := by
      refine norm_combo_lt_of_ne le_rfl ?_ hxy ha hb hab
      simp [hnorm]
    calc
      ‖a • x + b • y‖ ^ p < ‖x‖ ^ p :=
        Real.rpow_lt_rpow (norm_nonneg _) hlt_norm (lt_trans zero_lt_one hp)
      _ = a • (‖x‖ ^ p) + b • (‖y‖ ^ p) := by
        rw [hnorm, smul_eq_mul, smul_eq_mul, ← add_mul, hab, one_mul]
  · have hle_norm : ‖a • x + b • y‖ ≤ a * ‖x‖ + b * ‖y‖ := by
      simpa [smul_eq_mul] using
        convexOn_univ_norm.2 (by simp) (by simp) ha.le hb.le hab
    have hlt_rpow : (a * ‖x‖ + b * ‖y‖) ^ p < a * ‖x‖ ^ p + b * ‖y‖ ^ p := by
      exact (strictConvexOn_rpow hp).2 (by simp) (by simp) (by simp [hnorm]) ha hb
        (by simpa [smul_eq_mul] using hab)
    exact lt_of_le_of_lt (Real.rpow_le_rpow (norm_nonneg _) hle_norm (by positivity))
      (by simpa [smul_eq_mul] using hlt_rpow)

end StrictConvex

section NormInequality

variable {E : Type u} [SeminormedAddCommGroup E]

-- Proof sketch: apply the triangle inequality `‖x + y‖ ≤ ‖x‖ + ‖y‖`, raise both sides to the
-- power `p`, and then use the two-point `rpow` estimate valid for `1 ≤ p`
-- `NNReal.rpow_add_le_mul_rpow_add_rpow` transferred back to real norms.
/-- Example 8.23 (2): for `1 ≤ p`, the norm power satisfies
`‖x + y‖ ^ p ≤ 2 ^ (p - 1) * (‖x‖ ^ p + ‖y‖ ^ p)`. -/
theorem norm_add_rpow_le_two_rpow_sub_one_mul_add_rpow (p : ℝ) (hp : 1 ≤ p) (x y : E) :
    ‖x + y‖ ^ p ≤ (2 : ℝ) ^ (p - 1) * (‖x‖ ^ p + ‖y‖ ^ p) := by
  have h_triangle : ‖x + y‖ ≤ ‖x‖ + ‖y‖ := norm_add_le x y
  have h_rpow : ‖x + y‖ ^ p ≤ (‖x‖ + ‖y‖) ^ p :=
    Real.rpow_le_rpow (norm_nonneg _) h_triangle (by positivity)
  have h_mean : (‖x‖ + ‖y‖) ^ p ≤ (2 : ℝ) ^ (p - 1) * (‖x‖ ^ p + ‖y‖ ^ p) := by
    exact_mod_cast NNReal.rpow_add_le_mul_rpow_add_rpow ‖x‖₊ ‖y‖₊ hp
  exact h_rpow.trans h_mean

end NormInequality
