/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 4.3: rewrite the relaxed affine displacement from a fixed point as the
original displacement plus a scaled residual. -/
private lemma relaxed_sub_fixedPoint_eq_add_smul_residual {D : Set H} (T : D → H) (lam : ℝ)
    (x y : D) :
    ((1 - lam) • (x : H) + lam • T x) - (y : H) = ((x : H) - y) + lam • (T x - (x : H)) := by
  simp [sub_eq_add_neg, add_smul, add_assoc, add_left_comm, add_comm]

/-- Helper for Proposition 4.3: firm quasinonexpansiveness forces the cross term in the textbook
expansion to be at most the negative residual norm square. -/
private lemma inner_le_neg_residual_norm_sq_of_firmly_quasinonexpansive {D : Set H} {T : D → H}
    (hT : IsFirmlyQuasinonexpansiveOn T) (x y : D) (hy : T y = (y : H)) :
    inner ℝ ((x : H) - y) (T x - (x : H)) ≤ -‖T x - (x : H)‖ ^ 2 := by
  -- Expand the firm inequality at `x` and the fixed point `y`.
  have hineq := hT x y hy
  have hexpand :
      ‖T x - (y : H)‖ ^ 2 =
        ‖(x : H) - y‖ ^ 2 + 2 * inner ℝ ((x : H) - y) (T x - (x : H)) +
          ‖T x - (x : H)‖ ^ 2 := by
    -- Rewrite `T x - y` as `(x - y) + (T x - x)` and expand the squared norm.
    rw [show T x - (y : H) = ((x : H) - y) + (T x - (x : H)) by
      abel_nf]
    simpa using norm_add_sq_real ((x : H) - y) (T x - (x : H))
  have hres : ‖(x : H) - T x‖ ^ 2 = ‖T x - (x : H)‖ ^ 2 := by
    -- The two residuals differ only by sign.
    rw [norm_sub_rev]
  -- Cancelling the common `‖x - y‖^2` term yields the desired cross-term bound.
  nlinarith [hineq, hexpand, hres]

/-- Helper for Proposition 4.3: exact expansion of the relaxed affine displacement squared norm. -/
private lemma sq_norm_relaxed_sub_fixedPoint_eq {D : Set H} {T : D → H} (lam : ℝ) (x y : D) :
    ‖((1 - lam) • (x : H) + lam • T x) - (y : H)‖ ^ 2 =
      ‖(x : H) - y‖ ^ 2 +
        2 * lam * inner ℝ ((x : H) - y) (T x - (x : H)) +
        lam ^ 2 * ‖T x - (x : H)‖ ^ 2 := by
  -- Rewrite the relaxed displacement into the affine textbook form.
  rw [relaxed_sub_fixedPoint_eq_add_smul_residual]
  -- Expand `‖u + lam • v‖^2` and normalize the scalar terms.
  rw [norm_add_sq_real]
  rw [real_inner_smul_right]
  rw [show ‖lam • (T x - (x : H))‖ ^ 2 = lam ^ 2 * ‖T x - (x : H)‖ ^ 2 by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]]
  ring

/-- Proposition 4.3: if `T` is firmly quasinonexpansive on `D`, then every nonnegative
relaxation `x ↦ (1 - λ) • x + λ • T x` satisfies the estimate
`‖((1 - λ) • x + λ • T x) - y‖^2 ≤ ‖x - y‖^2 - λ (2 - λ) ‖T x - x‖^2`
at every fixed point `y` of `T` in `D`. -/
-- Proof sketch: expand `‖((1 - lam) • x + lam • T x) - y‖ ^ 2` as
-- `‖(x - y) + lam • (T x - x)‖ ^ 2`, use firm quasinonexpansiveness to bound the cross term by
-- `-‖T x - x‖ ^ 2`, and simplify the resulting quadratic polynomial in `lam`.
theorem sq_norm_relaxedMap_sub_fixedPoint_le {D : Set H} {T : D → H}
    (hT : IsFirmlyQuasinonexpansiveOn T) {lam : ℝ} (hlam : 0 ≤ lam) (x y : D)
    (hy : T y = (y : H)) :
    ‖((1 - lam) • (x : H) + lam • T x) - (y : H)‖ ^ 2 ≤
      ‖(x : H) - y‖ ^ 2 - lam * (2 - lam) * ‖T x - (x : H)‖ ^ 2 := by
  rw [sq_norm_relaxed_sub_fixedPoint_eq]
  have hinner :=
    inner_le_neg_residual_norm_sq_of_firmly_quasinonexpansive hT x y hy
  have hcross :
      2 * lam * inner ℝ ((x : H) - y) (T x - (x : H)) ≤
        -(2 * lam) * ‖T x - (x : H)‖ ^ 2 := by
    nlinarith
  nlinarith [hcross]

end
