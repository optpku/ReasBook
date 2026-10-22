/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic

public section

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/-- The explicit affine comparison sequence `k ↦ ((k : ℝ) + 2) / 2` used in the FISTA rate
argument. -/
def fista_affine_comparison : ℕ → ℝ := fun k ↦ ((k : ℝ) + 2) / 2

/-- The explicit formula for `fista_affine_comparison`. -/
@[simp] theorem fista_affine_comparison_apply (k : ℕ) :
    fista_affine_comparison k = ((k : ℝ) + 2) / 2 := by
  -- Unfold the affine comparison sequence to expose its closed form.
  rfl

/-- Helper for Remark 10.35: the explicit affine comparison sequence dominates its displayed
affine lower bound. -/
theorem fista_affine_comparison_lower_bound (k : ℕ) :
    ((k : ℝ) + 2) / 2 ≤ fista_affine_comparison k := by
  -- Rewrite the sequence value to its explicit formula; the claimed lower bound is equality.
  simpa only [fista_affine_comparison_apply] using
    (le_rfl : ((k : ℝ) + 2) / 2 ≤ ((k : ℝ) + 2) / 2)

/-- Remark 10.35 (2): the explicit affine comparison sequence satisfies the quadratic recursion
inequality used in the FISTA `O(1 / k^2)` estimate. -/
theorem fista_affine_comparison_quadratic_recursion_bound (k : ℕ) :
    fista_affine_comparison (k + 1) ^ (2 : ℕ) - fista_affine_comparison (k + 1) ≤
      fista_affine_comparison k ^ (2 : ℕ) := by
  -- Rewrite the recursive term as the previous affine value plus `1 / 2`.
  have stepIdentity :
      fista_affine_comparison (k + 1) ^ (2 : ℕ) - fista_affine_comparison (k + 1) =
        fista_affine_comparison k ^ (2 : ℕ) - (1 / 4 : ℝ) := by
    -- Both sides are explicit quadratic polynomials in `k`, so `ring` closes the identity.
    rw [fista_affine_comparison_apply, fista_affine_comparison_apply]
    norm_num
    ring
  -- After the identity, the goal is the obvious fact that subtracting `1 / 4` decreases a real.
  rw [stepIdentity]
  linarith
