/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open Finset

/- Text 2.16 lies in the finite-sum / Faulhaber arithmetic domain.

Source/core/bridge triage:
* source-facing: the textbook upper bound on `∑_{i=1}^k i^2`;
* core/canonical: mathlib's interval-level Faulhaber theorem `sum_Ico_pow`;
* bridge/view: `Ico_add_one_right_eq_Icc`, converting the textbook `Icc` sum to the
  canonical `Ico` owner.

Sampled owner-style declarations in this domain:
* mathlib `sum_Ico_pow`;
* mathlib `sum_range_pow`;
* mathlib `Ico_add_one_right_eq_Icc`;
* the downstream cast of `sum_Icc_sq_le_cubic_third` in `Text_2_15`.

Best owner abstraction:
* the source-facing interval sum on `Icc 1 k`, derived directly from `sum_Ico_pow`.

Primitive data:
* the canonical interval owner `sum_Ico_pow`.

Derived API:
* the textbook `Icc`-indexed cubic upper bound;
* its downstream `ℝ`-cast in `Text_2_15`.
-/

/-- Text 2.16: The sum of the squares from `1` to `k` is bounded above by `(k + 1)^3 / 3`. -/
-- Proof sketch: rewrite the textbook `Icc` sum as the canonical interval sum `sum_Ico_pow`,
-- expand the `p = 2` Faulhaber formula, and compare the resulting cubic polynomial with
-- `(k + 1)^3 / 3`.
theorem sum_Icc_sq_le_cubic_third (k : ℕ) :
    (∑ i ∈ Icc 1 k, (i : ℚ) ^ 2) ≤ ((k + 1 : ℚ) ^ 3) / 3 := by
  rw [← Ico_add_one_right_eq_Icc 1 k]
  rw [sum_Ico_pow]
  rw [sum_range_succ, sum_range_succ, sum_range_succ, sum_range_zero]
  norm_num [bernoulli'_zero, bernoulli'_one, bernoulli'_two]
  have hk : (0 : ℚ) ≤ k := by positivity
  nlinarith
