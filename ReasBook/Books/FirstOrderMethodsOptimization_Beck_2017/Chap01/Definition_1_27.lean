/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section

variable {n : ℕ}

/-- Definition 1.27: For a vector `x` in `ℝ^n`, modeled as `Fin n → ℝ`, `sgn x` is the
coordinatewise sign vector whose `i`-th entry is `1` when `x i ≥ 0` and `-1` when `x i < 0`. -/
noncomputable def sgn (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ if 0 ≤ x i then 1 else -1

/-- The coordinates of `sgn x` are `1` on nonnegative entries of `x` and `-1` on negative ones. -/
@[simp] theorem sgn_apply (x : Fin n → ℝ) (i : Fin n) :
    sgn x i = if 0 ≤ x i then 1 else -1 :=
  rfl

end
