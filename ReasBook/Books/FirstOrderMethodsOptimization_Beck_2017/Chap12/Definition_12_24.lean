/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open WithLp

noncomputable section

/- Definition 12.24 is a `bridge/view`: the scalar penalty
`h(x, y, z) = √((x - y)^2 + (x - z)^2)` is exactly the canonical `L²` norm of the difference pair
`(x - y, x - z)`.

Domain sampling in the surrounding normed-space API and Chapter 12 TV files gives:
- `core/canonical`: `WithLp 2 (ℝ × ℝ)` together with `WithLp.prod_norm_eq_of_L2`;
- `bridge/view`: the textbook square-root expansion of that canonical norm;
- downstream chapter alignment: Proposition 12.4 already uses the same `WithLp 2` owner for
  isotropic horizontal/vertical TV pairs.

This file should therefore reuse the canonical `L²` owner directly instead of keeping a parallel
local wrapper for the same norm expression. -/

/- Definition 12.24: the three-variable penalty is the `L²` norm of the pair of differences from
`x` to `y` and `z`. -/
#check fun x y z : ℝ ↦ ‖toLp 2 (x - y, x - z)‖

-- Proof sketch: apply `WithLp.prod_norm_eq_of_L2` to the difference pair and simplify the real
-- norms to absolute values, then square the absolutes back to plain squares.
/-- Expanding the canonical `L²` norm of the difference pair gives the formula
`√((x - y)^2 + (x - z)^2)`. -/
@[simp] theorem centered_pairwise_difference_norm_eq (x y z : ℝ) :
    ‖toLp 2 (x - y, x - z)‖ =
      Real.sqrt ((x - y) ^ (2 : ℕ) + (x - z) ^ (2 : ℕ)) := by
  simpa [Real.norm_eq_abs, sq_abs] using
    (prod_norm_eq_of_L2 (toLp 2 (x - y, x - z)))
