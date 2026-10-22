/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section

variable (n : ℕ)

/- Definition 1.25: for a vector `x` in `ℝ^n`, modeled as `Fin n → ℝ`, the nonnegative part
`[x]_+` is the canonical positive-part operation `x⁺`. -/
#check ((·⁺) : (Fin n → ℝ) → Fin n → ℝ)

variable {n : ℕ}

-- Proof sketch: unfold the canonical positive part `x⁺ = x ⊔ 0`; on the pointwise lattice
-- `Fin n → ℝ`, evaluation at a coordinate turns this into the scalar supremum `max (x i) 0`.
/-- The coordinates of the positive part of `x` are the maxima of the coordinates of `x` with `0`.
-/
theorem posPart_apply (x : Fin n → ℝ) (i : Fin n) :
    x⁺ i = max (x i) 0 := by
  rfl

end
