/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section

variable (n : ℕ)

/- Definition 1.21 (core/canonical): the nonnegative orthant `ℝ^n_+` is the principal upper set
`Set.Ici 0` in the pointwise order on `Fin n → ℝ`. -/
#check (Set.Ici (0 : Fin n → ℝ))

/-- Membership in the nonnegative orthant means that every coordinate is nonnegative. -/
theorem mem_nonnegativeOrthant_iff {x : Fin n → ℝ} :
    x ∈ Set.Ici (0 : Fin n → ℝ) ↔ ∀ i, 0 ≤ x i := by
  simp [Pi.le_def]

end
