/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

section

variable (n : ℕ)

/-- Definition 1.22: The positive orthant `ℝ^n_{++}` is the subset of `ℝ^n` consisting of the
vectors whose coordinates are all strictly positive. -/
def positiveOrthant : Set (Fin n → ℝ) :=
  Set.pi Set.univ (fun _ : Fin n ↦ Set.Ioi (0 : ℝ))

-- Proof sketch: unfold `positiveOrthant` and simplify membership in the product set.
/-- A vector belongs to the positive orthant exactly when each of its coordinates is positive. -/
theorem mem_positiveOrthant_iff {x : Fin n → ℝ} :
    x ∈ positiveOrthant n ↔ ∀ i, 0 < x i := by
  simp [positiveOrthant]

end
