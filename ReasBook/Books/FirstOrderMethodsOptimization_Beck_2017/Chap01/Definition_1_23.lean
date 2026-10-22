/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

section

variable (n : ℕ)

/- Definition 1.23: The unit simplex `Δ_n` in `ℝ^n`, modeled as `Fin n → ℝ`, is the standard
simplex `stdSimplex ℝ (Fin n)` consisting of the nonnegative vectors whose coordinates sum to
`1`. -/
#check (stdSimplex ℝ (Fin n) : Set (Fin n → ℝ))

-- Proof sketch: unfold `stdSimplex`; its defining predicate is exactly the conjunction of
-- coordinatewise nonnegativity and the condition that the finite sum of the coordinates is `1`.
/-- Membership in the unit simplex means coordinatewise nonnegativity and coordinate sum `1`. -/
theorem mem_unitSimplex_iff {x : Fin n → ℝ} :
    x ∈ stdSimplex ℝ (Fin n) ↔ (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1 := by
  rfl

end
