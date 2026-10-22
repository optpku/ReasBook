/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Filter.Extr

noncomputable section

-- Semantic recall: `lean_leansearch` surfaced only generic matrix positive-definiteness API.
-- For this one-constraint exercise, the clean source-faithful surface is the explicit scalar dual
-- problem `max -(1 / 2) * (λ - 1)^2` over `λ ≥ 0`.

section

/-- The explicit dual feasible set for Exercise 9.4 is the half-line `λ ≥ 0`. -/
def chapter09Exercise94DualFeasibleSet : Set ℝ :=
  Set.Ici 0

/-- Unfolding `chapter09Exercise94DualFeasibleSet` gives the half-line `λ ≥ 0`. -/
@[simp] theorem chapter09Exercise94DualFeasibleSet_eq :
    chapter09Exercise94DualFeasibleSet = Set.Ici 0 :=
  rfl

/-- Membership in `chapter09Exercise94DualFeasibleSet` is exactly the scalar inequality
`0 ≤ λ`. -/
@[simp] theorem mem_chapter09Exercise94DualFeasibleSet (l : ℝ) :
    l ∈ chapter09Exercise94DualFeasibleSet ↔ 0 ≤ l :=
  Iff.rfl

/-- The explicit dual objective for Exercise 9.4 is `φ(λ) = -(1 / 2) * (λ - 1)^2`. -/
def chapter09Exercise94DualObjective (l : ℝ) : ℝ :=
  -((1 / 2 : ℝ) * (l - 1) ^ (2 : ℕ))

/-- Unfolding `chapter09Exercise94DualObjective` gives the scalar quadratic formula
`φ(λ) = -(1 / 2) * (λ - 1)^2`. -/
@[simp] theorem chapter09Exercise94DualObjective_eq (l : ℝ) :
    chapter09Exercise94DualObjective l = -((1 / 2 : ℝ) * (l - 1) ^ (2 : ℕ)) :=
  rfl

/-- The scalar dual objective of Exercise 9.4 is always nonpositive. -/
theorem chapter09Exercise94DualObjective_nonpos (l : ℝ) :
    chapter09Exercise94DualObjective l ≤ 0 := by
  rw [chapter09Exercise94DualObjective_eq]
  exact neg_nonpos.mpr <| mul_nonneg (by norm_num) (sq_nonneg (l - 1))

/-- The optimal dual multiplier for Exercise 9.4 is `λ = 1`. -/
def chapter09Exercise94DualOptimizer : ℝ :=
  1

/-- Unfolding `chapter09Exercise94DualOptimizer` gives the source multiplier `λ = 1`. -/
@[simp] theorem chapter09Exercise94DualOptimizer_eq :
    chapter09Exercise94DualOptimizer = 1 :=
  rfl

/-- The optimal multiplier `chapter09Exercise94DualOptimizer` is feasible for the dual problem. -/
@[simp] theorem chapter09Exercise94DualOptimizer_mem_dualFeasibleSet :
    chapter09Exercise94DualOptimizer ∈ chapter09Exercise94DualFeasibleSet := by
  simp [chapter09Exercise94DualOptimizer]

/-- The dual objective vanishes at the optimizer `chapter09Exercise94DualOptimizer = 1`. -/
@[simp] theorem chapter09Exercise94DualObjective_optimizer :
    chapter09Exercise94DualObjective chapter09Exercise94DualOptimizer = 0 := by
  simp [chapter09Exercise94DualObjective, chapter09Exercise94DualOptimizer]

/-- Every multiplier has dual value at most the value at the optimizer
`chapter09Exercise94DualOptimizer`. -/
theorem chapter09Exercise94DualObjective_le_optimizer (l : ℝ) :
    chapter09Exercise94DualObjective l ≤
      chapter09Exercise94DualObjective chapter09Exercise94DualOptimizer := by
  simpa [chapter09Exercise94DualObjective_optimizer] using
    chapter09Exercise94DualObjective_nonpos l

/-- Chapter09 Exercise 9.4 (1): the explicit dual problem
`max chapter09Exercise94DualObjective λ` subject to `λ ∈ chapter09Exercise94DualFeasibleSet`
is solved by `chapter09Exercise94DualOptimizer = 1`. -/
theorem chapter09Exercise94DualIsMaxOn :
    IsMaxOn
      chapter09Exercise94DualObjective
      chapter09Exercise94DualFeasibleSet
      chapter09Exercise94DualOptimizer := by
  rw [isMaxOn_iff]
  intro l _
  exact chapter09Exercise94DualObjective_le_optimizer l

/-- Chapter09 Exercise 9.4 (2): the optimal value of the dual problem is `0`. -/
theorem chapter09Exercise94DualOptimalValue :
    chapter09Exercise94DualObjective chapter09Exercise94DualOptimizer = 0 :=
  chapter09Exercise94DualObjective_optimizer

end
