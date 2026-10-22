/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {E : Type u} {α : Type v} [Preorder α]

/- This item is `source-facing`: the displayed model is a constrained minimization problem with
objective `f` and feasible set `C`. In this domain the canonical minimizer owner is mathlib's
`IsMinOn`, and Chapter 8 already represents optimization models by their solution sets rather than
by bundled problem structures. The public API below therefore exposes the set of feasible
minimizers of `f` on `C`. -/

/-- Definition 8.5: the constrained minimization model `min {f(x) : x ∈ C}` is represented by the
set of feasible points that minimize `f` over `C`. -/
def constrained_problem_solutions (f : E → α) (C : Set E) : Set E :=
  {x | x ∈ C ∧ IsMinOn f C x}

-- Proof sketch: unfold `constrained_problem_solutions`; membership is definitionally feasibility
-- together with the owner predicate `IsMinOn` on the same feasible set.
/-- A point belongs to `constrained_problem_solutions f C` exactly when it is feasible for `C` and
minimizes `f` on `C`. -/
@[simp] theorem mem_constrained_problem_solutions_iff {f : E → α} {C : Set E} {x : E} :
    x ∈ constrained_problem_solutions f C ↔ x ∈ C ∧ IsMinOn f C x := by
  -- Unfolding the solution-set definition exposes the feasibility and minimizer conditions.
  rfl

-- Proof sketch: combine `mem_constrained_problem_solutions_iff` with `isMinOn_iff` to rewrite the
-- minimizer condition as pointwise comparison against every feasible point.
/-- A point solves the constrained problem exactly when it lies in `C` and its objective value is
less than or equal to that of every feasible point. -/
theorem mem_constrained_problem_solutions_iff_mem_and_forall_le {f : E → α} {C : Set E} {x : E} :
    x ∈ constrained_problem_solutions f C ↔ x ∈ C ∧ ∀ y ∈ C, f x ≤ f y := by
  -- First rewrite solution-set membership, then expand `IsMinOn` to the pointwise order condition.
  rw [mem_constrained_problem_solutions_iff, isMinOn_iff]

end
