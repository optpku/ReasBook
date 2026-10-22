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

/- Definition 8.2 is `source-facing`: it introduces the unconstrained minimization problem for an
objective `f` on the whole ambient space. The canonical mathlib owner for a global minimizer is
`IsMinOn f Set.univ x`, so this file exposes the corresponding solution-set view instead of adding
a bundled optimization-problem structure or a redundant alias for `f` itself. The Euclidean-space
setup from Definition 8.1 is not semantically active for this owner and is therefore omitted. -/

/-- Definition 8.2: the unconstrained problem `(P)` for an objective `f` is represented by the set
of points that globally minimize `f` on the whole ambient space. -/
def unconstrained_problem_solutions (f : E → α) : Set E :=
  {x | IsMinOn f Set.univ x}

-- Proof sketch: unfold `unconstrained_problem_solutions`; membership in the set is definitionally
-- the statement that the point is a global minimizer of `f`.
/-- A point belongs to the solution set of the unconstrained problem exactly when it globally
minimizes `f`. -/
theorem mem_unconstrained_problem_solutions_iff {f : E → α} {x : E} :
    x ∈ unconstrained_problem_solutions f ↔ IsMinOn f Set.univ x := by
  -- Unfold the source-facing owner so membership becomes the canonical mathlib minimizer predicate.
  rfl

-- Proof sketch: combine `mem_unconstrained_problem_solutions_iff` with mathlib's
-- `isMinOn_univ_iff` to rewrite global minimality as pointwise comparison with every objective
-- value.
/-- A point solves the unconstrained problem exactly when its objective value is less than or equal
to the value at every other point. -/
theorem mem_unconstrained_problem_solutions_iff_forall_le {f : E → α} {x : E} :
    x ∈ unconstrained_problem_solutions f ↔ ∀ y, f x ≤ f y := by
  -- First pass from the solution-set view to the global minimizer predicate on `Set.univ`.
  rw [mem_unconstrained_problem_solutions_iff]
  -- Then use mathlib's characterization of `IsMinOn` over the whole ambient space.
  simpa using (isMinOn_univ_iff (f := f) (a := x))

end
