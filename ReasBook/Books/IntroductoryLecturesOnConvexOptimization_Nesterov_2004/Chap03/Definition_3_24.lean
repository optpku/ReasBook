/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConstrainedArgmin

universe u v

section

variable {X : Type u} (Q : Set X) (f : X → ℝ) (x : X)

/-- Definition 3.24: the set of minimizers `X^*` of `f` on the feasible set `Q` is the canonical
constrained argmin set `argmin[Q] f`. -/
abbrev minimizerSet : Set X :=
  argmin[Q] f

/-- The Chapter 1 owner for the Definition 3.24 minimizer set. -/
recall constrainedArgmin {X : Type u} {Y : Type v} [Preorder Y] (Q : Set X) (f : X → Y) : Set X

/-- Helper for Definition 3.24: the canonical constrained argmin owner is exactly the feasible
minimizer set written as a set-builder. -/
theorem constrainedArgmin_eq_setOf_isMinOn :
    argmin[Q] f = {x | x ∈ Q ∧ IsMinOn f Q x} := by
  -- Unfold the Chapter 1 owner of the minimizer set.
  rfl

/-- Helper for Definition 3.24: membership in the textbook minimizer set means feasibility
together with minimizing `f` on `Q`. -/
-- The downstream bridge is the existing Chapter 1 membership expansion.
recall mem_constrainedArgmin_iff {X : Type u} {Y : Type v} [Preorder Y] {Q : Set X} {f : X → Y}
    {x : X} : x ∈ argmin[Q] f ↔ x ∈ Q ∧ IsMinOn f Q x

end
