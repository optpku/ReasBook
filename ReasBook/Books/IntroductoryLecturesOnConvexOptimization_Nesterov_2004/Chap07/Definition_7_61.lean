/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_56

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]

/- Definition 7.61 lies in Chapter 7's constrained concave-maximization domain.

Sampled owner-style declarations:
- `maximalValueOn` in `Chap07/Definition_7_56`, the chapter owner for faithful maximal values of
  real objectives on feasible sets;
- `maximalValueOn_eq_sSup_image` in `Chap07/Definition_7_56`, the canonical expansion theorem for
  that owner;
- `LinearPackingProblem.optimalValue` in `Chap07/Definition_7_41`, the chapter pattern for
  source-facing maximization problems whose value is derived from the same owner;
- the direct specialization of `maximalValueOn` in `Chap07/Definition_7_55` to a
  barrier-regularized affine payoff.

Best owner abstraction:
- source-facing: `ConcaveMaximizationOverIntersectionDomain`, carrying the textbook data
  `(hatP, Q, ψ)`;
- core/canonical: the feasible-set expressions `hatP ∩ Q` and `hatP ∩ interior Q`, together with
  the Chapter 7 value owner `maximalValueOn`;
- bridge/view: the membership lemmas for `problem.feasibleSet` / `problem.strictFeasibleSet` and
  the `sSup` expansion of `problem.optimalValue`.

Primitive data:
- the sets `hatP` and `Q`;
- the objective `ψ`;
- concavity of `ψ` on `hatP ∩ Q`;
- positivity of `ψ` on `hatP ∩ interior Q`.

Derived API:
- the feasible set `problem.feasibleSet = hatP ∩ Q`;
- the strict feasible set `problem.strictFeasibleSet = hatP ∩ interior Q`;
- the coercion to the objective function;
- the canonical maximal-value owner `problem.optimalValue`.

The previous version introduced standalone top-level wrappers for `hatP ∩ Q`,
`hatP ∩ interior Q`, and a raw real-valued `sSup` optimal value. Those are duplicate wheels:
the intersection sets are better exposed as the source-facing problem's own derived feasible-set
surface, and the value should reuse the chapter owner `maximalValueOn` so empty or unbounded
feasible-value sets are represented faithfully.
-/

/-- Definition 7.61: a concave maximization problem over an intersection domain consists of sets
`hatP, Q ⊆ E` and an objective `ψ : E → ℝ` that is concave on the feasible region
`hatP ∩ Q` and strictly positive on the strict feasible region `hatP ∩ interior Q`. -/
structure ConcaveMaximizationOverIntersectionDomain (E : Type u)
    [TopologicalSpace E] [AddCommGroup E] [Module ℝ E] where
  /-- The outer set `hatP` appearing in the decomposition `P = hatP ∩ Q`. -/
  hatP : Set E
  /-- The second constraint set `Q` in the decomposition `P = hatP ∩ Q`. -/
  Q : Set E
  /-- The objective `ψ : E → ℝ`. -/
  objective : E → ℝ
  /-- The objective is concave on the feasible region `hatP ∩ Q`. -/
  objective_concaveOn : ConcaveOn ℝ (hatP ∩ Q) objective
  /-- The objective is strictly positive on the strict feasible region `hatP ∩ interior Q`. -/
  objective_pos :
    ∀ ⦃x : E⦄, x ∈ hatP ∩ interior Q → 0 < objective x

namespace ConcaveMaximizationOverIntersectionDomain

/-- A concave maximization problem over an intersection domain can be used as its objective
function. -/
instance : CoeFun (ConcaveMaximizationOverIntersectionDomain E) (fun _ ↦ E → ℝ) where
  coe problem := problem.objective

/-- Evaluating a concave maximization problem as a function returns its objective value. -/
@[simp] theorem coe_apply
    (problem : ConcaveMaximizationOverIntersectionDomain E) (x : E) :
    problem x = problem.objective x :=
  rfl

/-- The feasible set `P = hatP ∩ Q` attached to an intersection-domain concave maximization
problem. -/
abbrev feasibleSet (problem : ConcaveMaximizationOverIntersectionDomain E) : Set E :=
  problem.hatP ∩ problem.Q

/-- Membership in `problem.feasibleSet` means belonging to both `hatP` and `Q`. -/
@[simp] theorem mem_feasibleSet_iff
    (problem : ConcaveMaximizationOverIntersectionDomain E) {x : E} :
    x ∈ problem.feasibleSet ↔ x ∈ problem.hatP ∧ x ∈ problem.Q :=
  Iff.rfl

/-- The strict feasible set `hatP ∩ interior Q` attached to an intersection-domain concave
maximization problem. -/
abbrev strictFeasibleSet (problem : ConcaveMaximizationOverIntersectionDomain E) : Set E :=
  problem.hatP ∩ interior problem.Q

/-- Membership in `problem.strictFeasibleSet` means belonging to `hatP` and to the interior of
`Q`. -/
@[simp] theorem mem_strictFeasibleSet_iff
    (problem : ConcaveMaximizationOverIntersectionDomain E) {x : E} :
    x ∈ problem.strictFeasibleSet ↔ x ∈ problem.hatP ∧ x ∈ interior problem.Q :=
  Iff.rfl

/-- The objective is strictly positive at every strict feasible point. -/
theorem objective_pos_of_mem_strictFeasibleSet
    (problem : ConcaveMaximizationOverIntersectionDomain E) {x : E}
    (hx : x ∈ problem.strictFeasibleSet) :
    0 < problem x :=
  problem.objective_pos hx

/-- The optimal value `ψ⋆` of the problem, formalized through the canonical Chapter 7 maximal
value owner on the feasible set `P = hatP ∩ Q`. -/
def optimalValue (problem : ConcaveMaximizationOverIntersectionDomain E) : EReal :=
  maximalValueOn problem.feasibleSet problem

/-- Expanding `problem.optimalValue` gives the supremum of the objective values on the feasible
set `P = hatP ∩ Q`, viewed in `EReal`. -/
theorem optimalValue_eq_sSup_image
    (problem : ConcaveMaximizationOverIntersectionDomain E) :
    problem.optimalValue = sSup ((fun x ↦ (problem x : EReal)) '' problem.feasibleSet) := by
  simpa using maximalValueOn_eq_sSup_image problem.feasibleSet problem

end ConcaveMaximizationOverIntersectionDomain

end
