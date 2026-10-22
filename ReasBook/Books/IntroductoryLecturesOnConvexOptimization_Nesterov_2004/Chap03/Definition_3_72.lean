/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_21
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_42

-- Declarations for this item will be appended below by the statement pipeline.

namespace GeneralMinimizationProblem

variable {n m : ℕ}

/- Definition 3.72 lies in the constrained-optimization domain of source-facing data on
`GeneralMinimizationProblem n m`.

Primary mathematical domain:
* finitely constrained Lipschitz minimization and its single aggregate-constraint reformulation

Sampled owner-style declarations:
* `problem.HasLeConstraints` and `problem.mem_feasibleSet_iff` in
  `Chap01/Definition_1_1_1`
* `problem.IsFunctionalConstraintProblem` in
  `Chap01/Definition_1_10_21`
* `pointwiseSupremumOn` and
  `constraintInequalities_eq_aggregateConstraintSublevelSet` in
  `Chap03/Definition_3_42`

Best owner abstraction:
* `GeneralMinimizationProblem n m`, with the Chapter 1 bundled owner
  `problem.IsFunctionalConstraintProblem` used only as derived API and the aggregate constraint
  reused from the Chapter 3 owner `pointwiseSupremumOn`

Primitive data:
* the owner problem `problem`
* nonemptiness, boundedness, closedness, and convexity of `problem.basicFeasibleSet`
* the inequality-sense hypothesis `problem.HasLeConstraints`
* global Lipschitz bounds for `problem.objective` and each scalar constraint

Derived API:
* the Chapter 1 owner predicate `problem.IsFunctionalConstraintProblem`, recovered by deriving
  continuity from the primitive Lipschitz hypotheses
* the aggregate constraint `pointwiseSupremumOn (Set.univ : Set (Fin m))` applied to the coercion
  of `problem.constraints` into `WithTop ℝ`
* the feasible-set rewrite already owned upstream by
  `constraintInequalities_eq_aggregateConstraintSublevelSet`

Source/core/bridge triage:
* source-facing: Definition 3.72 as feasible-set geometry, inequality sense, and
  Lipschitz data on the owner problem, together with the aggregate constraint
  `f̄ = pointwiseSupremumOn (Set.univ : Set (Fin m))` applied to the coerced constraint family
* core/canonical: `GeneralMinimizationProblem n m` together with
  `problem.IsFunctionalConstraintProblem` and `pointwiseSupremumOn`
* bridge/view: `isFunctionalConstraintProblem_of_lipschitz`, which upgrades the source-facing
  hypothesis list to the canonical Chapter 1 owner predicate, and the rewrite of the finite
  constraint family as one aggregate inequality

Accordingly, this file keeps the main labeled entry at the source-facing primitive data,
derives the canonical functional-constraint package instead of introducing a parallel local
predicate, reuses the Chapter 3 owner for the aggregate constraint after the canonical
`ℝ → WithTop ℝ` coercion, and keeps only the owner-level bridge from `problem.feasibleSet` to
the aggregate-constraint sublevel set. -/

variable (problem : GeneralMinimizationProblem n m)

/-
Definition 3.72: a finitely constrained Lipschitz minimization problem on a nonempty bounded
closed convex set `Q ⊆ ℝⁿ` is exactly a general minimization problem whose basic feasible set `Q`
is nonempty bounded closed and convex, whose scalar constraints are all of the form `fⱼ(x) ≤ 0`,
and whose objective and constraint functions are globally Lipschitz on `Q`. The source spelling
uses `Fin m`; the aggregate-constraint reformulation below does not need any extra nonemptiness
hypothesis on that index type, because the owner theorem already handles the empty-index case. The
canonical Chapter 1 owner predicate is recovered separately by
`isFunctionalConstraintProblem_of_lipschitz`.
-/
#check (
  0 < m ∧
    problem.basicFeasibleSet.Nonempty ∧
    Bornology.IsBounded problem.basicFeasibleSet ∧
    IsClosed problem.basicFeasibleSet ∧
    Convex ℝ problem.basicFeasibleSet ∧
    problem.HasLeConstraints ∧
    (∃ L : NNReal, LipschitzWith L problem.objective) ∧
    ∀ j : Fin m, ∃ L : NNReal, LipschitzWith L (problem.constraints j)
)

/- Definition 3.42 supplies the aggregate constraint for the real-valued family after coercion to
`WithTop ℝ`:
`f̄ = pointwiseSupremumOn (Set.univ : Set (Fin m))
  (fun x j ↦ (problem.constraints j x : WithTop ℝ))`. -/
#check
  pointwiseSupremumOn (Set.univ : Set (Fin m))
    (fun x j ↦ (problem.constraints j x : WithTop ℝ))

/- The family of inequalities `fⱼ(x) ≤ 0` is exactly the single aggregate inequality
`pointwiseSupremumOn (Set.univ : Set (Fin m))
  (fun x j ↦ (problem.constraints j x : WithTop ℝ)) x ≤ 0`, with no extra nonemptiness
hypothesis on `Fin m`. -/
#check
  constraintInequalities_eq_aggregateConstraintSublevelSet
    (fun j x ↦ (problem.constraints j x : WithTop ℝ))

section

variable {problem : GeneralMinimizationProblem n m}

/-- The explicit closedness, inequality-sense, and Lipschitz hypotheses from the textbook
spelling of Definition 3.72 imply the canonical Chapter 1 owner predicate. -/
theorem isFunctionalConstraintProblem_of_lipschitz
    (hQ_closed : IsClosed problem.basicFeasibleSet)
    (hle : problem.HasLeConstraints)
    (hobjective : ∃ L : NNReal, LipschitzWith L problem.objective)
    (hconstraints : ∀ j : Fin m, ∃ L : NNReal, LipschitzWith L (problem.constraints j)) :
    problem.IsFunctionalConstraintProblem := by
  refine
    { basicFeasibleSet_isClosed := hQ_closed
      objective_continuous := ?_
      constraint_continuous := ?_
      hasLeConstraints := hle }
  · rcases hobjective with ⟨L, hL⟩
    exact hL.continuous
  · intro j
    rcases hconstraints j with ⟨L, hL⟩
    exact hL.continuous

/-- Under the primitive Chapter 1 inequality-sense assumption `problem.HasLeConstraints`, the
owner feasible set is exactly the sublevel set of the aggregate constraint from Definition 3.42
obtained by coercing the real-valued constraint family into `WithTop ℝ`. -/
theorem feasibleSet_eq_aggregateConstraintSublevelSet
    (hle : problem.HasLeConstraints) :
    problem.feasibleSet =
      {x : problem.basicFeasibleSet |
        pointwiseSupremumOn (Set.univ : Set (Fin m))
          (fun y j ↦ (problem.constraints j y : WithTop ℝ)) x ≤ (0 : WithTop ℝ)} := by
  ext x
  rw [problem.mem_feasibleSet_iff hle]
  simpa using
    (Set.ext_iff.mp <|
      constraintInequalities_eq_aggregateConstraintSublevelSet
        (fun j y ↦ (problem.constraints j y : WithTop ℝ))) x

end

end GeneralMinimizationProblem
