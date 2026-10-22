/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_13

-- Declarations for this item will be appended below by the statement pipeline.

open Set

universe u v

variable {ι : Type u} {X : Type v}

/-
Definition 3.42 lies in the finite-family pointwise-supremum / constraint-aggregation domain.

Sampled owner-style declarations:
- `pointwiseSupremumOn` in `Chap03/PointwiseSupremumOn`, the chapter owner for subset-indexed
  pointwise suprema;
- `pointwiseSupremumOn_univ_le_zero_iff` in `Chap03/Lemma_3_13`, the finite-specialization bridge
  from one aggregate inequality to coordinatewise inequalities;
- `LagrangianProblem.feasibleSet` and `LagrangianProblem.mem_feasibleSet_iff` in
  `Chap01/Definition_1_10_2`, the project owner for finite `≤ 0` feasibility once constraints
  are packaged in an optimization problem;
- `GeneralMinimizationProblem.mem_feasibleSet_iff` in `Chap01/Definition_1_1_1`, the matching
  owner bridge for problem objects with explicit comparison senses.

Best owner abstraction:
- `pointwiseSupremumOn`.

Primitive data:
- the finite family of constraint functions.

Derived API:
- the coordinatewise-to-aggregate inequality equivalence;
- the induced equality between the original feasible family and the single aggregate sublevel set.

Source/core/bridge triage:
- source-facing: the textbook aggregate constraint function `\bar f`;
- core/canonical: `pointwiseSupremumOn`;
- bridge/view: the set equality comparing the family of inequalities with the single aggregate
  sublevel condition.

The source-facing aggregate map is exactly the `Set.univ` finite specialization of the chapter
owner `pointwiseSupremumOn`. Since the owner bridge itself does not use the finiteness witnesses,
this file keeps the public surface on an arbitrary index type and carrier, and it retains only the
set-level bridge needed to rewrite the feasible family of inequalities as one aggregate sublevel
condition.
-/

/- Definition 3.42: the textbook aggregate constraint function `\bar f` is exactly the `univ`
finite specialization of the chapter owner `pointwiseSupremumOn` for a `WithTop ℝ`-valued
constraint family. -/
#check (fun constraints : ι → X → WithTop ℝ ↦
  pointwiseSupremumOn (univ : Set ι) (fun x i ↦ constraints i x) :
    (ι → X → WithTop ℝ) → X → WithTop ℝ)

/-- The feasible points of the finitely constrained problem on a carrier `X` are exactly the
points satisfying the single aggregate inequality
`pointwiseSupremumOn (univ : Set ι) (fun x i ↦ constraints i x) x ≤ 0`, where the textbook
aggregate function `\bar f` is exactly this owner construction. This equality is the set-theoretic
content behind rewriting `min {f(x) : x ∈ Q, fⱼ(x) ≤ 0}` as
`min {f(x) : x ∈ Q, pointwiseSupremumOn (univ : Set ι) (fun x i ↦ constraints i x) x ≤ 0}`. -/
-- Proof sketch: extensionality reduces set equality to pointwise membership, and the pointwise
-- comparison is exactly `pointwiseSupremumOn_univ_le_zero_iff`.
theorem constraintInequalities_eq_aggregateConstraintSublevelSet
    (constraints : ι → X → WithTop ℝ) :
    {x | ∀ j : ι, constraints j x ≤ 0} =
      {x | pointwiseSupremumOn (univ : Set ι) (fun x i ↦ constraints i x) x ≤ 0} := by
  ext x
  change (∀ j : ι, constraints j x ≤ 0) ↔
    pointwiseSupremumOn (univ : Set ι) (fun y i ↦ constraints i y) x ≤ 0
  rw [pointwiseSupremumOn_univ_le_zero_iff]
