/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Theorem_6_11

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConstrainedArgmin

noncomputable section

universe u

variable {E₁ : Type u} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]

/- Definition 6.26 lies in the chapter's proximal-subproblem / constrained-minimization domain.

Sampled owner-style declarations:
- `linearOptimizationOracleObjective` in `Chap06/Theorem_6_11`, the earlier chapter owner for the
  affine-plus-regularizer objective on a feasible subtype;
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for a
  feasible set together with a real-valued objective;
- `constrainedArgmin` / `argmin[Q]` and `mem_constrainedArgmin_iff` in
  `Chap01/Definition_1_3_3`, the canonical owner of minimizer sets on a feasible set;
- `explicitModelSmoothedProblem` in `Chap06/Definition_6_9`, the chapter pattern of keeping the
  optimization problem itself as the source-facing owner and deriving its minimizers via the
  Chapter 1 argmin API.

Best owner abstraction:
- source-facing: `proximalMinimizationProblem`;
- core/canonical: `linearOptimizationOracleObjective`, `SetConstrainedMinimizationProblem Q₁`, and
  `argmin[Set.univ]`;
- bridge/view: the pointwise formula for the problem objective.

Primitive data:
- a feasible set `Q₁ : Set E₁`;
- a prox term `d₁ : Q₁ → ℝ`;
- a linear functional `s : StrongDual ℝ E₁`.

Derived API:
- the affine-plus-regularizer objective `linearOptimizationOracleObjective s d₁` on the feasible
  subtype `Q₁`;
- the associated problem owner on `Q₁` with feasible set `Set.univ`;
- the canonical minimizer set `argmin[Set.univ] (proximalMinimizationProblem Q₁ d₁ s)`.

Source/core/bridge triage:
- source-facing: the proximal minimization problem from the text;
- core/canonical: `linearOptimizationOracleObjective`, `SetConstrainedMinimizationProblem`, and
  `argmin[Q]`;
- bridge/view: the pointwise formula below.

The previous file introduced a second public objective owner with the same interface and
mathematical content as `linearOptimizationOracleObjective`. This refinement removes that duplicate
wheel and defines the proximal subproblem directly through the chapter's existing affine-plus-
regularizer owner.
-/

/-- Definition 6.26: the proximal minimization subproblem is the constrained problem on the
feasible subtype `Q₁` whose objective is the canonical affine-plus-regularizer owner
`linearOptimizationOracleObjective s d₁`. Its minimizer set is the canonical Chapter 1 owner
`argmin[Set.univ] (proximalMinimizationProblem Q₁ d₁ s)`. -/
def proximalMinimizationProblem
    (Q₁ : Set E₁) (d₁ : Q₁ → ℝ) (s : StrongDual ℝ E₁) :
    SetConstrainedMinimizationProblem Q₁ where
  feasibleSet := Set.univ
  objective := linearOptimizationOracleObjective s d₁

/-- Unfolding the proximal minimization problem recovers the constrained problem with feasible set
`Set.univ` on `Q₁` and objective `linearOptimizationOracleObjective s d₁`. -/
-- Proof sketch: unfold `proximalMinimizationProblem`.
@[simp] theorem proximalMinimizationProblem_def
    (Q₁ : Set E₁) (d₁ : Q₁ → ℝ) (s : StrongDual ℝ E₁) :
    proximalMinimizationProblem Q₁ d₁ s =
      { feasibleSet := Set.univ
        objective := linearOptimizationOracleObjective s d₁ } := by
  -- Unfold the owner to expose its record fields.
  rfl

/-- The feasible set of the proximal minimization problem is the whole feasible subtype `Q₁`. -/
-- Proof sketch: unfold `proximalMinimizationProblem`.
@[simp] theorem proximalMinimizationProblem_feasibleSet
    (Q₁ : Set E₁) (d₁ : Q₁ → ℝ) (s : StrongDual ℝ E₁) :
    (proximalMinimizationProblem Q₁ d₁ s).feasibleSet = Set.univ := by
  -- The feasible set is definitionally `Set.univ` on the feasible subtype.
  rfl

/-- The objective field of the proximal minimization problem is the canonical affine-plus-
regularizer objective `linearOptimizationOracleObjective s d₁`. -/
-- Proof sketch: unfold `proximalMinimizationProblem`.
@[simp] theorem proximalMinimizationProblem_objective
    (Q₁ : Set E₁) (d₁ : Q₁ → ℝ) (s : StrongDual ℝ E₁) :
    (proximalMinimizationProblem Q₁ d₁ s).objective =
      linearOptimizationOracleObjective s d₁ := by
  -- The objective field is exactly the chapter's affine-plus-regularizer owner.
  rfl

/-- Evaluating the proximal minimization problem at a feasible point gives the prox term plus the
linear pairing. -/
-- Proof sketch: use `proximalMinimizationProblem_objective` and
-- `linearOptimizationOracleObjective_apply`, then commute the summands.
theorem proximalMinimizationProblem_spec
    (Q₁ : Set E₁) (d₁ : Q₁ → ℝ) (s : StrongDual ℝ E₁) (x : Q₁) :
    proximalMinimizationProblem Q₁ d₁ s x =
      d₁ x + s x := by
  -- Rewrite the packaged problem through its objective field.
  rw [proximalMinimizationProblem_objective]
  -- Now evaluate the canonical affine-plus-regularizer objective and reorder the sum.
  simpa [add_comm] using linearOptimizationOracleObjective_apply s d₁ x

/-- Evaluating the proximal minimization problem gives the prox term plus the linear pairing. -/
-- Proof sketch: apply `proximalMinimizationProblem_spec`.
@[simp] theorem proximalMinimizationProblem_apply
    (Q₁ : Set E₁) (d₁ : Q₁ → ℝ) (s : StrongDual ℝ E₁) (x : Q₁) :
    proximalMinimizationProblem Q₁ d₁ s x =
      d₁ x + s x := by
  -- Reuse the textbook evaluation formula rather than reproving it.
  simpa using proximalMinimizationProblem_spec Q₁ d₁ s x

/-- The canonical minimizer set of the proximal minimization problem is exactly the argmin set of
`linearOptimizationOracleObjective s d₁` on the feasible subtype `Q₁`. -/
-- Proof sketch: unfold `proximalMinimizationProblem`; both sides reduce to the same argmin set on
-- `Set.univ`.
@[simp] theorem proximalMinimizationProblem_argmin
    (Q₁ : Set E₁) (d₁ : Q₁ → ℝ) (s : StrongDual ℝ E₁) :
    argmin[Set.univ] (proximalMinimizationProblem Q₁ d₁ s) =
      argmin[Set.univ] (linearOptimizationOracleObjective s d₁) := by
  -- Both argmin sets are definitionally the same once the objective is unfolded.
  ext x
  simp [proximalMinimizationProblem]

end
