/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open scoped ConstrainedArgmin

universe u

noncomputable section

variable {m : ℕ}
variable {E₁ : Type u} [AddCommGroup E₁] [Module ℝ E₁]

/-
Definition 6.23 lies in the constrained finite-residual `ℓ₁`-minimization domain.

Sampled owner-style declarations:
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for a
  feasible set together with a real-valued objective;
- `LagrangianProblem.constraintVector` in `Chap01/Definition_1_10_2`, the project owner for
  packaging a finite scalar family as an `ℝ^m`-valued map;
- `fenchelConjugate` in `Chap06/Definition_6_1`, the chapter owner for source-facing dual data on
  `Module.Dual ℝ E₁`;
- `maxAbsoluteValueOptimizationObjective` in `Chap06/Definition_6_21`, the nearby Chapter 6
  finite-family objective already stated with rows in `Module.Dual ℝ E₁`;
- `EuclideanSpace.l1Seminorm` and `EuclideanSpace.lpSeminorm_one_eq_l1Seminorm` in
  `Chap03/Definition_3_7`, the chapter owner for the finite `ℓ₁` norm and its source-facing
  coordinate formula;
- `equationSystemOptimizationProblem` in `Chap01/Example_1_1_6`, the earlier project pattern of
  defining a source-facing optimization problem directly as a `SetConstrainedMinimizationProblem`
  instead of rebuilding a parallel wrapper.

Best owner abstraction:
- source-facing: `sumAbsoluteValuesObjective` and `sumAbsoluteValuesOptimizationProblem`;
- core/canonical: `SetConstrainedMinimizationProblem`,
  `LagrangianProblem.constraintVector`, and
  `EuclideanSpace.l1Seminorm`;
- bridge/view: the coordinate expansion `∑ j, |a j x - b j|`.

Primitive data:
- the feasible set `Q₁`;
- a finite row family `a : Fin m → Module.Dual ℝ E₁`;
- a finite offset family `b : Fin m → ℝ`.

Derived API:
- the affine residual family `x ↦ a j x - b j`;
- the residual vector
  `(LagrangianProblem.mk (fun _ ↦ 0) (fun j x ↦ a j x - b j)).constraintVector x`;
- the `ℓ₁`-objective value `EuclideanSpace.l1Seminorm m ...`;
- the packaged constrained problem in the Chapter 1 owner.
-/

/-- The objective `x ↦ ∑ⱼ |aⱼ x - b⁽ʲ⁾|` for the sum-of-absolute-values problem. -/
def sumAbsoluteValuesObjective
    (a : Fin m → Module.Dual ℝ E₁) (b : Fin m → ℝ) : E₁ → ℝ :=
  EuclideanSpace.l1Seminorm m ∘
    (LagrangianProblem.mk (fun _ ↦ 0) (fun j x ↦ a j x - b j)).constraintVector

/-- Evaluating the sum-of-absolute-values objective expands to the finite sum of absolute
residuals. -/
@[simp] theorem sumAbsoluteValuesObjective_apply
    (a : Fin m → Module.Dual ℝ E₁) (b : Fin m → ℝ) (x : E₁) :
    sumAbsoluteValuesObjective a b x = ∑ j : Fin m, |a j x - b j| := by
  rw [sumAbsoluteValuesObjective, Function.comp_apply, EuclideanSpace.l1Seminorm_apply]
  simp [LagrangianProblem.constraintVector_apply]

/-- Definition 6.23: the sum-of-absolute-values optimization problem on a feasible set `Q₁`
minimizes `x ↦ ∑ⱼ |aⱼ x - b⁽ʲ⁾|` over `Q₁`. -/
def sumAbsoluteValuesOptimizationProblem
    (Q₁ : Set E₁) (a : Fin m → Module.Dual ℝ E₁) (b : Fin m → ℝ) :
    SetConstrainedMinimizationProblem E₁ where
  feasibleSet := Q₁
  objective := sumAbsoluteValuesObjective a b

/-- The feasible set of the sum-of-absolute-values optimization problem is exactly `Q₁`. -/
@[simp] theorem sumAbsoluteValuesOptimizationProblem_feasibleSet_eq
    (Q₁ : Set E₁) (a : Fin m → Module.Dual ℝ E₁) (b : Fin m → ℝ) :
    (sumAbsoluteValuesOptimizationProblem Q₁ a b).feasibleSet = Q₁ :=
  rfl

/-- Unfolding the sum-of-absolute-values optimization problem recovers the constrained problem with
feasible set `Q₁` and objective `sumAbsoluteValuesObjective a b`. -/
@[simp] theorem sumAbsoluteValuesOptimizationProblem_def
    (Q₁ : Set E₁) (a : Fin m → Module.Dual ℝ E₁) (b : Fin m → ℝ) :
    sumAbsoluteValuesOptimizationProblem Q₁ a b =
      { feasibleSet := Q₁
        objective := sumAbsoluteValuesObjective a b } :=
  rfl

-- Proof sketch: unfold `sumAbsoluteValuesOptimizationProblem`, then rewrite the objective by
-- `sumAbsoluteValuesObjective_apply`.
/-- Evaluating the objective of the sum-of-absolute-values optimization problem yields the finite
sum of absolute residuals `∑ⱼ |aⱼ x - b⁽ʲ⁾|`. -/
@[simp] theorem sumAbsoluteValuesOptimizationProblem_apply
    (Q₁ : Set E₁) (a : Fin m → Module.Dual ℝ E₁) (b : Fin m → ℝ) (x : E₁) :
    sumAbsoluteValuesOptimizationProblem Q₁ a b x = ∑ j : Fin m, |a j x - b j| := by
  -- Unfold the packaged problem to expose its source-facing objective.
  rw [sumAbsoluteValuesOptimizationProblem, SetConstrainedMinimizationProblem.coe_apply]
  -- Then expand the source-facing objective into the finite sum of absolute residuals.
  simp [sumAbsoluteValuesObjective_apply]

/-- The feasible set of the sum-of-absolute-values optimization problem is exactly `Q₁`. -/
@[simp] theorem sumAbsoluteValuesOptimizationProblem_feasibleSet
    (Q₁ : Set E₁) (a : Fin m → Module.Dual ℝ E₁) (b : Fin m → ℝ) :
    (sumAbsoluteValuesOptimizationProblem Q₁ a b).feasibleSet = Q₁ :=
  sumAbsoluteValuesOptimizationProblem_feasibleSet_eq Q₁ a b

/-- A point is feasible for the sum-of-absolute-values optimization problem exactly when it belongs
to `Q₁`. -/
-- Proof sketch: rewrite the feasible-set field of the packaged problem by
-- `sumAbsoluteValuesOptimizationProblem_feasibleSet`.
@[simp] theorem mem_sumAbsoluteValuesOptimizationProblem_feasibleSet_iff
    (Q₁ : Set E₁) (a : Fin m → Module.Dual ℝ E₁) (b : Fin m → ℝ) {x : E₁} :
    x ∈ (sumAbsoluteValuesOptimizationProblem Q₁ a b).feasibleSet ↔ x ∈ Q₁ := by
  -- The wrapper does not alter feasibility; it only packages `Q₁` as the feasible set field.
  simp

/-- Evaluating the packaged sum-of-absolute-values problem recovers its source-facing objective. -/
@[simp] theorem sumAbsoluteValuesOptimizationProblem_spec
    (Q₁ : Set E₁) (a : Fin m → Module.Dual ℝ E₁) (b : Fin m → ℝ) (x : E₁) :
    sumAbsoluteValuesOptimizationProblem Q₁ a b x = sumAbsoluteValuesObjective a b x :=
  rfl

/-- The objective field of the sum-of-absolute-values optimization problem is the sum-of-absolute-
values objective `x ↦ ∑ⱼ |aⱼ x - b⁽ʲ⁾|`. -/
@[simp] theorem sumAbsoluteValuesOptimizationProblem_objective
    (Q₁ : Set E₁) (a : Fin m → Module.Dual ℝ E₁) (b : Fin m → ℝ) :
    (sumAbsoluteValuesOptimizationProblem Q₁ a b).objective =
      sumAbsoluteValuesObjective a b :=
  rfl

/-- Coercing the sum-of-absolute-values optimization problem to a function recovers its
source-facing objective. -/
@[simp] theorem sumAbsoluteValuesOptimizationProblem_coe
    (Q₁ : Set E₁) (a : Fin m → Module.Dual ℝ E₁) (b : Fin m → ℝ) :
    ⇑(sumAbsoluteValuesOptimizationProblem Q₁ a b) = sumAbsoluteValuesObjective a b :=
  rfl

/-- The minimizer set of the packaged optimization problem is exactly the constrained argmin of
the sum-of-absolute-values objective on the feasible set `Q₁`. -/
-- Proof sketch: extensionality on points, then unfold membership in `argmin`, rewrite the
-- feasible set and objective with the preceding simp lemmas, and simplify.
@[simp] theorem sumAbsoluteValuesOptimizationProblem_argmin
    (Q₁ : Set E₁) (a : Fin m → Module.Dual ℝ E₁) (b : Fin m → ℝ) :
    argmin[(sumAbsoluteValuesOptimizationProblem Q₁ a b).feasibleSet]
        (sumAbsoluteValuesOptimizationProblem Q₁ a b) =
      argmin[Q₁] (sumAbsoluteValuesObjective a b) := by
  -- Compare the two argmin sets pointwise and simplify both memberships definitionally.
  ext x
  simp

/-- Minimizing the packaged sum-of-absolute-values problem on its feasible set is exactly
minimizing `sumAbsoluteValuesObjective a b` on `Q₁`. -/
-- Proof sketch: unfold the feasible set and objective of
-- `sumAbsoluteValuesOptimizationProblem`, then simplify with the preceding companion lemmas.
@[simp] theorem sumAbsoluteValuesOptimizationProblem_isMinOn_iff
    (Q₁ : Set E₁) (a : Fin m → Module.Dual ℝ E₁) (b : Fin m → ℝ) {x : E₁} :
    IsMinOn (sumAbsoluteValuesOptimizationProblem Q₁ a b)
        (sumAbsoluteValuesOptimizationProblem Q₁ a b).feasibleSet x ↔
      IsMinOn (sumAbsoluteValuesObjective a b) Q₁ x := by
  -- Unfolding the wrapper changes neither the feasible set nor the objective.
  rfl

/-- Membership in the canonical argmin set of the packaged sum-of-absolute-values problem means
belonging to `Q₁` and minimizing `sumAbsoluteValuesObjective a b` there. -/
-- Proof sketch: rewrite membership with `mem_constrainedArgmin_iff`, then use
-- `sumAbsoluteValuesOptimizationProblem_feasibleSet` and
-- `sumAbsoluteValuesOptimizationProblem_isMinOn_iff`.
@[simp] theorem mem_sumAbsoluteValuesOptimizationProblem_argmin_iff
    (Q₁ : Set E₁) (a : Fin m → Module.Dual ℝ E₁) (b : Fin m → ℝ) {x : E₁} :
    x ∈ argmin[(sumAbsoluteValuesOptimizationProblem Q₁ a b).feasibleSet]
        (sumAbsoluteValuesOptimizationProblem Q₁ a b) ↔
      x ∈ Q₁ ∧ IsMinOn (sumAbsoluteValuesObjective a b) Q₁ x := by
  -- Expand argmin membership and rewrite the wrapper data to the source-facing problem.
  simp

end
