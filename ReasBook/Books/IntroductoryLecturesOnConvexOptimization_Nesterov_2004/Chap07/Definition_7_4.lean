/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped WithTopConvexAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Definition 7.4: a conic unconstrained minimization problem on a real inner product space
consists of a nonempty closed convex feasible set `Q₁` avoiding the origin together with a convex
positively `1`-homogeneous real-valued objective `f`, under the standing nondegeneracy condition
`0 ∈ interior (∂f(0))`. Since the objective is `E → ℝ`, the textbook assumption `dom f = E` is
built into the type, while the ambient constrained-problem data are owned canonically by
`SetConstrainedMinimizationProblem`. -/
structure ConicUnconstrainedMinimizationProblem (E : Type u)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    extends SetConstrainedMinimizationProblem E where
  /-- The feasible set `Q₁` is nonempty. -/
  feasibleSet_nonempty : feasibleSet.Nonempty
  /-- The feasible set `Q₁` is closed. -/
  feasibleSet_isClosed : IsClosed feasibleSet
  /-- The feasible set `Q₁` is convex. -/
  feasibleSet_convex : Convex ℝ feasibleSet
  /-- The origin does not belong to `Q₁`. -/
  zero_not_mem_feasibleSet : (0 : E) ∉ feasibleSet
  /-- The objective `f : E → ℝ` is convex on the whole space. -/
  objective_convex : ConvexOn ℝ Set.univ objective
  /-- The objective `f` is positively homogeneous of degree `1`. -/
  objective_posHomogeneous : IsPositivelyHomogeneousOn 1 Set.univ objective
  /-- The origin lies in the interior of the subdifferential `∂f(0)`. -/
  zero_mem_interior_subdifferential :
    (0 : E) ∈ interior (∂ (fun y ↦ (objective y : WithTop ℝ))(0))

namespace ConicUnconstrainedMinimizationProblem

/-- A conic unconstrained minimization problem can be used as its underlying objective function.
-/
instance : CoeFun (ConicUnconstrainedMinimizationProblem E) (fun _ ↦ E → ℝ) where
  coe problem := problem.toSetConstrainedMinimizationProblem

/-- Evaluating a conic unconstrained minimization problem returns its objective value. -/
@[simp] theorem coe_apply (problem : ConicUnconstrainedMinimizationProblem E) (x : E) :
    problem x = problem.objective x :=
  rfl

/-- The positive-homogeneity field recovers the textbook nonnegative scaling law. -/
theorem map_nonneg_smul
    (problem : ConicUnconstrainedMinimizationProblem E) (x : E) {t : ℝ} (ht : 0 ≤ t) :
    problem (t • x) = t * problem x := by
  simpa [NNReal.smul_def, Real.rpow_one, smul_eq_mul] using
    problem.objective_posHomogeneous.map_smul (by simp) (⟨t, ht⟩ : NNReal)

end ConicUnconstrainedMinimizationProblem
