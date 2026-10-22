/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped SupportFunction

variable {m n : ℕ}

local notation "Eₘ" => EuclideanSpace ℝ (Fin m)
local notation "Eₙ" => EuclideanSpace ℝ (Fin n)

/-- Definition 7.10: a support-function minimization problem consists of a closed bounded convex
set `Q₂ ⊆ ℝᵐ` with `0 ∈ interior Q₂`, a matrix `A ∈ ℝ^(m × n)` with full column rank, and a
closed convex set `Q₁ ⊆ ℝⁿ`; its canonical support-function objective is `x ↦ ξ[Q₂] (A x)`, and
the associated real-valued minimization objective is obtained from that Chapter 3 owner by the
standard `toReal` bridge. -/
structure SupportFunctionOptimizationProblem (m n : ℕ) where
  /-- The closed bounded convex set `Q₂ ⊆ ℝᵐ` defining the support function. -/
  Q2 : Set (EuclideanSpace ℝ (Fin m))
  /-- The set `Q₂` is closed. -/
  Q2_closed : IsClosed Q2
  /-- The set `Q₂` is bounded. -/
  Q2_bounded : Bornology.IsBounded Q2
  /-- The set `Q₂` is convex. -/
  Q2_convex : Convex ℝ Q2
  /-- The origin belongs to the interior of `Q₂`. -/
  zero_mem_interior_Q2 : (0 : EuclideanSpace ℝ (Fin m)) ∈ interior Q2
  /-- The matrix `A ∈ ℝ^(m × n)` defining the linear map `x ↦ A x`. -/
  A : Matrix (Fin m) (Fin n) ℝ
  /-- The matrix `A` has full column rank, encoded as injectivity of its Euclidean linear map. -/
  A_full_column_rank : Function.Injective (Matrix.toEuclideanLin A)
  /-- The closed convex feasible set `Q₁ ⊆ ℝⁿ`. -/
  Q1 : Set (EuclideanSpace ℝ (Fin n))
  /-- The feasible set `Q₁` is closed. -/
  Q1_closed : IsClosed Q1
  /-- The feasible set `Q₁` is convex. -/
  Q1_convex : Convex ℝ Q1

namespace SupportFunctionOptimizationProblem

/-- The support set `Q₂`, viewed as the canonical convex-body owner used by the Chapter 7 support
radius API. -/
def supportBody (problem : SupportFunctionOptimizationProblem m n) : ConvexBody Eₘ where
  carrier := problem.Q2
  convex' := problem.Q2_convex
  isCompact' := by
    simpa using Metric.isCompact_of_isClosed_isBounded problem.Q2_closed problem.Q2_bounded
  nonempty' := ⟨0, interior_subset problem.zero_mem_interior_Q2⟩

@[simp] theorem coe_supportBody (problem : SupportFunctionOptimizationProblem m n) :
    (problem.supportBody : Set Eₘ) = problem.Q2 :=
  rfl

/-- The canonical Chapter 3 support-function objective `x ↦ ξ[Q₂] (A x)`. -/
def objectiveEReal (problem : SupportFunctionOptimizationProblem m n) : Eₙ → EReal :=
  ξ[problem.Q2] ∘ Matrix.toEuclideanLin problem.A

@[simp] theorem objectiveEReal_apply (problem : SupportFunctionOptimizationProblem m n) (x : Eₙ) :
    problem.objectiveEReal x = ξ[problem.Q2] (Matrix.toEuclideanLin problem.A x) :=
  rfl

/-- The real-valued objective used by the Chapter 1 constrained minimization owner. -/
def objective (problem : SupportFunctionOptimizationProblem m n) : Eₙ → ℝ :=
  fun x ↦ (problem.objectiveEReal x).toReal

@[simp] theorem objective_apply (problem : SupportFunctionOptimizationProblem m n) (x : Eₙ) :
    problem.objective x = (ξ[problem.Q2] (Matrix.toEuclideanLin problem.A x)).toReal :=
  rfl

/-- The canonical set-constrained minimization owner attached to the support-function problem. -/
def toSetConstrainedMinimizationProblem
    (problem : SupportFunctionOptimizationProblem m n) :
    SetConstrainedMinimizationProblem Eₙ where
  feasibleSet := problem.Q1
  objective := problem.objective

@[simp] theorem toSetConstrainedMinimizationProblem_feasibleSet
    (problem : SupportFunctionOptimizationProblem m n) :
    problem.toSetConstrainedMinimizationProblem.feasibleSet = problem.Q1 :=
  rfl

@[simp] theorem toSetConstrainedMinimizationProblem_objective
    (problem : SupportFunctionOptimizationProblem m n) :
    problem.toSetConstrainedMinimizationProblem.objective = problem.objective :=
  rfl

@[simp] theorem toSetConstrainedMinimizationProblem_apply
    (problem : SupportFunctionOptimizationProblem m n) (x : Eₙ) :
    problem.toSetConstrainedMinimizationProblem x = problem.objective x :=
  rfl

/-- A support-function optimization problem can be used as its objective function `x ↦ F(Ax)`. -/
instance : CoeFun (SupportFunctionOptimizationProblem m n) (fun _ ↦ Eₙ → ℝ) where
  coe problem := problem.toSetConstrainedMinimizationProblem

@[simp] theorem coe_apply (problem : SupportFunctionOptimizationProblem m n) (x : Eₙ) :
    problem x = problem.objective x :=
  rfl

/-- The Chapter 1 owner optimal value of the support-function minimization problem is the infimum
of the real-valued bridge objective on the feasible set `Q₁`, viewed in `EReal`. -/
theorem optimalValue_eq_sInf_image (problem : SupportFunctionOptimizationProblem m n) :
    problem.toSetConstrainedMinimizationProblem.optimalValue =
      sInf ((fun x ↦ (problem.objective x : EReal)) '' problem.Q1) := by
  simpa using problem.toSetConstrainedMinimizationProblem.optimalValue_eq_sInf_image

end SupportFunctionOptimizationProblem

end
