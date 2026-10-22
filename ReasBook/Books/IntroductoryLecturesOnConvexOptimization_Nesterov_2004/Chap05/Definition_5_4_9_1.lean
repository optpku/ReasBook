/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_8_20
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Theorem_5_4_8_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators RealInnerProductSpace

variable {n m : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-
Definition 5.4.9.1 lies in the Chapter 5 box-constrained `ℓ_p` approximation domain.

Sampled owner declarations:
- `lpApproximationObjective` in `Definition_5_4_8_20`, the chapter owner for the residual
  objective `x ↦ ∑ i, |⟪aᵢ, x⟫ - b⁽ⁱ⁾|^p`;
- `lpApproximationProblem` and `mem_lpApproximationProblem_feasibleSet_iff` in
  `Theorem_5_4_8_9`, the chapter owner for the same box-constrained problem and its box-membership
  expansion;
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner for a
  feasible set together with its ambient real-valued objective;
- `SemidefiniteOptimizationProblem.toSetConstrainedMinimizationProblem` in
  `Definition_5_4_4_4`, the local Chapter 5 pattern for keeping source-facing primitive data while
  routing the ambient optimization interface through the Chapter 1 owner.

Best owner abstraction:
- source-facing: `LpApproximationBoxProblem n m`, whose primitive data are exactly the textbook
  exponent, residual vectors/targets, and box bounds;
- core/canonical: `SetConstrainedMinimizationProblem E`, together with the existing chapter owners
  `lpApproximationObjective` and `lpApproximationProblem`;
- bridge/view: `toSetConstrainedMinimizationProblem`, plus the derived `feasibleSet` and the
  evaluation/membership lemmas exposing its objective through the canonical owner.

Primitive data:
- `p : Set.Ici (1 : ℝ)`, `a`, `b`;
- `α`, `β`.

Derived API:
- `toSetConstrainedMinimizationProblem := lpApproximationProblem problem.p problem.a problem.b
  problem.α problem.β`;
- `feasibleSet := problem.toSetConstrainedMinimizationProblem.feasibleSet`;
- `one_le_p : 1 ≤ (problem.p : ℝ)`;
- `objective_apply`, `mem_feasibleSet_iff`, and the induced coercion to the canonical objective.

This refinement therefore keeps the textbook source-facing data owner, but removes the duplicate
ambient optimization wrapper surface in favor of the canonical Chapter 1 owner
`lpApproximationProblem`, without introducing a second local name for the same objective.
-/

/-- Definition 5.4.9.1: an `ℓ_p` approximation problem with box constraints on `ℝⁿ` is given by
an exponent `p ≥ 1`, vectors `a₁, ..., aₘ ∈ ℝⁿ`, scalars `b⁽¹⁾, ..., b⁽ᵐ⁾ ∈ ℝ`, and box bounds
`α`, `β ∈ ℝⁿ`. The associated optimization problem minimizes
`∑ i, |⟪aᵢ, x⟫ - b⁽ⁱ⁾|^p` over the box `α ≤ x ≤ β`. -/
structure LpApproximationBoxProblem (n m : ℕ) where
  /-- The exponent `p` in the `ℓ_p` approximation objective, constrained by `p ≥ 1`. -/
  p : Set.Ici (1 : ℝ)
  /-- The vectors `a₁, ..., aₘ ∈ ℝⁿ`. -/
  a : Fin m → EuclideanSpace ℝ (Fin n)
  /-- The scalar targets `b⁽¹⁾, ..., b⁽ᵐ⁾ ∈ ℝ`. -/
  b : Fin m → ℝ
  /-- The lower box bound `α ∈ ℝⁿ`. -/
  α : EuclideanSpace ℝ (Fin n)
  /-- The upper box bound `β ∈ ℝⁿ`. -/
  β : EuclideanSpace ℝ (Fin n)

namespace LpApproximationBoxProblem

/-- The canonical Chapter 1 owner attached to a box-constrained `ℓ_p` approximation problem. -/
def toSetConstrainedMinimizationProblem
    (problem : LpApproximationBoxProblem n m) :
    SetConstrainedMinimizationProblem E :=
  lpApproximationProblem problem.p problem.a problem.b problem.α problem.β

/-- The exponent of a box-constrained `ℓ_p` approximation problem satisfies `p ≥ 1`. -/
theorem one_le_p (problem : LpApproximationBoxProblem n m) : 1 ≤ (problem.p : ℝ) :=
  problem.p.2

/-- The feasible box `\{x : ℝⁿ | α ≤ x ≤ β\}` of an `ℓ_p` approximation problem. -/
abbrev feasibleSet (problem : LpApproximationBoxProblem n m) : Set E :=
  problem.toSetConstrainedMinimizationProblem.feasibleSet

/-- The owner bridge preserves the box feasible set. -/
@[simp] theorem toSetConstrainedMinimizationProblem_feasibleSet
    (problem : LpApproximationBoxProblem n m) :
    problem.toSetConstrainedMinimizationProblem.feasibleSet = problem.feasibleSet :=
  rfl

/-- The owner bridge evaluates to the `ℓ_p` approximation objective. -/
@[simp] theorem toSetConstrainedMinimizationProblem_apply
    (problem : LpApproximationBoxProblem n m) (x : E) :
    problem.toSetConstrainedMinimizationProblem x =
      lpApproximationObjective problem.p problem.a problem.b x :=
  rfl

/-- An `ℓ_p` approximation problem with box constraints can be evaluated as its objective
function. -/
instance : CoeFun (LpApproximationBoxProblem n m) (fun _ ↦ E → ℝ) where
  coe problem := problem.toSetConstrainedMinimizationProblem

/-- Evaluating a box-constrained `ℓ_p` approximation problem returns its objective value. -/
@[simp] theorem coe_apply
    (problem : LpApproximationBoxProblem n m) (x : E) :
    problem x = lpApproximationObjective problem.p problem.a problem.b x :=
  rfl

/-- A point is feasible exactly when it lies componentwise between the box bounds `α` and `β`. -/
-- Proof sketch: unfold `feasibleSet`; membership is exactly the coordinatewise condition
-- `∀ i, problem.α i ≤ x i ∧ x i ≤ problem.β i`.
@[simp] theorem mem_feasibleSet_iff
    (problem : LpApproximationBoxProblem n m) (x : E) :
    x ∈ problem.feasibleSet ↔
      ∀ i : Fin n, problem.α i ≤ x i ∧ x i ≤ problem.β i := by
  simp [feasibleSet, toSetConstrainedMinimizationProblem]

/-- Evaluating the objective expands to the finite sum of `p`-th powers of the residual
terms `|⟪aᵢ, x⟫ - b⁽ⁱ⁾|`. -/
-- Proof sketch: expand the inherited coercion to `lpApproximationObjective`; the displayed
-- equality is exactly its defining formula.
@[simp] theorem objective_apply
    (problem : LpApproximationBoxProblem n m) (x : E) :
    problem x =
      ∑ i : Fin m, |⟪problem.a i, x⟫ - problem.b i| ^ (problem.p : ℝ) := by
  simp [lpApproximationObjective]

end LpApproximationBoxProblem
