/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_1_4_5

-- Declarations for this item will be appended below by the statement pipeline.

open AffineMap

namespace Set

/-- A map on a subset is quadratic when it differs from the restriction of an ambient quadratic map
by an affine map on that subset. -/
def QuadraticOn {X Y : Type*} (Q : Set X) (k : Type*) [CommRing k] [AddCommGroup X] [Module k X]
    [AddCommGroup Y] [Module k Y] (f : Q → Y) : Prop :=
  ∃ q : QuadraticMap k X Y, Set.AffineOn Q k (fun x ↦ f x - q x.1)

end Set

namespace FunctionalConstraintsMinimizationProblem

variable {X : Type*} [AddCommGroup X] [Module ℝ X] {m : ℕ}

local notation "F" => EuclideanSpace ℝ (Fin m)

/-
Definition 1.1.4.7 lies in the quadratic constrained-optimization domain.

Sampled owner-side declarations in this domain:
* `FunctionalConstraintsMinimizationProblem.constraintVector`
* `FunctionalConstraintsMinimizationProblem.IsLinearlyConstrained`
* `Set.AffineOn`
* `QuadraticMap`

Owner abstraction:
* `FunctionalConstraintsMinimizationProblem X m` for the constrained-problem owner
* `Set.QuadraticOn` for quadratic data on `problem.basicFeasibleSet`

Source/core/bridge triage:
* `source-facing`: the textbook `GeneralMinimizationProblem n m` specialization
* `core/canonical`: `FunctionalConstraintsMinimizationProblem.IsQuadraticOptimizationProblem`
* `bridge/view`: the coordinatewise quadraticity theorem for `problem.constraintVector`

Primitive data:
* quadratic objective data on `problem.basicFeasibleSet`
* linearly constrained constraint data

Derived API:
* coordinatewise quadraticity of the scalar constraints
* owner-side consequences of quadratic optimization

As in Definition 1.1.4.6, nothing in the main notion uses coordinates on `ℝⁿ`; the Euclidean
ambient space is only the textbook specialization of this owner-level predicate.
-/

/-- The packaged owner constraint vector is quadratic exactly when each scalar constraint is
quadratic. -/
theorem constraintVector_quadraticOn_iff_forall_constraint_quadraticOn
    (problem : FunctionalConstraintsMinimizationProblem X m) :
    Set.QuadraticOn problem.basicFeasibleSet ℝ problem.constraintVector ↔
      ∀ j : Fin m, Set.QuadraticOn problem.basicFeasibleSet ℝ (problem.constraints j) := by
  constructor
  · rintro ⟨q, g, hg⟩ j
    refine ⟨(EuclideanSpace.projₗ j).compQuadraticMap q, ?_⟩
    refine ⟨(EuclideanSpace.projₗ j).toAffineMap.comp g, ?_⟩
    intro x hx
    change (problem.constraintVector ⟨x, hx⟩ - q x) j =
      ((EuclideanSpace.projₗ j).toAffineMap.comp g) x
    simpa using congrArg (fun y : F ↦ y j) (hg x hx)
  · intro h
    choose q hq using h
    choose g hg using hq
    refine ⟨
      (EuclideanSpace.equiv (Fin m) ℝ).symm.toLinearMap.compQuadraticMap
        (∑ j, (LinearMap.single ℝ (fun _ : Fin m ↦ ℝ) j).compQuadraticMap (q j)),
      ?_⟩
    refine ⟨
      ((EuclideanSpace.equiv (Fin m) ℝ).symm.toLinearMap.toAffineMap).comp (pi g),
      ?_⟩
    intro x hx
    ext j
    simp [hg j x hx]

/-- Quadraticity of the packaged owner constraint vector implies quadraticity of each scalar
constraint. -/
theorem constraint_isQuadratic
    {problem : FunctionalConstraintsMinimizationProblem X m}
    (h : Set.QuadraticOn problem.basicFeasibleSet ℝ problem.constraintVector)
    (j : Fin m) :
    Set.QuadraticOn problem.basicFeasibleSet ℝ (problem.constraints j) :=
  (problem.constraintVector_quadraticOn_iff_forall_constraint_quadraticOn.mp h) j

/-- Definition 1.1.4.7: a quadratic optimization problem is a minimization problem whose objective
function is quadratic and which is linearly constrained in the sense of
Definition 1.1.4.5. -/
def IsQuadraticOptimizationProblem
    (problem : FunctionalConstraintsMinimizationProblem X m) : Prop :=
  Set.QuadraticOn problem.basicFeasibleSet ℝ problem.objective ∧ problem.IsLinearlyConstrained

/-- A quadratic optimization problem has a quadratic objective function. -/
theorem IsQuadraticOptimizationProblem.objective_isQuadratic
    {problem : FunctionalConstraintsMinimizationProblem X m}
    (h : problem.IsQuadraticOptimizationProblem) :
    Set.QuadraticOn problem.basicFeasibleSet ℝ problem.objective :=
  h.1

/-- A quadratic optimization problem is, in particular, linearly constrained. -/
theorem IsQuadraticOptimizationProblem.isLinearlyConstrained
    {problem : FunctionalConstraintsMinimizationProblem X m}
    (h : problem.IsQuadraticOptimizationProblem) :
    problem.IsLinearlyConstrained :=
  h.2

/-- Every functional constraint of a quadratic optimization problem is affine. -/
theorem IsQuadraticOptimizationProblem.constraint_isAffine
    {problem : FunctionalConstraintsMinimizationProblem X m}
    (h : problem.IsQuadraticOptimizationProblem) (j : Fin m) :
    Set.AffineOn problem.basicFeasibleSet ℝ (problem.constraints j) :=
  h.isLinearlyConstrained.constraint_isAffine j

/-- A quadratic optimization problem has a polyhedral basic feasible set. -/
theorem IsQuadraticOptimizationProblem.isPolyhedron
    {problem : FunctionalConstraintsMinimizationProblem X m}
    (h : problem.IsQuadraticOptimizationProblem) :
    problem.basicFeasibleSet.IsPolyhedron :=
  h.isLinearlyConstrained.isPolyhedron

end FunctionalConstraintsMinimizationProblem

namespace GeneralMinimizationProblem

variable {n m : ℕ} (problem : GeneralMinimizationProblem n m)

/- Definition 1.1.4.7 in the textbook Euclidean ambient space is the specialization of the owner
predicate `FunctionalConstraintsMinimizationProblem.IsQuadraticOptimizationProblem`. -/
#check problem.IsQuadraticOptimizationProblem

end GeneralMinimizationProblem
