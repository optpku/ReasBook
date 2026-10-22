/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_1_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Definition 1.1.4.3 lies in the differentiability domain of constrained optimization with a
finite family of scalar constraints.

Sampled owner-style declarations:
* `FunctionalConstraintsMinimizationProblem` in `Definition_1_1_3`, the ambient constrained owner
* `FunctionalConstraintsMinimizationProblem.constraintVector` in `Definition_1_1_1`, the packaged
  finite constraint family
* `DifferentiableOn` together with `differentiableOn_piLp`
* mathlib's canonical ambient-extension operator `Function.extend Subtype.val`

Best owner abstraction:
* `FunctionalConstraintsMinimizationProblem X m`

Primitive data:
* `problem.basicFeasibleSet`
* `problem.objective`
* `problem.constraintVector`

Derived API:
* the ambient zero-extensions `problem.objectiveOnAmbient` and
  `problem.constraintVectorOnAmbient`
* the ambient textbook family `problem.componentOnAmbient`
* the owner smoothness predicate `problem.IsSmooth`
* the componentwise bridge `constraintVector_differentiableOn_iff`

Source/core/bridge triage:
* source-facing: the textbook `GeneralMinimizationProblem n m` specialization
* core/canonical: the ambient owner predicate `problem.IsSmooth`
* bridge/view: the ambient extension maps, the `Fin (m + 1)` component family, and the Euclidean
  specialization

Smoothness here depends only on a real normed ambient space, not on the concrete Euclidean model
`EuclideanSpace ℝ (Fin n)`, so the public owner belongs on
`FunctionalConstraintsMinimizationProblem X m` and the textbook `ℝⁿ` case is recovered as a
specialization. -/

namespace FunctionalConstraintsMinimizationProblem

section AmbientExtension

variable {X : Type u} {m : ℕ}

local notation "F" => EuclideanSpace ℝ (Fin m)

/-- The objective function of a minimization problem, viewed on the ambient space by extending the
owner objective by `0` outside the basic feasible set. -/
noncomputable def objectiveOnAmbient (problem : FunctionalConstraintsMinimizationProblem X m) :
    X → ℝ :=
  Function.extend Subtype.val problem.objective 0

/-- The full constraint family of a minimization problem, viewed on the ambient space by extending
the owner constraint vector by `0` outside the basic feasible set. -/
noncomputable def constraintVectorOnAmbient
    (problem : FunctionalConstraintsMinimizationProblem X m) : X → F :=
  Function.extend Subtype.val problem.constraintVector 0

@[simp] theorem objectiveOnAmbient_apply
    (problem : FunctionalConstraintsMinimizationProblem X m) {x : X}
    (hx : x ∈ problem.basicFeasibleSet) :
    problem.objectiveOnAmbient x = problem.objective ⟨x, hx⟩ := by
  simpa [objectiveOnAmbient] using Function.extend_val_apply hx

@[simp] theorem constraintVectorOnAmbient_apply
    (problem : FunctionalConstraintsMinimizationProblem X m) {x : X}
    (hx : x ∈ problem.basicFeasibleSet) :
    problem.constraintVectorOnAmbient x = problem.constraintVector ⟨x, hx⟩ := by
  simpa [constraintVectorOnAmbient] using Function.extend_val_apply hx

/-- The unified ambient family `f₀, f₁, …, f_m`, where index `0` is the objective and successor
indices are the scalar constraints, obtained by extending each owner component by `0` outside the
basic feasible set. -/
noncomputable def componentOnAmbient
    (problem : FunctionalConstraintsMinimizationProblem X m) :
    Fin (m + 1) → X → ℝ :=
  Fin.cases problem.objectiveOnAmbient fun i ↦ fun x ↦ problem.constraintVectorOnAmbient x i

@[simp] theorem componentOnAmbient_zero
    (problem : FunctionalConstraintsMinimizationProblem X m) :
    problem.componentOnAmbient 0 = problem.objectiveOnAmbient :=
  rfl

@[simp] theorem componentOnAmbient_succ
    (problem : FunctionalConstraintsMinimizationProblem X m) (i : Fin m) :
    problem.componentOnAmbient i.succ = fun x ↦ problem.constraintVectorOnAmbient x i :=
  rfl

end AmbientExtension

section Smoothness

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X] {m : ℕ}

/-- Definition 1.1.4.3: a functional-constraint minimization problem is smooth when the ambient
extensions of the objective and the packaged constraint vector are differentiable on the basic
feasible set. The textbook family `f₀, f₁, …, f_m` is recovered from these owner maps. -/
def IsSmooth (problem : FunctionalConstraintsMinimizationProblem X m) : Prop :=
  DifferentiableOn ℝ problem.objectiveOnAmbient problem.basicFeasibleSet ∧
    DifferentiableOn ℝ problem.constraintVectorOnAmbient problem.basicFeasibleSet

/-- Smoothness implies differentiability of the objective on the basic feasible set. -/
theorem IsSmooth.objective_differentiableOn
    {problem : FunctionalConstraintsMinimizationProblem X m} (h : problem.IsSmooth) :
    DifferentiableOn ℝ problem.objectiveOnAmbient problem.basicFeasibleSet :=
  h.1

/-- Smoothness implies differentiability of the full constraint map on the basic feasible set. -/
theorem IsSmooth.constraintVector_differentiableOn
    {problem : FunctionalConstraintsMinimizationProblem X m} (h : problem.IsSmooth) :
    DifferentiableOn ℝ problem.constraintVectorOnAmbient problem.basicFeasibleSet :=
  h.2

/-- Smoothness implies continuity of the objective on the basic feasible set. -/
theorem IsSmooth.objective_continuous
    {problem : FunctionalConstraintsMinimizationProblem X m} (h : problem.IsSmooth) :
    Continuous problem.objective := by
  have hObjectiveContinuousOn : ContinuousOn problem.objectiveOnAmbient problem.basicFeasibleSet :=
    h.objective_differentiableOn.continuousOn
  convert hObjectiveContinuousOn.restrict using 1
  ext x
  simp

/-- Smoothness implies continuity of the packaged constraint map on the basic feasible set. -/
theorem IsSmooth.constraintVector_continuous
    {problem : FunctionalConstraintsMinimizationProblem X m} (h : problem.IsSmooth) :
    Continuous problem.constraintVector := by
  have hConstraintContinuousOn :
      ContinuousOn problem.constraintVectorOnAmbient problem.basicFeasibleSet :=
    h.constraintVector_differentiableOn.continuousOn
  convert hConstraintContinuousOn.restrict using 1
  ext x
  simp

/-- The full constraint map is differentiable on the basic feasible set exactly when each scalar
constraint component is differentiable there. -/
theorem constraintVector_differentiableOn_iff
    (problem : FunctionalConstraintsMinimizationProblem X m) :
    DifferentiableOn ℝ problem.constraintVectorOnAmbient problem.basicFeasibleSet ↔
      ∀ i : Fin m,
        DifferentiableOn ℝ (fun x ↦ problem.constraintVectorOnAmbient x i)
          problem.basicFeasibleSet := by
  simpa using differentiableOn_piLp (2 : ENNReal)

/-- Smoothness is equivalent to differentiability of every member of the ambient textbook family
`f₀, f₁, …, f_m` on the basic feasible set. -/
theorem isSmooth_iff_forall_component_differentiableOn
    (problem : FunctionalConstraintsMinimizationProblem X m) :
    problem.IsSmooth ↔
      ∀ j : Fin (m + 1),
        DifferentiableOn ℝ (problem.componentOnAmbient j) problem.basicFeasibleSet := by
  rw [IsSmooth, Fin.forall_fin_succ]
  constructor
  · rintro ⟨hObjective, hConstraintVector⟩
    refine ⟨?_, (constraintVector_differentiableOn_iff problem).mp hConstraintVector⟩
    simpa using hObjective
  · rintro ⟨hObjective, hConstraints⟩
    refine ⟨?_, (constraintVector_differentiableOn_iff problem).mpr hConstraints⟩
    simpa using hObjective

/-- Smoothness implies differentiability of each scalar constraint on the basic feasible set. -/
theorem IsSmooth.constraint_differentiableOn
    {problem : FunctionalConstraintsMinimizationProblem X m} (h : problem.IsSmooth)
    (i : Fin m) :
    DifferentiableOn ℝ (fun x ↦ problem.constraintVectorOnAmbient x i)
      problem.basicFeasibleSet := by
  exact (constraintVector_differentiableOn_iff problem).mp h.constraintVector_differentiableOn i

end Smoothness

end FunctionalConstraintsMinimizationProblem

namespace GeneralMinimizationProblem

section

variable {n m : ℕ} (problem : GeneralMinimizationProblem n m)

/- Definition 1.1.4.3 in the textbook Euclidean ambient space is the specialization of the
ambient owner predicate `FunctionalConstraintsMinimizationProblem.IsSmooth`. -/
#check problem.IsSmooth

end

end GeneralMinimizationProblem
