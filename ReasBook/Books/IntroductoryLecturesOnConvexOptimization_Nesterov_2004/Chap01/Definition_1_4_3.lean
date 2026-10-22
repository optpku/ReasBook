/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_1_4_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_1_4_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3

-- Declarations for this item will be appended below by the statement pipeline.

namespace SetConstrainedMinimizationProblem

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

open FunctionalConstraintsMinimizationProblem
open GeneralMinimizationProblem

/- Definition 1.4.3 lies in the optimization-regularity domain.

Sampled owner-style declarations:
* `SetConstrainedMinimizationProblem`, the owner of the feasible-set and objective data;
* `FunctionalConstraintsMinimizationProblem.IsConstrained` together with
  `FunctionalConstraintsMinimizationProblem.not_isConstrained_iff_feasibleSet_eq_univ` in
  `Definition_1_1_4_1`, the earlier Chapter 1 owner for unconstrainedness;
* `GeneralMinimizationProblem.IsSmooth`, the earlier Chapter 1 owner for smoothness;
* `SetConstrainedMinimizationProblem.toGeneralMinimizationProblem`, the canonical bridge from a
  set-constrained problem to that earlier owner.

Best owner abstraction:
* `problem.toGeneralMinimizationProblem`, together with the owner predicates
  `¬ problem.toGeneralMinimizationProblem.IsConstrained` and
  `problem.toGeneralMinimizationProblem.IsSmooth`.

Primitive data:
* `problem.feasibleSet`
* `problem.objective`

Derived API:
* the canonical owner conjunction
  `¬ problem.toGeneralMinimizationProblem.IsConstrained ∧
    problem.toGeneralMinimizationProblem.IsSmooth`
* the smoothness bridge `isSmooth_iff_differentiable`, which turns owner smoothness into
  ordinary differentiability once the feasible set is known to be all of `ℝⁿ`
* the companion bridge `unconstrainedSmooth_iff`, which recovers the textbook formulation
  `problem.feasibleSet = Set.univ ∧ Differentiable ℝ problem`
* the direct consequences `feasibleSet_eq_univ_of_unconstrainedSmooth` and
  `differentiable_of_unconstrainedSmooth`

Source/core/bridge triage:
* source-facing: the canonical owner conjunction above
* core/canonical: `problem.toGeneralMinimizationProblem` with the owner predicates above
* bridge/view: `unconstrainedSmooth_iff`. -/

variable (problem : SetConstrainedMinimizationProblem E)

/- Definition 1.4.3: an unconstrained smooth minimization problem on `ℝⁿ` is a
set-constrained minimization problem whose canonical earlier Chapter 1 owner is both
unconstrained and smooth. -/
#check (
  ¬ problem.toGeneralMinimizationProblem.IsConstrained ∧
    problem.toGeneralMinimizationProblem.IsSmooth
)

private theorem toGeneralMinimizationProblem_objectiveOnAmbient_eq_objective
    (problem : SetConstrainedMinimizationProblem E)
    (hfeasibleSet : problem.feasibleSet = Set.univ) :
    problem.toGeneralMinimizationProblem.objectiveOnAmbient = problem.objective := by
  ext x
  have hx : x ∈ problem.toGeneralMinimizationProblem.basicFeasibleSet := by
    change x ∈ problem.feasibleSet
    simp [hfeasibleSet]
  simpa [SetConstrainedMinimizationProblem.toGeneralMinimizationProblem,
    SetConstrainedMinimizationProblem.toFunctionalConstraintsMinimizationProblem] using
    FunctionalConstraintsMinimizationProblem.objectiveOnAmbient_apply
      problem.toGeneralMinimizationProblem hx

private theorem toGeneralMinimizationProblem_feasibleSet_eq_feasibleSet
    (problem : SetConstrainedMinimizationProblem E) :
    (problem.toGeneralMinimizationProblem.feasibleSet : Set E) = problem.feasibleSet := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact y.2
  · intro hx
    refine ⟨⟨x, hx⟩, ?_, rfl⟩
    change problem.toGeneralMinimizationProblem.IsFeasible ⟨x, hx⟩
    intro i
    exact Fin.elim0 i

private theorem feasibleSet_eq_univ_of_toGeneralMinimizationProblem_not_isConstrained
    (problem : SetConstrainedMinimizationProblem E) :
    ¬ problem.toGeneralMinimizationProblem.IsConstrained → problem.feasibleSet = Set.univ := by
  intro hunconstrained
  refine Set.eq_univ_iff_forall.2 ?_
  intro x
  by_contra hx
  apply hunconstrained
  constructor
  · exact Set.subset_univ _
  · intro hsubset
    have hx' : x ∈ (problem.toGeneralMinimizationProblem.feasibleSet : Set E) := hsubset (by
      trivial)
    rw [toGeneralMinimizationProblem_feasibleSet_eq_feasibleSet problem] at hx'
    exact hx hx'

private theorem toGeneralMinimizationProblem_not_isConstrained_of_feasibleSet_eq_univ
    (problem : SetConstrainedMinimizationProblem E)
    (hfeasibleSet : problem.feasibleSet = Set.univ) :
    ¬ problem.toGeneralMinimizationProblem.IsConstrained := by
  intro hconstrained
  apply hconstrained.2
  intro x
  rw [toGeneralMinimizationProblem_feasibleSet_eq_feasibleSet problem, hfeasibleSet]
  intro _
  trivial

private theorem toGeneralMinimizationProblem_constraintVectorOnAmbient_eq_zero
    (problem : SetConstrainedMinimizationProblem E) :
    problem.toGeneralMinimizationProblem.constraintVectorOnAmbient =
      fun _ : E ↦ (0 : EuclideanSpace ℝ (Fin 0)) := by
  ext x i
  exact Fin.elim0 i

/-- If the feasible set is all of `ℝⁿ`, then the owner smoothness predicate is exactly ordinary
differentiability of the objective. -/
theorem isSmooth_iff_differentiable
    (problem : SetConstrainedMinimizationProblem E)
    (hfeasibleSet : problem.feasibleSet = Set.univ) :
    problem.toGeneralMinimizationProblem.IsSmooth ↔ Differentiable ℝ problem.objective := by
  constructor
  · intro hsmooth
    have hobjective :
        DifferentiableOn ℝ problem.toGeneralMinimizationProblem.objectiveOnAmbient
          problem.toGeneralMinimizationProblem.basicFeasibleSet := hsmooth.1
    change DifferentiableOn ℝ problem.toGeneralMinimizationProblem.objectiveOnAmbient
      problem.feasibleSet at hobjective
    rw [hfeasibleSet] at hobjective
    have hdiff : Differentiable ℝ problem.toGeneralMinimizationProblem.objectiveOnAmbient :=
      differentiableOn_univ.mp hobjective
    simpa [toGeneralMinimizationProblem_objectiveOnAmbient_eq_objective problem hfeasibleSet]
      using hdiff
  · intro hdiff
    refine ⟨?_, ?_⟩
    · change DifferentiableOn ℝ problem.toGeneralMinimizationProblem.objectiveOnAmbient
        problem.feasibleSet
      rw [hfeasibleSet]
      have hobjective : DifferentiableOn ℝ problem.objective Set.univ :=
        differentiableOn_univ.mpr hdiff
      have hobjective_eq :=
        toGeneralMinimizationProblem_objectiveOnAmbient_eq_objective problem hfeasibleSet
      rw [← hobjective_eq] at hobjective
      exact hobjective
    · change DifferentiableOn ℝ problem.toGeneralMinimizationProblem.constraintVectorOnAmbient
        problem.feasibleSet
      rw [hfeasibleSet]
      have hzero :
          DifferentiableOn ℝ (fun _ : E ↦ (0 : EuclideanSpace ℝ (Fin 0))) Set.univ := by
        rw [differentiableOn_univ]
        exact differentiable_const (0 : EuclideanSpace ℝ (Fin 0))
      rw [toGeneralMinimizationProblem_constraintVectorOnAmbient_eq_zero problem]
      exact hzero

/-- The canonical owner expression for Definition 1.4.3 is equivalent to the textbook
whole-space differentiability formulation. -/
theorem unconstrainedSmooth_iff
    (problem : SetConstrainedMinimizationProblem E) :
    (¬ problem.toGeneralMinimizationProblem.IsConstrained ∧
      problem.toGeneralMinimizationProblem.IsSmooth) ↔
      problem.feasibleSet = Set.univ ∧ Differentiable ℝ problem.objective := by
  constructor
  · rintro ⟨hunconstrained, hsmooth⟩
    have hfeasibleSet : problem.feasibleSet = Set.univ :=
      feasibleSet_eq_univ_of_toGeneralMinimizationProblem_not_isConstrained problem hunconstrained
    exact ⟨hfeasibleSet, (isSmooth_iff_differentiable problem hfeasibleSet).mp hsmooth⟩
  · rintro ⟨hfeasibleSet, hdiff⟩
    exact
      ⟨toGeneralMinimizationProblem_not_isConstrained_of_feasibleSet_eq_univ problem hfeasibleSet,
        (isSmooth_iff_differentiable problem hfeasibleSet).mpr hdiff⟩

/-- The owner expression of Definition 1.4.3 forces the feasible set to be all of `ℝⁿ`. -/
theorem feasibleSet_eq_univ_of_unconstrainedSmooth
    (problem : SetConstrainedMinimizationProblem E)
    (h : ¬ problem.toGeneralMinimizationProblem.IsConstrained ∧
      problem.toGeneralMinimizationProblem.IsSmooth) :
    problem.feasibleSet = Set.univ :=
  (unconstrainedSmooth_iff problem).mp h |>.1

/-- The owner expression of Definition 1.4.3 gives a differentiable objective on `ℝⁿ`. -/
theorem differentiable_of_unconstrainedSmooth
    (problem : SetConstrainedMinimizationProblem E)
    (h : ¬ problem.toGeneralMinimizationProblem.IsConstrained ∧
      problem.toGeneralMinimizationProblem.IsSmooth) :
    Differentiable ℝ problem.objective :=
  (unconstrainedSmooth_iff problem).mp h |>.2

end SetConstrainedMinimizationProblem
