/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

namespace SetConstrainedMinimizationProblem

open scoped ConstrainedArgmin

variable {X : Type u}

/- Definition 1.3.7 is expressed through the Chapter 1 owner abstraction
`SetConstrainedMinimizationProblem`. The primitive data remain only the feasible set and
objective; the optimal value and approximate-minimizer predicate are derived notions. -/

/-- The optimal value `f* = inf_{x ∈ Q} f(x)` of a set-constrained minimization problem, viewed
in `EReal` so that unbounded-below feasible objectives are represented faithfully. -/
def optimalValue (problem : SetConstrainedMinimizationProblem X) : EReal :=
  sInf ((fun x ↦ (problem x : EReal)) '' problem.feasibleSet)

/-- Expanding `problem.optimalValue` gives the infimum of the feasible objective values, taken
over the owner feasible set. -/
theorem optimalValue_eq_sInf_image (problem : SetConstrainedMinimizationProblem X) :
    problem.optimalValue =
      sInf ((fun x ↦ (problem x : EReal)) '' problem.feasibleSet) :=
  rfl

/-- The optimal value is bounded above by the objective value at every feasible point. -/
theorem optimalValue_le_of_mem_feasibleSet
    (problem : SetConstrainedMinimizationProblem X) {x : X} (hx : x ∈ problem.feasibleSet) :
    problem.optimalValue ≤ (problem x : EReal) := by
  rw [optimalValue_eq_sInf_image]
  refine csInf_le ?_ ?_
  · exact ⟨⊥, fun _ _ ↦ bot_le⟩
  · exact ⟨x, hx, rfl⟩

/-- If two constrained minimization problems have the same feasible set and the first objective is
pointwise bounded above by the second on that feasible set, then the first owner optimal value is
bounded above by the second. -/
theorem optimalValue_le_optimalValue_of_forall_le
    (problem₁ problem₂ : SetConstrainedMinimizationProblem X)
    (hfeasible : problem₁.feasibleSet = problem₂.feasibleSet)
    (hpointwise : ∀ x ∈ problem₁.feasibleSet, problem₁ x ≤ problem₂ x) :
    problem₁.optimalValue ≤ problem₂.optimalValue := by
  rw [problem₂.optimalValue_eq_sInf_image]
  refine le_sInf ?_
  rintro _ ⟨x, hx₂, rfl⟩
  have hx₁ : x ∈ problem₁.feasibleSet := by
    simpa [hfeasible] using hx₂
  refine (problem₁.optimalValue_le_of_mem_feasibleSet hx₁).trans ?_
  change ((problem₁ x : ℝ) : EReal) ≤ ((problem₂ x : ℝ) : EReal)
  exact_mod_cast hpointwise x hx₁

/-- If two constrained minimization problems have the same feasible set and the first objective is
pointwise at most `Δ` above the second on that feasible set, then the first owner optimal value is
at most `Δ` above the second. -/
theorem optimalValue_sub_le_optimalValue_of_forall_sub_le
    (problem₁ problem₂ : SetConstrainedMinimizationProblem X) {Δ : ℝ}
    (hfeasible : problem₁.feasibleSet = problem₂.feasibleSet)
    (hpointwise : ∀ x ∈ problem₁.feasibleSet, problem₁ x - Δ ≤ problem₂ x) :
    problem₁.optimalValue - Δ ≤ problem₂.optimalValue := by
  rw [problem₂.optimalValue_eq_sInf_image]
  refine le_sInf ?_
  rintro _ ⟨x, hx₂, rfl⟩
  apply EReal.sub_le_of_le_add
  have hx₁ : x ∈ problem₁.feasibleSet := by
    simpa [hfeasible] using hx₂
  refine (problem₁.optimalValue_le_of_mem_feasibleSet hx₁).trans ?_
  have hpointwise' : problem₁ x ≤ problem₂ x + Δ := by
    exact sub_le_iff_le_add.mp (hpointwise x hx₁)
  change ((problem₁ x : ℝ) : EReal) ≤ ((problem₂ x : ℝ) : EReal) + (Δ : EReal)
  exact_mod_cast hpointwise'

/-- If the constrained minimum is attained at a feasible point, then the owner optimal value is
that attained objective value. -/
theorem optimalValue_eq_of_isMinOn
    (problem : SetConstrainedMinimizationProblem X) {x : X} (hx : x ∈ problem.feasibleSet)
    (hmin : IsMinOn problem problem.feasibleSet x) :
    problem.optimalValue = (problem x : EReal) := by
  rw [optimalValue_eq_sInf_image]
  have hminEReal : IsMinOn (fun y ↦ (problem y : EReal)) problem.feasibleSet x := by
    rw [isMinOn_iff] at hmin ⊢
    intro y hy
    exact_mod_cast hmin y hy
  exact (hminEReal.isGLB hx).csInf_eq ⟨_, ⟨x, hx, rfl⟩⟩

/-- Any point in the canonical constrained argmin set realizes the owner optimal value. -/
theorem optimalValue_eq_of_mem_argmin
    (problem : SetConstrainedMinimizationProblem X) {x : X}
    (hx : x ∈ argmin[problem.feasibleSet] problem) :
    problem.optimalValue = (problem x : EReal) := by
  rw [mem_constrainedArgmin_iff] at hx
  exact problem.optimalValue_eq_of_isMinOn hx.1 hx.2

/-- Definition 1.3.7: `xBar` is an `ε`-approximate minimizer in function value for a
set-constrained minimization problem when it is feasible and its objective value is at most `ε`
above the optimal value. -/
def IsApproximateMinimizer (problem : SetConstrainedMinimizationProblem X)
    (ε : ℝ) (xBar : X) : Prop :=
  xBar ∈ problem.feasibleSet ∧ (problem xBar : EReal) ≤ problem.optimalValue + ε

/-- Unfolding `problem.IsApproximateMinimizer ε xBar` gives feasibility together with the
canonical additive bound on the objective value. -/
@[simp] theorem isApproximateMinimizer_iff (problem : SetConstrainedMinimizationProblem X)
    (ε : ℝ) (xBar : X) :
    problem.IsApproximateMinimizer ε xBar ↔
      xBar ∈ problem.feasibleSet ∧ (problem xBar : EReal) ≤ problem.optimalValue + ε :=
  Iff.rfl

end SetConstrainedMinimizationProblem

namespace FunctionalConstraintsMinimizationProblem

variable {X : Type u} {m : ℕ}

/-- A functional-constraint minimization problem canonically yields a set-constrained
minimization problem on its basic feasible set, with feasible points cut out by the owner
constraint family and objective inherited from the owner objective. -/
def toSetConstrainedMinimizationProblem
    (problem : FunctionalConstraintsMinimizationProblem X m) :
    SetConstrainedMinimizationProblem problem.basicFeasibleSet where
  feasibleSet := problem.feasibleSet
  objective := problem

/-- The canonical bridge preserves the owner feasible set. -/
@[simp] theorem toSetConstrainedMinimizationProblem_feasibleSet
    (problem : FunctionalConstraintsMinimizationProblem X m) :
    problem.toSetConstrainedMinimizationProblem.feasibleSet = problem.feasibleSet :=
  rfl

/-- The canonical bridge evaluates to the owner objective. -/
@[simp] theorem toSetConstrainedMinimizationProblem_apply
    (problem : FunctionalConstraintsMinimizationProblem X m)
    (x : problem.basicFeasibleSet) :
    problem.toSetConstrainedMinimizationProblem x = problem x :=
  rfl

end FunctionalConstraintsMinimizationProblem
