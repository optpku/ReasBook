/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_31

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient
open scoped PrimalEqualityConstrainedProblem.LagrangianMinimizerSelectionNotation

noncomputable section

universe u v

/- Primary domain: equality-constrained Lagrangian duality with a chosen minimizing primal
selection.

Owner declarations sampled before refining this file:
* `LagrangianProblem.lagrangianMinimizers` and `LagrangianProblem.dualFunction` in
  `Nesterov/Chap01/Definition_1_10_2.lean`;
* `PrimalEqualityConstrainedProblem.lagrangian`, `dualFunction`, `constraintResidual`, and
  `mem_equalityFeasibleSet_iff` in `Nesterov/Chap02/Definition_2_30.lean`;
* `PrimalEqualityConstrainedProblem.LagrangianMinimizerSelection`, together with the derived
  equality-problem API `LagrangianMinimizerSelection.isMinOn` and
  `LagrangianMinimizerSelection.dualFunction_eq_lagrangian`, in
  `Nesterov/Chap02/Definition_2_31.lean`;
* mathlib `HasGradientAt.unique` and `IsLocalMax.fderiv_eq_zero`, which give the canonical local
  stationary-point bridge at a dual maximizer.

Best owner abstraction: the primitive selected data are a
`LagrangianMinimizerSelection problem` over the equality problem's own Lagrangian layer, not an
independent function `x : Λ → problem.basicSet` plus separate minimizer proofs.

Primitive data here are `problem`, a minimizing selection `selection`, and the multiplier `uStar`.
The residual, the selected dual profile
`u ↦ problem.lagrangian (selection u) u`, the subproblem optimality
statement, and the dual-value identity are all derived API from the owner selection abstraction.
The pointwise stationarity input at `uStar` is most faithfully expressed by
`HasGradientAt` for that selected dual profile, not by a global equation for mathlib's total
`gradient`.
-/

namespace PrimalEqualityConstrainedProblem
namespace LagrangianMinimizerSelection

variable {E : Type u} {Λ : Type v} [AddCommMonoid E] [Module ℝ E]
variable [NormedAddCommGroup Λ] [InnerProductSpace ℝ Λ]
variable {problem : PrimalEqualityConstrainedProblem E Λ}
variable (selection : LagrangianMinimizerSelection problem)

local notation "Q₌" => problem.equalityFeasibleSet
local notation "φ" => φ[selection]
local notation "g" => g[selection]

/-- The owner-facing core of Proposition 2.20: if the selected dual residual vanishes at `uStar`,
then the selected minimizer is feasible and minimizes the primal objective on the feasible set. -/
-- Proof sketch: `dualResidual selection uStar = 0` is exactly the equality-constraint residual
-- vanishing at `selection uStar`, hence `selection uStar` is feasible. For any feasible `y`, the
-- minimizer property `isMinOn selection uStar` compares the two Lagrangian values at
-- `selection uStar` and `y`; feasibility removes the multiplier term on both sides, leaving the
-- desired objective comparison on the owner feasible set.
theorem isMinOn_feasibleSet_of_dualResidual_eq_zero
    {uStar : Λ}
    (hresidual : g uStar = 0) :
    (selection uStar : E) ∈ Q₌ ∧
      IsMinOn problem Q₌ (selection uStar) := by
  have hselection_mem :
      (selection uStar : E) ∈ problem.feasibleSet :=
    (problem.mem_lagrangianMinimizers_iff.mp (selection uStar).2).1
  have hfeasible : (selection uStar : E) ∈ Q₌ := by
    rw [problem.mem_equalityFeasibleSet_iff_constraintResidual_eq_zero]
    exact ⟨hselection_mem, hresidual⟩
  have hmin := selection.isMinOn uStar
  rw [isMinOn_iff] at hmin ⊢
  constructor
  · exact hfeasible
  · intro y hy
    have hy' := problem.mem_equalityFeasibleSet_iff_constraintResidual_eq_zero.mp hy
    have hselectedResidual :
        problem.constraintResidual (selection uStar) = 0 := hresidual
    simpa [PrimalEqualityConstrainedProblem.lagrangian, hselectedResidual, hy'.2] using
      hmin y hy'.1

/-- At a feasible selected minimizer, the equality-constraint term in the selected dual profile
vanishes, so the selected dual profile equals the primal objective. -/
-- Proof sketch: feasibility of `selection u` is equivalent to vanishing constraint residual, and
-- substituting this into the owner Lagrangian formula removes the multiplier term.
theorem selectedDualProfile_eq_objective_of_mem_feasibleSet
    {u : Λ}
    (hfeasible : (selection u : E) ∈ Q₌) :
    φ u = problem (selection u) := by
  have hg :
      g u = 0 :=
    (problem.mem_equalityFeasibleSet_iff_constraintResidual_eq_zero.mp hfeasible).2
  simpa [hg] using selection.selectedDualProfile_eq_objective_add_inner_dualResidual u

section StationaryPoint

variable [CompleteSpace Λ]

/-- Proposition 2.20 in textbook form: if the canonical selected dual profile
`selection.selectedDualProfile` is maximized at `uStar` and has gradient there equal to the
dual residual, then the selected minimizer at `uStar` solves the primal problem. -/
-- Proof sketch: a global maximizer on `Set.univ` is a local maximizer, so Fermat's theorem and
-- the local differentiability packaged by `hprofile_grad` give a zero gradient witness at `uStar`.
-- Uniqueness of gradients identifies `dualResidual selection uStar = 0`, and the core residual
-- theorem then yields feasibility and primal optimality of `selection uStar`.
theorem isMinOn_feasibleSet_of_dualOptimal
    {uStar : Λ}
    (huStar : IsMaxOn φ Set.univ uStar)
    (hprofile_grad : HasGradientAt φ (g uStar) uStar) :
    (selection uStar : E) ∈ Q₌ ∧
      IsMinOn problem Q₌ (selection uStar) := by
  have hlocalMax : IsLocalMax φ uStar := huStar.isLocalMax (by simp)
  have hfderiv := (hasGradientAt_iff_hasFDerivAt.mp hprofile_grad)
  have hfrechet_zero : (InnerProductSpace.toDual ℝ Λ) (g uStar) = 0 :=
    hlocalMax.hasFDerivAt_eq_zero hfderiv
  have hgradient_zero : HasGradientAt φ (0 : Λ) uStar := by
    have hfderiv_zero : HasFDerivAt φ (0 : StrongDual ℝ Λ) uStar := by
      simpa [hfrechet_zero] using hfderiv
    simpa using hfderiv_zero.hasGradientAt
  have hresidual_zero : g uStar = 0 :=
    HasGradientAt.unique hprofile_grad hgradient_zero
  exact selection.isMinOn_feasibleSet_of_dualResidual_eq_zero hresidual_zero

/-- Companion reformulation of Proposition 2.20 using mathlib's total `gradient` at the single
point `uStar`: differentiability at `uStar` upgrades the pointwise identity
`∇ φ(uStar) = selection.dualResidual uStar` to the `HasGradientAt` hypothesis used by the main
theorem. -/
-- Proof sketch: differentiability identifies the total gradient with the unique pointwise
-- gradient, so the assumed gradient identity converts directly into the `HasGradientAt` input of
-- the main proposition.
theorem isMinOn_feasibleSet_of_dualOptimal_of_gradient_eq_dualResidual
    {uStar : Λ}
    (huStar : IsMaxOn φ Set.univ uStar)
    (hprofile_diff : DifferentiableAt ℝ φ uStar)
    (hprofile_grad : ∇ φ uStar = g uStar) :
    (selection uStar : E) ∈ Q₌ ∧
      IsMinOn problem Q₌ (selection uStar) := by
  exact selection.isMinOn_feasibleSet_of_dualOptimal huStar <|
    by simpa [hprofile_grad] using hprofile_diff.hasGradientAt

end StationaryPoint

/-- Once the selected point is known to minimize the primal problem, strong duality identifies the
primal optimal value with the dual value and the recovered primal objective value. -/
-- Proof sketch: from the primal optimality statement, `selection uStar` lies in the feasible set
-- and attains the infimum defining `primalOptimalValue`. The identity
-- `dualFunction_eq_lagrangian selection uStar` rewrites the dual value as the Lagrangian value at
-- `selection uStar`, and feasibility removes the multiplier term, giving the objective value.
theorem primalOptimalValue_eq_dualFunction_eq_objective_of_isMinOn_feasibleSet
    {uStar : Λ}
    (hoptimal :
      (selection uStar : E) ∈ Q₌ ∧
        IsMinOn problem Q₌ (selection uStar)) :
    problem.primalOptimalValue = problem.dualFunction uStar ∧
      problem.dualFunction uStar =
        (problem (selection uStar) : EReal) := by
  have hprimal :
      problem.primalOptimalValue = (problem (selection uStar) : EReal) :=
    problem.primalProblem.optimalValue_eq_of_isMinOn hoptimal.1 hoptimal.2
  have hdual :
      problem.dualFunction uStar = (problem (selection uStar) : EReal) := by
    calc
      problem.dualFunction uStar = (φ uStar : EReal) :=
        selection.dualFunction_eq_selectedDualProfile uStar
      _ = (problem (selection uStar) : EReal) := by
        exact_mod_cast selection.selectedDualProfile_eq_objective_of_mem_feasibleSet hoptimal.1
  constructor
  · rw [hprimal, hdual]
  · exact hdual

end LagrangianMinimizerSelection
end PrimalEqualityConstrainedProblem
