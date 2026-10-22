/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_20

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient SeminormDualNorm
open scoped PrimalEqualityConstrainedProblem.LagrangianMinimizerSelectionNotation

noncomputable section

universe u v

/- Primary domain: equality-constrained Lagrangian duality with a chosen minimizing primal
selection.

Owner declarations sampled before refining this file:
* `PrimalEqualityConstrainedProblem.constraintResidual` and
  `PrimalEqualityConstrainedProblem.dualFunction` in `Definition_2_30.lean`;
* `PrimalEqualityConstrainedProblem.LagrangianMinimizerSelection`,
  `LagrangianMinimizerSelection.selectedDualProfile`, `dualResidual`, and `isMinOn` in
  `Definition_2_31.lean`;
* `LagrangianMinimizerSelection.isMinOn_feasibleSet_of_dualOptimal` in `Proposition_2_20.lean`,
  the owner theorem turning dual optimality into primal optimality for the selected point;
* `Seminorm.inner_le_dualNorm_mul` in `Proposition_2_1.lean`, the dual Cauchy--Schwarz estimate
  used to bound the objective gap.

Best owner abstraction: the equality problem's own Lagrangian layer with
`selection : PrimalEqualityConstrainedProblem.LagrangianMinimizerSelection problem`.
The selected dual profile `selectedDualProfile selection` and residual `dualResidual selection`
are derived owner API, not primitive public data.

Primitive data:
* the equality-constrained problem `problem`;
* a minimizing selection `selection`;
* a seminorm `d` on the multiplier space.

Derived API:
* the selected dual profile;
* the selected dual residual;
* the primal optimality of `selection uStar` obtained from owner dual optimality;
* dual-norm bounds via `dualNorm d`.

Source/core/bridge triage:
* source-facing: Proposition 2.21's infeasibility and primal-gap estimate for a selected
  equality-constrained dual profile;
* core/canonical: the owner selected profile and residual on
  `PrimalEqualityConstrainedProblem.LagrangianMinimizerSelection`;
* bridge/view: the coordinate formula `b - A x(u)` for the same residual, which remains available
  through `problem.constraintResidual (selection u)`.
-/

namespace PrimalEqualityConstrainedProblem
namespace LagrangianMinimizerSelection

variable {E : Type u} {Λ : Type v} [AddCommMonoid E] [Module ℝ E]
variable [NormedAddCommGroup Λ] [InnerProductSpace ℝ Λ]
variable [FiniteDimensional ℝ Λ]
variable {problem : PrimalEqualityConstrainedProblem E Λ}

variable (selection : LagrangianMinimizerSelection problem)

local notation "Q₌" => problem.equalityFeasibleSet
local notation "φ" => φ[selection]
local notation "g" => g[selection]

/-- Proposition 2.21 in owner form: if the selected dual profile `φ(u) = 𝓛(x(u), u)` has
pointwise gradient `g(u) = b - A x(u)` at the optimal multiplier `uStar` and at the comparison
point `uBar`, and `uStar` is a global maximizer of `φ`, then the dual norm of the infeasibility
at `uBar` equals the dual norm of `∇ φ(uBar)`, and the primal suboptimality of `x(uBar)` relative
to the optimal selected point `x(uStar)` is bounded by `‖uBar‖_d ‖∇ φ(uBar)‖_{d,*}`. -/
-- Proof sketch: `hprofile_grad_bar.gradient` identifies the owner residual `g uBar` with the
-- actual gradient at `uBar`, giving the infeasibility norm identity. Proposition 2.20 upgrades
-- `huStar` and the pointwise gradient witness `hprofile_grad_star` at `uStar` to primal
-- optimality of `selection uStar`; this identifies `φ(uStar)` with `problem (selection uStar)`.
-- Maximality gives `φ(uBar) ≤ φ(uStar)`, expanding
-- `φ(uBar) = problem (selection uBar) + ⟪uBar, selection.dualResidual uBar⟫`; the remaining
-- pairing is bounded by `Seminorm.inner_le_dualNorm_mul`.
theorem dual_gradient_bounds_infeasibility_and_suboptimality
    (d : Seminorm ℝ Λ) [Seminorm.IsNorm d]
    {uStar uBar : Λ}
    (hprofile_grad_star : HasGradientAt φ (g uStar) uStar)
    (hprofile_grad_bar : HasGradientAt φ (g uBar) uBar)
    (huStar : IsMaxOn φ Set.univ uStar) :
    ‖g uBar‖[d,*] = ‖∇ φ uBar‖[d,*] ∧
      problem (selection uBar) - problem (selection uStar) ≤
        d uBar * ‖∇ φ uBar‖[d,*] := by
  have hoptimal :=
    selection.isMinOn_feasibleSet_of_dualOptimal huStar hprofile_grad_star
  have hselected_star : φ uStar = problem (selection uStar) :=
    selection.selectedDualProfile_eq_objective_of_mem_feasibleSet hoptimal.1
  have hprofile_le :
      problem (selection uBar) + inner ℝ uBar (g uBar) ≤ problem (selection uStar) := by
    calc
      problem (selection uBar) + inner ℝ uBar (g uBar) = φ uBar := by
        symm
        exact selection.selectedDualProfile_eq_objective_add_inner_dualResidual uBar
      _ ≤ φ uStar := by
        simpa using (isMaxOn_univ_iff.mp huStar) uBar
      _ = problem (selection uStar) := hselected_star
  have hgap :
      problem (selection uBar) - problem (selection uStar) ≤ -inner ℝ uBar (g uBar) := by
    linarith
  have hpair :
      -inner ℝ uBar (g uBar) ≤ d uBar * ‖g uBar‖[d,*] := by
    simpa [real_inner_comm, mul_comm] using
      (Seminorm.inner_le_dualNorm_mul d (-uBar) (g uBar))
  constructor
  · simp [hprofile_grad_bar.gradient]
  · calc
      problem (selection uBar) - problem (selection uStar) ≤ -inner ℝ uBar (g uBar) :=
        hgap
      _ ≤ d uBar * ‖g uBar‖[d,*] := hpair
      _ = d uBar * ‖∇ φ uBar‖[d,*] := by
        rw [hprofile_grad_bar.gradient]

end LagrangianMinimizerSelection
end PrimalEqualityConstrainedProblem
