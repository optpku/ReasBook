/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_31

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

open scoped PrimalEqualityConstrainedProblem.LagrangianMinimizerSelectionNotation

/- Primary domain: equality-constrained Lagrangian duality with a chosen minimizing primal
selection.

Owner declarations sampled before refining this file:
* `PrimalEqualityConstrainedProblem.lagrangian`, `lagrangianMinimizers`, and
  `constraintResidual` in `Nesterov/Chap02/Definition_2_30.lean`;
* `PrimalEqualityConstrainedProblem.LagrangianMinimizerSelection.isMinOn` in
  `Nesterov/Chap02/Definition_2_31.lean`, the owner theorem expressing that a chosen section
  minimizes each fixed-multiplier Lagrangian subproblem;
* `PrimalEqualityConstrainedProblem.LagrangianMinimizerSelection.
  selectedDualProfile_eq_objective_add_inner_dualResidual` in
  `Nesterov/Chap02/Definition_2_31.lean`, the canonical expansion of the selected profile.

Best owner abstraction: the equality problem's own Lagrangian layer, with
`selection : LagrangianMinimizerSelection problem` as the source-facing auxiliary choice data.

Primitive data:
* `problem`, `selection`, and the multipliers `u₁`, `u₂`.

Derived API:
* `selection.isMinOn u`;
* `selection.dualResidual`;
* `selection.selectedDualProfile_eq_objective_add_inner_dualResidual`.

Source/core/bridge triage:
* source-facing: Proposition 2.19 as the affine support inequality for the selected dual profile
  `u ↦ 𝓛(x(u), u)`;
* core/canonical: the equality-problem minimizing-section owner `selection.isMinOn`;
* bridge/view: rewriting the comparison bound through
  `selectedDualProfile_eq_objective_add_inner_dualResidual`.

No parallel local dual-function wrapper is kept here; this file stays as a thin source-facing
bridge to the equality-problem minimizing-section API. -/

namespace PrimalEqualityConstrainedProblem
namespace LagrangianMinimizerSelection

variable {E : Type u} {Λ : Type v} [AddCommMonoid E] [Module ℝ E]
variable [NormedAddCommGroup Λ] [InnerProductSpace ℝ Λ]
variable {problem : PrimalEqualityConstrainedProblem E Λ}

variable (selection : LagrangianMinimizerSelection problem)

local notation "φ" => φ[selection]
local notation "g" => g[selection]

/-- Proposition 2.19: for a chosen minimizer `x(u) ∈ argmin_x 𝓛(x, u)` of each equality-
constrained Lagrangian subproblem, the selected dual profile `u ↦ 𝓛(x(u), u)` satisfies the
affine support inequality `φ(u₁) ≤ φ(u₂) + ⟪u₁ - u₂, g(u₂)⟫`, where `g(u) = b - A x(u)`. -/
-- Proof sketch: evaluate the owner theorem `selection.isMinOn u₁` at the feasible comparison
-- point `selection u₂`, then expand the resulting `u₁`-Lagrangian value into the selected
-- profile at `u₂` plus the affine residual term.
theorem selectedDualProfile_le_affine_support
    (u₁ u₂ : Λ) :
    φ u₁ ≤ φ u₂ + inner ℝ (u₁ - u₂) (g u₂) := by
  have hu₂_mem : (selection u₂ : E) ∈ problem.feasibleSet :=
    (problem.mem_lagrangianMinimizers_iff.mp (selection u₂).2).1
  have hmin := selection.isMinOn u₁
  rw [isMinOn_iff] at hmin
  have hcompare :
      φ u₁ ≤ problem.lagrangian (selection u₂) u₁ := by
    simpa [selectedDualProfile] using hmin (selection u₂) hu₂_mem
  calc
    φ u₁ ≤ problem.lagrangian (selection u₂) u₁ := hcompare
    _ = problem (selection u₂) + inner ℝ u₁ (g u₂) := rfl
    _ = problem (selection u₂) + (inner ℝ u₂ (g u₂) + inner ℝ (u₁ - u₂) (g u₂)) := by
          congr 1
          calc
            inner ℝ u₁ (g u₂) = inner ℝ (u₂ + (u₁ - u₂)) (g u₂) := by
                    congr 1
                    abel
            _ = inner ℝ u₂ (g u₂) + inner ℝ (u₁ - u₂) (g u₂) := by
                    rw [inner_add_left]
    _ = (problem (selection u₂) + inner ℝ u₂ (g u₂)) + inner ℝ (u₁ - u₂) (g u₂) := by
          abel
    _ = φ u₂ + inner ℝ (u₁ - u₂) (g u₂) := by
          rw [← selection.selectedDualProfile_eq_objective_add_inner_dualResidual u₂]

end LagrangianMinimizerSelection
end PrimalEqualityConstrainedProblem
