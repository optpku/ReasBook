/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_30

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

/- Primary domain: equality-constrained Lagrangian duality for the Chapter 2 owner
`PrimalEqualityConstrainedProblem`.

Owner declarations sampled before refining this file:
* `PrimalEqualityConstrainedProblem.lagrangian`, `dualFunction`, `lagrangianMinimizers`, and
  `constraintResidual` in `Nesterov/Chap02/Definition_2_30.lean`;
* `SetConstrainedMinimizationProblem.optimalValue` and `argmin[Q]` in
  `Nesterov/Chap01/Definition_1_3_7.lean`, which already provide the canonical optimal-value and
  minimizer-set owners used upstream in `Definition_2_30`;
* `LagrangianProblem.dualFunction` and `LagrangianProblem.lagrangianMinimizers` in
  `Nesterov/Chap01/Definition_1_10_2.lean`, showing the chapter's owner style for fixed-multiplier
  Lagrangian subproblems.

Best owner abstraction:
* source-facing: the equality-problem dual objective together with the auxiliary minimizing
  section `LagrangianMinimizerSelection problem`;
* core/canonical: the equality-problem owner API from `Definition_2_30`;
* bridge/view: the selected residual and selected dual profile obtained by evaluating the owner
  constructions along a minimizing section.

Primitive data:
* `problem : PrimalEqualityConstrainedProblem E Λ`;
* `selection : ∀ u : Λ, problem.lagrangianMinimizers u`.

Derived API:
* `problem.dualObjective`;
* `selection.dualResidual`;
* `selection.selectedDualProfile`;
* the selected-point specializations of `IsMinOn` and `dualFunction_eq_lagrangian`.

This file keeps the minimizing section only as auxiliary attainment data over the equality-problem
owner. It does not introduce a second primal/dual wrapper or a parallel dual-function owner. -/

namespace PrimalEqualityConstrainedProblem

variable {E : Type u} {Λ : Type v} [AddCommMonoid E] [Module ℝ E]
variable [NormedAddCommGroup Λ] [InnerProductSpace ℝ Λ]

/-- Definition 2.31: the equality-constrained Lagrangian dual objective is the negation of the
source-facing dual function `φ(u) = inf_{x ∈ Q} 𝓛(x, u)` attached to `problem`;
minimizing this function over `u ∈ ℝᵐ` is the textbook dual problem. -/
def dualObjective (problem : PrimalEqualityConstrainedProblem E Λ) : Λ → EReal :=
  -problem.dualFunction

/-- Evaluating the equality-constrained dual objective recovers `-φ(u)`. -/
-- Proof sketch: unfold `dualObjective`; the statement is exactly the defining formula.
@[simp] theorem dualObjective_eq_neg_dualFunction
    (problem : PrimalEqualityConstrainedProblem E Λ) (u : Λ) :
    problem.dualObjective u = -problem.dualFunction u :=
  rfl

/-- A chosen minimizer `x(u) ∈ argmin_{x ∈ Q} 𝓛(x, u)` for each dual multiplier `u`, viewed as
auxiliary attainment data over the equality-constrained problem `problem`. -/
abbrev LagrangianMinimizerSelection (problem : PrimalEqualityConstrainedProblem E Λ) :=
  ∀ u : Λ, problem.lagrangianMinimizers u

namespace LagrangianMinimizerSelection

variable {problem : PrimalEqualityConstrainedProblem E Λ}

/-- The residual `g(u) = b - A x(u)` attached to a chosen Lagrangian minimizer selection. -/
def dualResidual (selection : LagrangianMinimizerSelection problem) (u : Λ) : Λ :=
  problem.constraintResidual (selection u)

/-- The real-valued selected dual profile `u ↦ 𝓛(x(u), u)` attached to a chosen minimizing
selection. -/
def selectedDualProfile (selection : LagrangianMinimizerSelection problem) : Λ → ℝ :=
  fun u ↦ problem.lagrangian (selection u) u

end LagrangianMinimizerSelection

namespace LagrangianMinimizerSelectionNotation

/- Source-facing notation for the selected dual profile `φ(u) = 𝓛(x(u), u)`. -/
scoped notation:max "φ[" selection:arg "]" =>
  PrimalEqualityConstrainedProblem.LagrangianMinimizerSelection.selectedDualProfile selection

/- Pointwise source-facing notation for the selected dual profile `φ(u)`. -/
scoped notation:max "φ[" selection:arg "](" u:arg ")" =>
  PrimalEqualityConstrainedProblem.LagrangianMinimizerSelection.selectedDualProfile selection u

/- Source-facing notation for the selected dual residual `g(u) = b - A x(u)`. -/
scoped notation:max "g[" selection:arg "]" =>
  PrimalEqualityConstrainedProblem.LagrangianMinimizerSelection.dualResidual selection

/- Pointwise source-facing notation for the selected dual residual `g(u)`. -/
scoped notation:max "g[" selection:arg "](" u:arg ")" =>
  PrimalEqualityConstrainedProblem.LagrangianMinimizerSelection.dualResidual selection u

end LagrangianMinimizerSelectionNotation

open scoped LagrangianMinimizerSelectionNotation

namespace LagrangianMinimizerSelection

variable {problem : PrimalEqualityConstrainedProblem E Λ}

/-- Expanding the selected dual profile recovers the primal objective plus the multiplier pairing
with the selected residual. -/
-- Proof sketch: unfold `selectedDualProfile`, `dualResidual`, and `problem.lagrangian`, then use
-- the residual-identification lemma from `Definition_2_30`.
theorem selectedDualProfile_eq_objective_add_inner_dualResidual
    (selection : LagrangianMinimizerSelection problem) (u : Λ) :
    φ[selection](u) = problem (selection u) + inner ℝ u (g[selection](u)) :=
  rfl

/-- The selected point `x(u)` is a global minimizer of the Lagrangian subproblem over `Q`. -/
-- Proof sketch: each `selection u` is by definition a point of
-- `problem.lagrangianMinimizers u`, and the source-facing characterization of that
-- set is exactly `IsMinOn`.
theorem isMinOn (selection : LagrangianMinimizerSelection problem) (u : Λ) :
    IsMinOn
      (fun x ↦ problem.lagrangian x u)
      problem.feasibleSet
      (selection u) := by
  simpa using (problem.mem_lagrangianMinimizers_iff.mp (selection u).2).2

/-- Evaluating the Lagrangian at a selected minimizer realizes the dual function. -/
-- Proof sketch: apply the equality-problem theorem
-- `problem.dualFunction_eq_lagrangian` to the minimizer witness
-- `(selection u).2`.
theorem dualFunction_eq_lagrangian
    (selection : LagrangianMinimizerSelection problem) (u : Λ) :
    problem.dualFunction u = (problem.lagrangian (selection u) u : EReal) :=
  problem.dualFunction_eq_lagrangian (selection u).2

/-- The dual function equals the selected real-valued dual profile attached to a minimizing
selection. -/
-- Proof sketch: expand `selectedDualProfile` and rewrite with
-- `dualFunction_eq_lagrangian`.
theorem dualFunction_eq_selectedDualProfile
    (selection : LagrangianMinimizerSelection problem) (u : Λ) :
    problem.dualFunction u = (φ[selection](u) : EReal) := by
  simpa [selectedDualProfile] using selection.dualFunction_eq_lagrangian u

/-- A minimizing selection realizes the dual objective as the negated selected Lagrangian value.
-/
-- Proof sketch: rewrite the dual function by
-- `dualFunction_eq_selectedDualProfile` and then unfold `problem.dualObjective`.
theorem dualObjective_eq_neg_selectedDualProfile
    (selection : LagrangianMinimizerSelection problem) (u : Λ) :
    problem.dualObjective u = -(φ[selection](u) : EReal) := by
  rw [dualObjective_eq_neg_dualFunction, selection.dualFunction_eq_selectedDualProfile]

end LagrangianMinimizerSelection

end PrimalEqualityConstrainedProblem
