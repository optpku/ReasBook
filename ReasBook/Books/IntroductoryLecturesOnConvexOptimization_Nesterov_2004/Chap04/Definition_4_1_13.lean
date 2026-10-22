/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_14

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open EuclideanSpace

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Definition 4.1.13 lies in the chapter's cubic-regularized Lagrangian-duality domain.

Sampled owner declarations:
* `cubicRegularizedQuadraticScalarLagrangian` in `Theorem_4_1_11`, the existing source-facing
  scalar Lagrangian for the cubic epigraph reformulation;
* `cubicRegularizedQuadraticDualFunction` in `Theorem_4_1_11`, the existing chapter owner of the
  scalar dual function `ψ(λ)`;
* `cubicRegularizedQuadraticEpigraphProblem` in `Definition_4_1_14`, the owner
  `LagrangianProblem` packaging of the same one-constraint epigraph subproblem;
* `LagrangianProblem.dualFunction` in `Chap01/Definition_1_10_2`, the core/canonical dual-value
  owner for finitely constrained Lagrangian problems.

Best owner abstraction:
* source-facing: `cubicRegularizedQuadraticDualFunction g H M`;
* core/canonical:
  `(cubicRegularizedQuadraticEpigraphProblem g H M).dualFunction`;
* bridge/view:
  `cubicRegularizedQuadraticDualFunction_eq_epigraphProblem_dualFunction`.

Primitive data:
* the cubic-regularized epigraph problem data `g`, `H`, and `M`;
* the induced owner problem `cubicRegularizedQuadraticEpigraphProblem g H M`.

Derived API:
* the scalar Lagrangian `cubicRegularizedQuadraticScalarLagrangian`;
* the source-facing scalar dual function `cubicRegularizedQuadraticDualFunction`;
* the canonical `LagrangianProblem.dualFunction` view on the epigraph owner.

Source/core/bridge triage:
* source-facing: the scalar dual function `ψ(λ)` attached to the cubic-regularized quadratic
  subproblem;
* core/canonical: the Chapter 1 owner `LagrangianProblem.dualFunction` on the epigraph problem;
* bridge/view: the specialization theorem below identifying the source-facing scalar owner with
  the generic dual-value owner.

This file therefore deletes the parallel local `...PrimalObjective`, `...Constraint`,
`...Lagrangian`, and `...DualFunction` stack and reuses the established owner declarations
directly. -/

/- The scalar Lagrangian `𝓛(h, τ, λ)` for the cubic-regularized quadratic subproblem is already
the chapter owner `cubicRegularizedQuadraticScalarLagrangian`. -/
recall cubicRegularizedQuadraticScalarLagrangian

/- Definition 4.1.13 is the existing source-facing owner
`cubicRegularizedQuadraticDualFunction`. -/
recall cubicRegularizedQuadraticDualFunction

/- Expanding the source-facing dual function recovers the defining infimum of the scalar
Lagrangian over `(h, τ)`. -/
recall cubicRegularizedQuadraticDualFunction_eq_sInf

/-- The Chapter 4 scalar dual owner is exactly the generic `LagrangianProblem.dualFunction`
specialized to the one-constraint epigraph problem and the scalar multiplier `λ`. -/
theorem cubicRegularizedQuadraticDualFunction_eq_epigraphProblem_dualFunction
    (g : E) (H : Matrix (Fin n) (Fin n) ℝ) (M lam : ℝ) :
    cubicRegularizedQuadraticDualFunction g H M lam =
      (cubicRegularizedQuadraticEpigraphProblem g H M).dualFunction
        (single 0 lam) := by
  rw [LagrangianProblem.dualFunction, SetConstrainedMinimizationProblem.optimalValue,
    cubicRegularizedQuadraticDualFunction]
  congr 1
  ext y
  constructor
  · rintro ⟨x, -, rfl⟩
    refine ⟨x, ?_⟩
    simpa using
      (congrArg (fun t : ℝ ↦ (t : EReal))
        (cubicRegularizedQuadraticEpigraphProblem_lagrangian_eq g H M x.1 x.2 lam)).symm
  · rintro ⟨x, -, rfl⟩
    refine ⟨x, ?_⟩
    simpa using
      congrArg (fun t : ℝ ↦ (t : EReal))
        (cubicRegularizedQuadraticEpigraphProblem_lagrangian_eq g H M x.1 x.2 lam)
