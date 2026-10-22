/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace LagrangianProblem

variable {Q : Type u} {m : ℕ}

local notation "Λ" => EuclideanSpace ℝ (Fin m)

open scoped EuclideanOrthant

/- Definition 3.26 lies in the chapter's Lagrangian-duality API.

Primary domain:
- Lagrangian duality for finitely many inequality constraints.

Sampled owner-style declarations:
- `LagrangianProblem.dualFunction`
- `EuclideanSpace.nonnegativeOrthant`
- `IsMaxOn`
- `isMaxOn_iff`
- `EuclideanSpace.mem_nonnegativeOrthant_iff`

Best owner abstraction:
- `problem : LagrangianProblem Q m`, with a source-facing predicate on a multiplier vector
  `lamStar : Λ`.

Primitive data:
- the owner problem `problem`
- the candidate multiplier `lamStar`

Derived API:
- the dual function `problem.dualFunction`
- nonnegativity via `ℝ₊^m`
- dual optimality on `ℝ₊^m` via `IsMaxOn`
- the coordinatewise textbook spelling via `isOptimalDualMultiplier_iff`

Source/core/bridge triage:
- source-facing: the notion that `lamStar` is a vector of optimal dual multipliers
- core/canonical: membership in the nonnegative orthant together with `IsMaxOn` of the dual
  function on that orthant
- bridge/view: `EuclideanSpace.mem_nonnegativeOrthant_iff` and `isMaxOn_iff`

The source definition is genuinely about a named property of a multiplier vector, so this file
keeps a source-facing predicate instead of only recalling a raw type expression. The earlier
`dualFeasibleSet = dualDomain ∩ ℝ₊ᵐ` packaging is not used in the main owner here because the
textbook definition quantifies over all nonnegative multipliers, not only over those with
`q(λ) > -∞`. -/

/-- Definition 3.26: a vector `λ*` is a vector of optimal dual (Lagrange) multipliers if it is
nonnegative and maximizes the dual function on `ℝ₊^m`. -/
def IsOptimalDualMultiplier (problem : LagrangianProblem Q m) (lamStar : Λ) : Prop :=
  lamStar ∈ ℝ₊^m ∧
    IsMaxOn problem.dualFunction (ℝ₊^m) lamStar

section

variable {problem : LagrangianProblem Q m} {lamStar : Λ}

/-- The source-facing predicate `problem.IsOptimalDualMultiplier lamStar` is equivalent to the
textbook coordinatewise formulation `λ* ≥ 0` and `q(λ*) ≥ q(λ)` for every nonnegative
multiplier `λ`. -/
-- Proof sketch: unfold `LagrangianProblem.IsOptimalDualMultiplier`, rewrite orthant membership
-- by `EuclideanSpace.mem_nonnegativeOrthant_iff` and optimality by `isMaxOn_iff`, then regroup
-- the resulting conjunction and quantifiers.
theorem isOptimalDualMultiplier_iff :
    problem.IsOptimalDualMultiplier lamStar ↔
      (∀ j : Fin m, 0 ≤ lamStar j) ∧
        ∀ lam : Λ, (∀ j : Fin m, 0 ≤ lam j) →
          problem.dualFunction lam ≤ problem.dualFunction lamStar := by
  rw [IsOptimalDualMultiplier, EuclideanSpace.mem_nonnegativeOrthant_iff]
  constructor
  · rintro ⟨hlamStar, hmax⟩
    refine ⟨hlamStar, ?_⟩
    intro lam hlam
    exact (isMaxOn_iff.mp hmax) lam <| by
      simpa [EuclideanSpace.mem_nonnegativeOrthant_iff] using hlam
  · rintro ⟨hlamStar, hmax⟩
    refine ⟨hlamStar, isMaxOn_iff.mpr ?_⟩
    intro lam hlam
    exact hmax lam <| by
      simpa [EuclideanSpace.mem_nonnegativeOrthant_iff] using hlam

end

end LagrangianProblem
