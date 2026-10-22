/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Theorem_9_1_1

noncomputable section

section Chapter09Theorem913

variable {n me mi : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "pointEquiv" => EuclideanSpace.equiv (Fin n) ℝ

-- Domain sampling:
-- * primary domain: quadratic-program local optimality, KKT multipliers, and second-order
--   necessary conditions;
-- * inspected project owners:
--   `QuadraticProgram` from `Definition_9_1_extra_1`,
--   `ConstrainedOptimizationProblem.IsKKTPoint` from `Chapter08.Theorem_8_2_7`,
--   `QuadraticProgram.HasSecondOrderNecessaryCondition` from `Theorem_9_1_1`,
--   and `ConstrainedOptimizationProblem.sequentialNullConstraintDirections` from
--   `Chapter08.Definition_8_3_1`;
-- * best owner abstraction: the matrix-based Chapter 9 owner `QuadraticProgram n me mi`,
--   together with the Chapter 8 KKT owner on `P.toConstrainedOptimizationProblem` and the
--   Chapter 9 second-order owner `P.HasSecondOrderNecessaryCondition`;
-- * source/core/bridge triage:
--   - source-facing item here: Theorem 9.1.3 itself;
--   - core/canonical owners: `P.toConstrainedOptimizationProblem.IsKKTPoint` and
--     `P.HasSecondOrderNecessaryCondition`;
--   - bridge/view: the Euclidean-space transport `pointEquiv`;
-- * primitive data vs derived API:
--   - primitive data already live in the Chapter 9 owner `QuadraticProgram`;
--   - the theorem surface here is derived API over that owner, so the previous duplicate local
--     quadratic-program/KKT/critical-cone packaging is deleted in favor of the canonical owner.

namespace QuadraticProgram

/-- Chapter09 Theorem 9.1.3: for a feasible point `xStar` of the quadratic program `P`,
`xStar` is a local minimizer if and only if there exists a multiplier vector `λ*` such that
`(xStar, λ*)` is a Chapter 8 KKT pair for the constrained-problem bridge of `P` and the
Chapter 9 second-order necessary condition holds on the corresponding null-constraint
directions. -/
theorem isLocalMinOn_iff_exists_isKKTPoint_with_secondOrderNecessaryCondition
    (P : QuadraticProgram n me mi) (xStar : Point)
    (hxStar : xStar ∈ P.feasibleSet) :
    IsLocalMinOn P P.feasibleSet xStar ↔
      ∃ lamStar : Fin (me + mi) → ℝ,
        P.toConstrainedOptimizationProblem.IsKKTPoint (pointEquiv xStar) lamStar ∧
          P.HasSecondOrderNecessaryCondition xStar lamStar := by
  sorry

end QuadraticProgram

end Chapter09Theorem913
