/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Exercise_9_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Problem_9_3_extra_1

noncomputable section

open Matrix

section

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin m)

-- Domain-style sampling for this file:
-- * primary domain: equality-constrained quadratic-program duality.
-- * inspected owner declarations:
--   - `EqualityConstrainedQuadraticProgram.toQuadraticProgram` and
--     `EqualityConstrainedQuadraticProgram.toDualVariable` from
--     `Problem_9_3_extra_1`;
--   - `QuadraticProgram.DualVariable`, `QuadraticProgram.dualObjective`, and
--     `QuadraticProgram.SatisfiesDualStationarity` from `Theorem_9_2_1`;
--   - `QuadraticProgram.dualObjective_eq_sInf_lagrangian_of_stationarity` from `Exercise_9_3`.
-- * source/core/bridge triage:
--   - source-facing layer here: the Exercise 9.7 equality-multiplier formula;
--   - core/canonical layer: `QuadraticProgram` together with its dual-variable owner;
--   - bridge/view layer: `problem.toDualVariable λ`, converting an equality multiplier `λ` to
--     the canonical dual variable of the associated quadratic program.
-- * primitive data vs. derived API:
--   - primitive data remain owned by `EqualityConstrainedQuadraticProgram`;
--   - this file contributes only the canonical bridge from `λ` to the upstream dual owner and
--     the positive-definite theorem identifying the source formula with the Lagrangian dual
--     value.

namespace EqualityConstrainedQuadraticProgram

open scoped QuadraticProgram

/-- Exercise 9.7: if the Hessian `B = problem.G` is positive definite, then the source explicit
dual expression
`λ ↦ bᵀ λ - (1 / 2) * (A λ - g)ᵀ B⁻¹ (A λ - g)`
is exactly the infimum over `x : ℝ^n` of the canonical Chapter 9 Lagrangian
`ℒ[problem.toQuadraticProgram] x (λ, 0)`. This is the source-faithful bridge from the equality-
constrained textbook dual formula to the existing Chapter 9 dual owner. -/
theorem dualObjective_eq_sInf_lagrangian
    (problem : EqualityConstrainedQuadraticProgram n m) (hG : problem.G.PosDef)
    (lam : ConstraintPoint) :
    dotProduct problem.b lam - (1 / 2 : ℝ) *
        dotProduct (WithLp.toLp 2 (problem.A.mulVec lam.ofLp) - problem.g)
          (WithLp.toLp 2
            (problem.G⁻¹.mulVec (WithLp.toLp 2 (problem.A.mulVec lam.ofLp) - problem.g).ofLp)) =
      sInf (Set.range fun x : Point ↦ ℒ[problem.toQuadraticProgram] x (lam, 0)) := by
  letI : Invertible problem.G := hG.isUnit.invertible
  simpa [EqualityConstrainedQuadraticProgram.toDualVariable,
    EqualityConstrainedQuadraticProgram.toQuadraticProgram,
    QuadraticProgram.dualObjective, Matrix.invOf_eq_nonsing_inv]
    using
      QuadraticProgram.dualObjective_eq_sInf_lagrangian_of_stationarity
        problem.toQuadraticProgram hG (problem.toDualVariable lam)
        (problem.satisfiesDualStationarity_toDualVariable lam)

end EqualityConstrainedQuadraticProgram

end
