/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Theorem_9_2_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Theorem_9_2_3

noncomputable section

namespace QuadraticProgram

-- Domain-style sampling in Chapter 9:
-- * core/canonical owner: `QuadraticProgram` from `Definition_9_1_extra_1`
-- * derived dual API: `DualVariable`, `SatisfiesDualStationarity`, `dualObjective`, and
--   `IsDualFeasible` from
--   `Theorem_9_2_1`
-- * bridge/view here: Exercise 9.3 identifies that explicit dual objective with the infimum of
--   the canonical quadratic-program Lagrangian from `Theorem_9_2_3`
--
-- Primitive data stay upstream in the chapter owner. This file contributes only the source-facing
-- bridge theorem.

variable {n me mi : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

open scoped QuadraticProgram

/-- Chapter09 Exercise 9.3: when `P.G` is positive definite, the explicit dual objective from
`(9.2.8)` equals the infimum over `x : ℝ^n` of the Chapter 9 quadratic-program Lagrangian with
the multiplier pair `(dual.eqMultiplier, dual.ineqMultiplier)` for every dual variable `dual`
satisfying the stationarity relation `(9.2.9)`. The inequality-multiplier nonnegativity from
`(9.2.10)` is irrelevant for this identity and is recovered later by passing to a dual-feasible
variable. This is the source bridge identifying the explicit dual objective formula with the
Lagrangian dual of `(9.1.1)`-`(9.1.3)`. -/
theorem dualObjective_eq_sInf_lagrangian_of_stationarity
    (P : QuadraticProgram n me mi) (hG : P.G.PosDef) (dual : DualVariable P)
    (hstationarity : P.SatisfiesDualStationarity dual) :
    P.dualObjective hG dual =
      sInf (Set.range fun x : Point ↦ ℒ[P] x (dual.eqMultiplier, dual.ineqMultiplier)) := sorry

end QuadraticProgram
