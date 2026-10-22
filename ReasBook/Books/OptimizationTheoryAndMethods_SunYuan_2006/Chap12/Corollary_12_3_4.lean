/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Theorem_12_3_3

noncomputable section

open Filter

section Chapter12Corollary1234

variable {n m : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "Multiplier" => EuclideanSpace ℝ (Fin m)
local notation "∇" => @gradient ℝ Point _ _ _ _

-- Domain-style sampling:
-- * primary domain: Chapter 12 SQP superlinear convergence through the active-constraint
--   Jacobian/projection owners on `StandardPenaltyProblem`;
-- * sampled same-domain owners in the minimal semantic closure:
--   `satisfiesEventualSqpSubproblemAssumption` from `Assumption_12_3_2`,
--   `StandardPenaltyProblem.activeConstraintJacobian`,
--   `StandardPenaltyProblem.activeConstraintNullspaceProjection`, and
--   `sqpProjectedHessianErrorRatio` from `Theorem_12_3_3`;
-- * best owner abstraction: the active-constraint operators are owned by
--   `StandardPenaltyProblem`, while eventual stagewise hypotheses should use the canonical
--   `Filter.atTop` eventuality rather than a new local threshold wrapper;
-- * source/core/bridge triage: the projected stationarity-residual ratio is a source-facing
--   companion for Corollary 12.3.4; the active-set operators remain core owners on
--   `StandardPenaltyProblem`; no extra bridge wrapper is needed here;
-- * primitive data here: `problem`, `xStar`, and the sequences `x`, `d`, `lam`; the assumption
--   package `h1231` is derived theorem input, not owner data for the ratio itself.

/-- The projected stationarity-residual ratio from `(12.3.27)`,
`‖P_k [∇ f(x_k + d_k) - A(x_k + d_k) λ_k]‖ / ‖d_k‖`,
with `P_k = problem.activeConstraintNullspaceProjection (x k) xStar`. -/
def sqpProjectedStationarityResidualRatio
    (problem : StandardPenaltyProblem n m)
    (xStar : Point)
    (x d : ℕ → Point)
    (lam : ℕ → Multiplier) : ℕ → ℝ :=
  fun k ↦
    ‖problem.activeConstraintNullspaceProjection (x k) xStar
        (∇ problem.objective (x k + d k) -
          problem.activeConstraintJacobian (x k + d k) xStar (lam k))‖ /
      ‖d k‖

/-- Unfolding `sqpProjectedStationarityResidualRatio problem xStar x d lam k` gives the
displayed quotient from `(12.3.27)`. -/
theorem sqpProjectedStationarityResidualRatio_apply
    (problem : StandardPenaltyProblem n m)
    (xStar : Point)
    (x d : ℕ → Point)
    (lam : ℕ → Multiplier) (k : ℕ) :
    sqpProjectedStationarityResidualRatio problem xStar x d lam k =
      ‖problem.activeConstraintNullspaceProjection (x k) xStar
          (∇ problem.objective (x k + d k) -
            problem.activeConstraintJacobian (x k + d k) xStar (lam k))‖ /
        ‖d k‖ :=
  rfl

/-- Chapter12 Corollary 12.3.4: under the assumptions of Theorem 12.3.3, if `lam` is the
eventual SQP multiplier sequence satisfying `∀ᶠ k in atTop,
g_k + B_k d_k = A(x_k) λ_k`, then the superlinear step condition `(12.3.11)` is equivalent to
the projected stationarity-residual limit
`(12.3.27)`. -/
theorem hasSuperlinearlyConvergentStep_iff_projectedStationarityResidualRatio_tendsto_zero
    (problem : StandardPenaltyProblem n m)
    (x g d : ℕ → Point)
    (B : ℕ → Point →L[ℝ] Point)
    (lam : ℕ → Multiplier)
    (h1231 : HasSqpSuperlinearConvergenceAssumptions problem x)
    (hAssumption1232 :
      satisfiesEventualSqpSubproblemAssumption
        x
        h1231.xStar
        g
        B
        problem.activeConstraintJacobian
        problem.activeConstraintValues
        d)
    (hLam :
      ∀ᶠ k in atTop,
        g k + B k (d k) =
          problem.activeConstraintJacobian (x k) h1231.xStar (lam k)) :
    HasSuperlinearlyConvergentStep x d h1231.xStar ↔
      Tendsto
        (sqpProjectedStationarityResidualRatio problem h1231.xStar x d lam)
        atTop
        (nhds (0 : ℝ)) := by
  sorry

end Chapter12Corollary1234
