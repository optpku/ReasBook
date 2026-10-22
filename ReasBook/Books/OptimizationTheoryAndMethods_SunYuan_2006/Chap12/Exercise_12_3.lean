/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Corollary_12_3_4

noncomputable section

-- Domain-style sampling pass for this item:
-- * primary domain: Chapter 12 SQP superlinear convergence via the active-constraint Jacobian,
--   nullspace projection, and projected stationarity-residual ratio.
-- * sampled upstream declarations in the minimal semantic closure:
--   - `HasSuperlinearlyConvergentStep` from `Definition_12_3_extra_1`
--   - `satisfiesEventualSqpSubproblemAssumption` from `Assumption_12_3_2`
--   - `StandardPenaltyProblem.activeConstraintJacobian` and
--     `StandardPenaltyProblem.activeConstraintNullspaceProjection` from `Theorem_12_3_3`
--   - `hasSuperlinearlyConvergentStep_iff_projectedStationarityResidualRatio_tendsto_zero`
--     from `Corollary_12_3_4`
-- * best owner abstraction: `StandardPenaltyProblem` owns the active-constraint operators, while
--   the exercise statement itself already lives on the canonical corollary theorem owner.
-- * primitive data vs derived API:
--   - primitive/source-facing data: the Chapter 12 SQP problem data and iterate, step,
--     Hessian-model, and multiplier sequences governed by the upstream assumption packages
--   - derived API: the projected stationarity-residual ratio and its equivalence with
--     superlinear step convergence
-- This file therefore stays at the recall layer and reuses the corollary owner directly instead
-- of keeping a parallel local theorem or local copies of the active-set operators.

-- Source/core/bridge triage:
-- * source-facing recall owner:
--   `hasSuperlinearlyConvergentStep_iff_projectedStationarityResidualRatio_tendsto_zero`
-- * core/canonical owners: `HasSuperlinearlyConvergentStep`,
--   `satisfiesEventualSqpSubproblemAssumption`,
--   `StandardPenaltyProblem.activeConstraintJacobian`, and
--   `StandardPenaltyProblem.activeConstraintNullspaceProjection`
-- * bridge/view: `sqpProjectedStationarityResidualRatio` remains the upstream corollary-level
--   bridge; no extra local bridge/view declaration is needed here.

/- Chapter12 Exercise 12.3 records the same source-facing equivalence as
`hasSuperlinearlyConvergentStep_iff_projectedStationarityResidualRatio_tendsto_zero`,
now reused directly from the canonical Corollary 12.3.4 owner. -/
#check hasSuperlinearlyConvergentStep_iff_projectedStationarityResidualRatio_tendsto_zero
