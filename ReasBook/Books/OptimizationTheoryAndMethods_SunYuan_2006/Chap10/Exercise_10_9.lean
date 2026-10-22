/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Definition_10_5_extra_1

noncomputable section

-- Domain-style sampling pass for this item:
-- * primary domain: Chapter 10 equality-constrained smooth exact penalty functions.
-- * sampled upstream declarations in the minimal semantic closure:
--   - `isChosenPseudoInverseAt` from `ChosenPseudoInverse`
--   - `constraintJacobian`
--   - `isConstraintJacobianPseudoInverseField`
--   - `fletcherMultiplierEstimate1023`
--   - `fletcherSimpleSmoothExactPenaltyFunction`
--   - `norm_constraint_le_of_isMinOn_fletcherSimpleSmoothExactPenaltyFunction`
-- * best owner abstraction: the Chapter 10 source-facing smooth exact penalty API already owned
--   by `Definition_10_5_extra_1`, with Exercise 10.9 itself living at the recall layer.
-- * primitive data vs derived API:
--   - primitive/source-facing data: the Jacobian field, chosen pseudoinverse field, multiplier
--     estimate, and Fletcher penalty surface;
--   - derived API: the monotonicity theorem for minimizers of the simple smooth exact penalty
--     subproblems.
-- This file therefore deletes the duplicate local wheel and reuses the existing theorem owner
-- directly.

-- Source/core/bridge triage:
-- * source-facing theorem owner:
--   `norm_constraint_le_of_isMinOn_fletcherSimpleSmoothExactPenaltyFunction`
-- * core/canonical support owners: `isChosenPseudoInverseAt`,
--   `isConstraintJacobianPseudoInverseField`, and `fletcherSimpleSmoothExactPenaltyFunction`
-- * bridge/view: none; the exercise is an exact recall of the upstream Chapter 10 theorem.

/- Chapter10 Exercise 10.9: direct recall of the Chapter 10 theorem stating that if `x σ`
globally minimizes Fletcher's simple smooth exact penalty subproblem `(10.5.5)` for each positive
penalty parameter `σ`, then the constraint residual norm is antitone in `σ`. -/
#check norm_constraint_le_of_isMinOn_fletcherSimpleSmoothExactPenaltyFunction
