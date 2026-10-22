/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Theorem_8_2_11

section Chapter08Theorem8212

variable {n m : ℕ} {E I : Set (Fin m)}

local notation "Point" => Fin n → ℝ

-- Domain-style sampling:
-- * primary domain: first-order KKT existence for constrained optimization under LICQ
-- * sampled owner declarations:
--   `ConstrainedOptimizationProblem.LicqAt`
--   `ConstrainedOptimizationProblem.constraintQualificationAt_of_licqAt`
--   `exists_isKKTPoint_of_isLocalMinOn_of_constraintQualificationAt`
-- * source/core/bridge triage:
--   `source-facing`: the LICQ-based multiplier-existence theorem stated here
--   `core/canonical`: `problem.IsKKTPoint xStar lamStar`
--   `bridge/view`: `problem.ConstraintQualificationAt xStar`
-- * primitive data vs derived API:
--   the primitive source hypothesis is `problem.LicqAt xStar`; the constraint qualification is
--   derived bridge data already owned by Theorem 8.2.11, so this file should reuse that bridge
--   instead of re-owning a parallel proof surface

/-- Chapter08 Theorem 8.2.12: under the standing differentiability setup of
Chapter08 Theorem 8.2.7, if `xStar` is a feasible local minimizer of `problem` and LICQ holds at
`xStar`, then there exists a multiplier vector `lamStar` such that
`problem.IsKKTPoint xStar lamStar`. -/
theorem exists_isKKTPoint_of_isLocalMinOn_of_licqAt
    (problem : ConstrainedOptimizationProblem n m E I) (xStar : Point)
    (hxStar : xStar ∈ problem)
    (h_localMin : IsLocalMinOn problem.objective problem.feasibleSet xStar)
    (h_objective : DifferentiableAt ℝ problem.objective xStar)
    (h_constraints : problem.HasConstraintGradientsAt xStar)
    (h_licq : problem.LicqAt xStar) :
    ∃ lamStar : Fin m → ℝ, problem.IsKKTPoint xStar lamStar :=
  exists_isKKTPoint_of_isLocalMinOn_of_constraintQualificationAt problem xStar hxStar
    h_localMin h_objective h_constraints
    (problem.constraintQualificationAt_of_licqAt xStar hxStar h_licq)

end Chapter08Theorem8212
