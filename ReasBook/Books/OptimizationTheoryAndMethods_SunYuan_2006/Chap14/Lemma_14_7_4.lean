/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.CStarAlgebra.Matrix
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Algorithm_14_7_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Lemma_14_6_2

noncomputable section

open scoped Matrix.Norms.L2Operator

section

variable {n m : ℕ}
variable {ρ : (Fin n → ℝ) → ℝ} [IsVectorNorm ρ]

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ValuePoint" => EuclideanSpace ℝ (Fin m)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

section

variable (problem : CompositeNonsmoothOptimizationProblem n m)
variable (xk dk : Point) (Bk : MatrixN) (Δk : ℝ)

local notation "ψₖ" => compositeNonsmoothPsi problem.outerFunction problem.smoothMap Δk xk

-- Domain sampling:
-- * primary domain: Chapter 14's composite nonsmooth trust-region model and its predicted
--   reduction bound;
-- * core/canonical owners inspected upstream:
--   `compositeNonsmoothTrustRegionModel`,
--   `IsCompositeNonsmoothTrustRegionSolution` from `Algorithm_14_7_1`,
--   `compositeNonsmoothPsi` from `Lemma_14_6_2`,
--   and the Section 14.6 Jacobian owner `compositeNonsmoothJacobianTranspose` from
--   `Lemma_14_6_1`;
-- * layer triage for this file: the theorem remains source-facing, while its inputs now reuse the
--   existing chapter owners instead of redeclaring parallel local wrappers.

/-- Chapter14 Lemma 14.7.4: if `dk` solves the composite nonsmooth trust-region subproblem
`(14.7.1)`-`(14.7.2)` built from the canonical Jacobian transpose `A(x) = ∇ f(x)ᵀ`, then the
canonical predicted reduction `φ_k(0) - φ_k(dk)` is bounded below by the standard trust-region
expression involving `ψ_(Δ_k)(x_k)`. To avoid Lean's `/ 0 = 0` convention from silently weakening
the source formula when `‖Bk‖ = 0`, the zero-operator-norm case is stated explicitly. -/
theorem compositeNonsmoothTrustRegionPredictedReductionLowerBound
    (hdk : IsCompositeNonsmoothTrustRegionSolution
      ρ
      problem
      xk
      Bk
      Δk
      dk) :
    trustRegionPredictedReduction
        (compositeNonsmoothTrustRegionModel
          problem
          xk
          Bk)
        dk ≥
      if ‖Bk‖ = 0 then
        (1 / 2 : ℝ) * ψₖ
      else
        (1 / 2 : ℝ) * ψₖ * min (1 : ℝ) (ψₖ / (‖Bk‖ * Δk ^ 2)) := sorry

end

end
