/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import OptimizationTheoryAndMethods_SunYuan_2006.Chap13.Lemma_13_6_4

noncomputable section

open scoped Matrix.Norms.L2Operator PowellYuan1364

section

variable {m n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin m)
local notation "Multiplier" => EuclideanSpace ℝ (Fin m)
local notation "Jacobian" => Matrix (Fin n) (Fin m) ℝ
local notation "HessianApproximation" => Matrix (Fin n) (Fin n) ℝ

-- Domain sampling for this refine pass:
-- * primary domain: the Chapter 13 sequence-level corollary layer built on the
--   `powellYuanPredictedReductionLowerBound` machinery from Lemma 13.6.4;
-- * inspected owner declarations:
--   `powellYuanSection13325` from `Lemma_13_6_3`,
--   `IsCdtSolution` and `cdtConstraintResidual` from `Theorem_13_5_1`,
--   `powellYuanSigmaUpdateDenominator` and `powellYuanPredictedReduction` from
--   `Algorithm_13_6_1`,
--   `powellYuanPredictedReductionLowerBound` together with the projector/radius owners from
--   `Lemma_13_6_4`,
--   and the later downstream bridge `PowellYuanCorollary1365Regime` from `Lemma_13_6_6`;
-- * source/core/bridge triage:
--   - source-facing: the corollary's direct existential lower-bound statement
--   - core/canonical: the CDT residual owner and Step-3 denominator/predicted-reduction owners
--   - bridge/view: the later regime packaging in `Lemma_13_6_6`, which adds eventual-smallness
--     data not present in Corollary 13.6.5 itself;
-- * primitive data vs derived API:
--   - primitive data here: the source constant `b₂` and the Section 13.3 branch hypothesis
--     `powellYuanSection13325` attached to the Step-2 solution witness `ξ_k`
--   - derived API: the owner theorem `powellYuanPredictedReductionLowerBound`, whose full
--     hypothesis shape this corollary should reuse rather than weakening into a parallel local
--     surrogate.

/-- Chapter13 Corollary 13.6.5: under the standing Chapter13 Assumption 13.6.2 stage setup plus
the Lemma 13.6.4 residual-decrease source data with the explicit constant `b₂ ≥ 0`, the
Section 13.3 branch hypothesis `(13.3.25)`, the multiplier-variation bound, and the canonical
pseudoinverse-product bound, there is a positive threshold `δ₃` with a positive constant `δ₄`
such that every stage satisfying `(13.6.31)` at a book index `k ≥ 1` also satisfies `(13.6.32)`,
written directly on the canonical Step-3 denominator owner
`powellYuanSigmaUpdateDenominator` and the stage predicted-reduction owner
`powellYuanPredictedReduction`. -/
theorem powellYuanPredictedReductionLowerBound_of_smallConstraintResidual
    (sigma : ℕ → ℝ)
    (c : ℕ → ConstraintPoint)
    (jacobian : Point → Jacobian)
    (x d : ℕ → Point)
    (g : ℕ → Point)
    (lam lamTrial : ℕ → Multiplier)
    (B : ℕ → HessianApproximation)
    (Δ : ℕ → ℝ)
    (b2 : ℝ)
    (h1362 : PowellYuanAssumption1362 x d jacobian B)
    (h_b2 : 0 ≤ b2)
    (h_sigma : ∀ k : ℕ, 1 ≤ k → 0 ≤ sigma k)
    (h_residualDecreaseSource :
      ∀ k : ℕ, 1 ≤ k →
        ∃ ξk : ℝ,
          IsCdtSolution
            (B k)
            (g k)
            (jacobian (x k))
            (c k)
            (Δ k)
            ξk
            (d k) ∧
          powellYuanSection13325
            (c k)
            (jacobian (x k))
            (Δ k)
            ξk
            b2)
    (h_multiplierVariation : powellYuanMultiplierVariationBound lam lamTrial d)
    (h_uniformProduct : powellYuanUniformProductBound (jacobian ∘ x) B) :
    ∃ delta3 : ℝ,
      0 < delta3 ∧
        ∃ delta4 : ℝ,
          0 < delta4 ∧
            ∀ k : ℕ, 1 ≤ k →
              ‖c k‖ ≤ delta3 * Δ k →
                (sigma k / 2 : ℝ) *
                    powellYuanSigmaUpdateDenominator
                      (c k)
                      (jacobian (x k))
                      (d k) +
                  delta4 * Δ k ≤
                    powellYuanPredictedReduction
                      (g k)
                      (B k)
                      (jacobian (x k))
                      (c k)
                      (lam k)
                      (lamTrial k)
                      (sigma k)
                      (d k)
                      (powellYuanHatDirection
                        (P̄[jacobian (x k)])
                        (d k)) := sorry

#print axioms PowellYuanAssumption1362
#print axioms powellYuanHatDirection
#print axioms powellYuanBarGradient
#print axioms powellYuanProjectedBarGradient
#print axioms cdtObjective
#print axioms powellYuanPredictedReduction
#print axioms powellYuanReducedTrustRegionRadius

end
