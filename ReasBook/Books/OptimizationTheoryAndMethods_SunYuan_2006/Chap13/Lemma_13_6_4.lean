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
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Exercise_1_5
import OptimizationTheoryAndMethods_SunYuan_2006.Chap13.Algorithm_13_6_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap13.Lemma_13_6_3

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

section

variable {m n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin m)
local notation "Multiplier" => EuclideanSpace ℝ (Fin m)
local notation "Jacobian" => Matrix (Fin n) (Fin m) ℝ
local notation "HessianApproximation" => Matrix (Fin n) (Fin n) ℝ

-- Domain sampling for this refine pass:
-- * primary domain: Chapter 13 Powell-Yuan trust-region stage data on the canonical Euclidean
--   `ℓ2` surface;
-- * sampled owner declarations:
--   `Matrix.pseudoinverse` / `A⁺`,
--   `powellYuanSection13325`,
--   `powellYuanConstraintResidualDecreaseLowerBound`,
--   `IsCdtSolution`,
--   `powellYuanPredictedReduction`,
--   `powellYuanUniformProductBound`;
-- * best owner abstraction: this lemma is the source-facing owner for the explicit Powell-Yuan
--   projector `P̄ = I - A A⁺`, while reusing the canonical pseudoinverse owner `A⁺` together
--   with the source-facing Section 13.3 branch owner `powellYuanSection13325` and the
--   Chapter 13 CDT/algorithm owners for the Step-2 solution predicate, predicted reduction,
--   hat direction, and sequence-level uniform bounds;
--   the later method-level projector in `Theorem_13_6_8` is a bridge/view that specializes to
--   the canonical pseudoinverse `A_k⁺ = (A_k)⁺`.
-- Primitive data vs derived API:
-- * primitive data here: the projector owner `powellYuanProjector`, the shifted gradient owner
--   `powellYuanBarGradient`, the source projected quantity `powellYuanProjectedBarGradient`, and
--   the reduced radius owner `powellYuanReducedTrustRegionRadius`;
-- * derived API reused from upstream: `cdtConstraintResidual`, `cdtObjective`, `IsCdtSolution`,
--   `powellYuanSection13325`, `powellYuanConstraintResidualDecreaseLowerBound`,
--   `powellYuanHatDirection`,
--   `powellYuanSigmaUpdateDenominator`,
--   `powellYuanPredictedReduction`, `powellYuanMultiplierVariationBound`, and
--   `powellYuanUniformProductBound`.

/-- The Powell-Yuan projector `P̄ = I - A A⁺` from `(13.6.17)`. -/
def powellYuanProjector
    (A : Jacobian) : HessianApproximation :=
  (1 : HessianApproximation) - A * A⁺

scoped[PowellYuan1364] notation:max "P̄[" A "]" => powellYuanProjector A

open scoped PowellYuan1364

/-- Unfolding `P̄[A]` gives the source formula `P̄ = I - A A⁺`. -/
theorem powellYuanProjector_eq
    (A : Jacobian) :
    P̄[A] = (1 : HessianApproximation) - A * A⁺ := rfl

/-- The shifted gradient `ḡ_k = g_k + B_k d̂_k` from `(13.6.18)`. -/
def powellYuanBarGradient
    (g : Point) (B : HessianApproximation) (A : Jacobian) (d : Point) : Point :=
  g + Matrix.toEuclideanLin B (powellYuanHatDirection (P̄[A]) d)

scoped[PowellYuan1364] notation:max "ḡ[" g ", " B ", " A ", " d "]" =>
  powellYuanBarGradient g B A d

/-- Unfolding `ḡ[g, B, A, d]` gives the source formula
`ḡ_k = g_k + B_k d̂_k`. -/
theorem powellYuanBarGradient_eq
    (g : Point) (B : HessianApproximation) (A : Jacobian) (d : Point) :
    ḡ[g, B, A, d] =
      g + Matrix.toEuclideanLin B (powellYuanHatDirection (P̄[A]) d) := rfl

/-- The projected shifted gradient `P̄_k ḡ_k` appearing in Lemma 13.6.4. -/
def powellYuanProjectedBarGradient
    (g : Point) (B : HessianApproximation) (A : Jacobian) (d : Point) : Point :=
  Matrix.toEuclideanLin (P̄[A]) (ḡ[g, B, A, d])

scoped[PowellYuan1364] notation:max "P̄ḡ[" g ", " B ", " A ", " d "]" =>
  powellYuanProjectedBarGradient g B A d

/-- Unfolding `P̄ḡ[g, B, A, d]` gives the source quantity `P̄_k ḡ_k`. -/
theorem powellYuanProjectedBarGradient_eq
    (g : Point) (B : HessianApproximation) (A : Jacobian) (d : Point) :
    P̄ḡ[g, B, A, d] =
      Matrix.toEuclideanLin (P̄[A]) (ḡ[g, B, A, d]) := rfl

/-- The reduced trust-region radius `Δ̄_k = sqrt (Δ_k^2 - ‖d̂_k‖₂^2)` from `(13.6.20)`. -/
def powellYuanReducedTrustRegionRadius
    (Δ : ℝ) (A : Jacobian) (d : Point) : ℝ :=
  Real.sqrt (Δ ^ (2 : ℕ) - ‖powellYuanHatDirection (P̄[A]) d‖ ^ (2 : ℕ))

scoped[PowellYuan1364] notation:max "Δ̄[" Δ ", " A ", " d "]" =>
  powellYuanReducedTrustRegionRadius Δ A d

/-- Unfolding `Δ̄[Δ, A, d]` gives the source formula
`Δ̄_k = sqrt (Δ_k^2 - ‖d̂_k‖₂^2)`. -/
theorem powellYuanReducedTrustRegionRadius_eq
    (Δ : ℝ) (A : Jacobian) (d : Point) :
    Δ̄[Δ, A, d] =
      Real.sqrt
        (Δ ^ (2 : ℕ) - ‖powellYuanHatDirection (P̄[A]) d‖ ^ (2 : ℕ)) := rfl

/-- Chapter13 Lemma 13.6.4: there exists a positive constant `δ₁` such that the source
predicted-reduction lower bound holds at every book index `k ≥ 1` for the canonical
Powell-Yuan predicted reduction `powellYuanPredictedReduction` from `(13.6.7)`, written using
the source-facing projector owner `powellYuanProjector`, under the Chapter13 Assumption 13.6.2
stage setup, the source Section 13.3 branch hypothesis together with the Step-2 solution data
that feed Lemma 13.6.3 for the residual-decrease constant `b₂`, and the uniform
multiplier/product bounds used in the proof of the lemma, with the canonical pseudoinverse
owner `A_k⁺ = (A_k)⁺` used directly. -/
theorem powellYuanPredictedReductionLowerBound
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
          powellYuanSection13325 (c k) (jacobian (x k)) (Δ k) ξk b2)
    (h_multiplierVariation : powellYuanMultiplierVariationBound lam lamTrial d)
    (h_uniformProduct : powellYuanUniformProductBound (jacobian ∘ x) B) :
    ∃ delta1 : ℝ, 0 < delta1 ∧
      ∀ k : ℕ, 1 ≤ k →
        (1 / 4 : ℝ) *
              ‖P̄ḡ[g k, B k, jacobian (x k), d k]‖ *
              min
                (Δ̄[Δ k, jacobian (x k), d k])
                (‖P̄ḡ[g k, B k, jacobian (x k), d k]‖ /
                  (2 * ‖B k‖)) +
            (sigma k / 2 : ℝ) * ‖c k‖ * min ‖c k‖ ((b2 * Δ k) / ‖(jacobian (x k))⁺‖) ≤
          (powellYuanPredictedReduction
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
                (d k))) -
            (sigma k / 2 : ℝ) *
              powellYuanSigmaUpdateDenominator
                (c k)
                (jacobian (x k))
                (d k) +
            delta1 * ‖d k‖ * ‖c k‖ := sorry

#print axioms powellYuanHatDirection
#print axioms powellYuanBarGradient
#print axioms powellYuanProjectedBarGradient
#print axioms cdtObjective
#print axioms IsCdtSolution
#print axioms powellYuanPredictedReduction
#print axioms powellYuanMultiplierVariationBound
#print axioms powellYuanUniformProductBound
#print axioms powellYuanReducedTrustRegionRadius
#print axioms powellYuanPredictedReductionLowerBound
#print axioms PowellYuanAssumption1362

end
