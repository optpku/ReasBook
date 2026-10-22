/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Data.Finset.Max
import OptimizationTheoryAndMethods_SunYuan_2006.Chap13.Algorithm_13_4_1

noncomputable section

section

open scoped Matrix.Norms.L2Operator

variable {ambientDim constraintDim tangentDim : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin ambientDim)

namespace NullSpaceTrustRegionMethod

/-- The source denominator `M_k = max_{1 ≤ i ≤ k} ‖B_i‖₂ + 1` from `(13.4.41)`, encoded on
book indices `k = 1, 2, 3, ...` by taking the supremum over `Finset.Icc 0 k` and assigning the
dummy index `0` the value `0`. -/
def hessianNormEnvelope
    (method : NullSpaceTrustRegionMethod ambientDim constraintDim tangentDim)
    (k : ℕ) : ℝ :=
  (Finset.Icc 0 k).sup' (Finset.nonempty_Icc.mpr (Nat.zero_le k))
      (fun i ↦ if i = 0 then 0 else ‖method.hessianApproximation i‖₂) + 1

/-- Unfolding `method.hessianNormEnvelope k` gives the source denominator `(13.4.41)`. -/
theorem hessianNormEnvelope_eq
    (method : NullSpaceTrustRegionMethod ambientDim constraintDim tangentDim)
    (k : ℕ) :
    method.hessianNormEnvelope k =
      (Finset.Icc 0 k).sup' (Finset.nonempty_Icc.mpr (Nat.zero_le k))
          (fun i ↦ if i = 0 then 0 else ‖method.hessianApproximation i‖₂) + 1 :=
  rfl

#print axioms NullSpaceTrustRegionMethod.hessianNormEnvelope

/-- Chapter13 Lemma 13.4.3: assume `f : Point → ℝ` is `C²`, the recorded gradient map
`method.gradientAt` agrees with `gradient f`, the recorded constraint map
`method.constraintResidualAt` is `C²` with Jacobian `method.constraintJacobianAt`, fix a
uniform bound `aBound` for the stagewise Jacobian norms `‖A_k‖₂`, and fix `δ > 0` such that
`δ ≤ ‖c_k‖₂ + ‖Z_kᵀ g_k‖₂` at every book index `k ≥ 1` where the Step-2 stopping test fails.
Then there exists `β₅ > 0` such that `β₅ / M_k ≤ ‖d_k‖₂` for all such `k ≥ 1`, where
`M_k = method.hessianNormEnvelope k = max_{1 ≤ i ≤ k} ‖B_i‖₂ + 1`. -/
theorem exists_trialStepNormLowerBound
    (f : Point → ℝ)
    (method : NullSpaceTrustRegionMethod ambientDim constraintDim tangentDim)
    (h_objective_contDiff : ContDiff ℝ 2 f)
    (h_gradient_eq : ∀ x : Point, _root_.gradient f x = method.gradientAt x)
    (h_constraint_contDiff : ContDiff ℝ 2 method.constraintResidualAt)
    (h_constraintJacobian_is_fderiv :
      ∀ x : Point,
        fderiv ℝ method.constraintResidualAt x =
          (Matrix.toEuclideanLin (method.constraintJacobianAt x).transpose).toContinuousLinearMap)
    (aBound : ℝ)
    (hA_bounded : ∀ k : ℕ, 1 ≤ k → ‖method.constraintJacobian k‖₂ ≤ aBound)
    (δ : ℝ)
    (hδ_pos : 0 < δ)
    (h_residual_lb :
      ∀ k : ℕ, 1 ≤ k →
        ¬ method.terminatedAt k →
        δ ≤
          nullSpaceStoppingResidual
            (method.constraintResidual k)
            (method.nullSpaceBasis k)
            (method.gradient k)) :
    ∃ β₅ : ℝ, 0 < β₅ ∧
      ∀ k : ℕ, 1 ≤ k → ¬ method.terminatedAt k →
        β₅ / method.hessianNormEnvelope k ≤ ‖method.trialStep k‖ := by
  sorry

end NullSpaceTrustRegionMethod

end
