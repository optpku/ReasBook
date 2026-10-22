/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Exercise_1_5
import OptimizationTheoryAndMethods_SunYuan_2006.Chap13.Assumption_13_6_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap13.Theorem_13_5_1

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

variable {m n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin m)
local notation "Multiplier" => EuclideanSpace ℝ (Fin m)
local notation "Jacobian" => Matrix (Fin n) (Fin m) ℝ
local notation "HessianApproximation" => Matrix (Fin n) (Fin n) ℝ

-- Semantic recall: Chapter 13 already uses `cdtConstraintResidual`, `cdtObjective`,
-- `cdtFeasibleSet`, and `IsCdtSolution` as the owner layer for the CDT subproblem. This file
-- keeps only the Powell-Yuan-specific residual, penalty, reduction, and update data explicit,
-- and reuses that earlier CDT owner for Step 2.

/-- The Step-2 stopping residual is `‖c_k‖ + ‖g_k - A_k λ_k‖`. -/
def powellYuanStoppingResidual
    (c : ConstraintPoint) (g : Point) (A : Jacobian) (lam : Multiplier) : ℝ :=
  ‖c‖ + ‖g - Matrix.toEuclideanLin A lam‖

/-- Unfolding `powellYuanStoppingResidual c g A lam` gives the source Step-2 residual
`‖c‖ + ‖g - A λ‖`. -/
theorem powellYuanStoppingResidual_eq
    (c : ConstraintPoint) (g : Point) (A : Jacobian) (lam : Multiplier) :
    powellYuanStoppingResidual c g A lam = ‖c‖ + ‖g - Matrix.toEuclideanLin A lam‖ := rfl

/-- The source Step-2 stopping test terminates once `powellYuanStoppingResidual c g A lam ≤ ε`. -/
def powellYuanTerminated
    (ε : ℝ) (c : ConstraintPoint) (g : Point) (A : Jacobian) (lam : Multiplier) : Prop :=
  powellYuanStoppingResidual c g A lam ≤ ε

/-- Unfolding `powellYuanTerminated ε c g A lam` gives the Step-2 stopping inequality. -/
theorem powellYuanTerminated_iff
    (ε : ℝ) (c : ConstraintPoint) (g : Point) (A : Jacobian) (lam : Multiplier) :
    powellYuanTerminated ε c g A lam ↔
      powellYuanStoppingResidual c g A lam ≤ ε := Iff.rfl

/-- The denominator in the Step-3 penalty update `(13.6.11)` is the difference
`‖c_k‖^2 - ‖c_k + A_kᵀ d_k‖^2`. -/
def powellYuanSigmaUpdateDenominator
    (c : ConstraintPoint) (A : Jacobian) (d : Point) : ℝ :=
  ‖c‖ ^ (2 : ℕ) - ‖cdtConstraintResidual c A d‖ ^ (2 : ℕ)

/-- Unfolding `powellYuanSigmaUpdateDenominator c A d` gives the denominator from
`(13.6.11)`. -/
theorem powellYuanSigmaUpdateDenominator_eq
    (c : ConstraintPoint) (A : Jacobian) (d : Point) :
    powellYuanSigmaUpdateDenominator c A d =
      ‖c‖ ^ (2 : ℕ) - ‖cdtConstraintResidual c A d‖ ^ (2 : ℕ) := rfl

/-- The Step-3 penalty-parameter correction `(13.6.11)`. -/
def powellYuanSigmaUpdate
    (σ pred : ℝ) (c : ConstraintPoint) (A : Jacobian) (d : Point) : ℝ :=
  2 * σ +
    max 0
      (-2 * pred / powellYuanSigmaUpdateDenominator c A d)

/-- Unfolding `powellYuanSigmaUpdate σ pred c A d` gives the source correction formula
`(13.6.11)`. -/
theorem powellYuanSigmaUpdate_eq
    (σ pred : ℝ) (c : ConstraintPoint) (A : Jacobian) (d : Point) :
    powellYuanSigmaUpdate σ pred c A d =
      2 * σ +
        max 0
          (-2 * pred /
            (‖c‖ ^ (2 : ℕ) - ‖cdtConstraintResidual c A d‖ ^ (2 : ℕ))) := rfl

/-- The Step-4 ratio is `Ared_k / Pred_k`. -/
def powellYuanReductionRatio (ared pred : ℝ) : ℝ :=
  ared / pred

/-- Unfolding `powellYuanReductionRatio ared pred` gives the source quotient
`Ared / Pred`. -/
theorem powellYuanReductionRatio_eq (ared pred : ℝ) :
    powellYuanReductionRatio ared pred = ared / pred := rfl

/-- The Step-4 accepted-point update `(13.6.12)`: accept `x_k + d_k` exactly when
`τ₀ < r_k`. -/
def powellYuanAcceptedPoint (tau0 : ℝ) (x d : Point) (r : ℝ) : Point :=
  if tau0 < r then x + d else x

/-- Unfolding `powellYuanAcceptedPoint τ₀ x d r` gives the source update `(13.6.12)`. -/
theorem powellYuanAcceptedPoint_eq (tau0 : ℝ) (x d : Point) (r : ℝ) :
    powellYuanAcceptedPoint tau0 x d r = if tau0 < r then x + d else x := rfl

/-- The Step-4 trust-region-radius update `(13.6.13)`. -/
def powellYuanRadiusUpdate
    (tau1 tau2 tau3 tau4 : ℝ) (Δ r : ℝ) (d : Point) : ℝ :=
  if tau4 < r then
    max (tau1 * ‖d‖) Δ
  else if tau2 ≤ r then
    Δ
  else
    min (Δ / tau1) (tau3 * ‖d‖)

/-- Unfolding `powellYuanRadiusUpdate τ₁ τ₂ τ₃ τ₄ Δ r d` gives the source piecewise update
`(13.6.13)`. -/
theorem powellYuanRadiusUpdate_eq
    (tau1 tau2 tau3 tau4 : ℝ) (Δ r : ℝ) (d : Point) :
    powellYuanRadiusUpdate tau1 tau2 tau3 tau4 Δ r d =
      if tau4 < r then
        max (tau1 * ‖d‖) Δ
      else if tau2 ≤ r then
        Δ
      else
        min (Δ / tau1) (tau3 * ‖d‖) := rfl

/-- The canonical CDT owner `IsCdtSolution B g A c Δ ξ d` specializes to the Powell-Yuan Step-2
subproblem conditions. -/
theorem isPowellYuanSubproblemSolution_iff
    (B : HessianApproximation)
    (g : Point)
    (A : Jacobian)
    (c : ConstraintPoint)
    (Δ ξ : ℝ)
    (d : Point) :
    IsCdtSolution B g A c Δ ξ d ↔
      ‖d‖ ≤ Δ ∧
        ‖cdtConstraintResidual c A d‖ ≤ ξ ∧
        ∀ d' : Point,
          ‖d'‖ ≤ Δ →
            ‖cdtConstraintResidual c A d'‖ ≤ ξ →
              cdtObjective B g d ≤ cdtObjective B g d' := by
  constructor
  · rintro ⟨hd, hmin⟩
    rw [mem_cdtFeasibleSet_iff] at hd
    refine ⟨hd.1, hd.2, ?_⟩
    intro d' hd'_norm hd'_residual
    have hd' : d' ∈ cdtFeasibleSet Δ ξ c A := by
      rw [mem_cdtFeasibleSet_iff]
      exact ⟨hd'_norm, hd'_residual⟩
    exact hmin hd'
  · rintro ⟨hd_norm, hd_residual, hmin⟩
    refine ⟨?_, ?_⟩
    · rw [mem_cdtFeasibleSet_iff]
      exact ⟨hd_norm, hd_residual⟩
    · intro d' hd'
      rw [mem_cdtFeasibleSet_iff] at hd'
      exact hmin d' hd'.1 hd'.2

/-- The normal component `d̂_k = d_k - P̄_k d_k` from `(13.6.19)`. -/
def powellYuanHatDirection
    (Pbar : HessianApproximation) (d : Point) : Point :=
  d - Matrix.toEuclideanLin Pbar d

/-- Unfolding `powellYuanHatDirection Pbar d` gives the source formula
`d̂_k = d_k - P̄_k d_k`. -/
theorem powellYuanHatDirection_eq
    (Pbar : HessianApproximation) (d : Point) :
    powellYuanHatDirection Pbar d =
      d - Matrix.toEuclideanLin Pbar d := rfl

/-- The predicted reduction `(13.6.7)` for the Powell-Yuan exact-penalty model. -/
def powellYuanPredictedReduction
    (g : Point)
    (B : HessianApproximation)
    (A : Jacobian)
    (c : ConstraintPoint)
    (lam lamTrial : Multiplier)
    (σ : ℝ)
    (d dHat : Point) : ℝ :=
  -((inner ℝ (g - Matrix.toEuclideanLin A lam) d) +
      (1 / 2 : ℝ) * inner ℝ d (Matrix.toEuclideanLin B dHat) -
      inner ℝ (lamTrial - lam) (c + (1 / 2 : ℝ) • Matrix.toEuclideanLin A.transpose d) +
      σ *
        (‖cdtConstraintResidual c A d‖ ^ (2 : ℕ) - ‖c‖ ^ (2 : ℕ)))

/-- Unfolding `powellYuanPredictedReduction g B A c lam lamTrial σ d dHat` gives the source
formula `(13.6.7)`. -/
theorem powellYuanPredictedReduction_eq
    (g : Point)
    (B : HessianApproximation)
    (A : Jacobian)
    (c : ConstraintPoint)
    (lam lamTrial : Multiplier)
    (σ : ℝ)
    (d dHat : Point) :
    powellYuanPredictedReduction g B A c lam lamTrial σ d dHat =
      -((inner ℝ (g - Matrix.toEuclideanLin A lam) d) +
          (1 / 2 : ℝ) * inner ℝ d (Matrix.toEuclideanLin B dHat) -
          inner ℝ (lamTrial - lam) (c + (1 / 2 : ℝ) • Matrix.toEuclideanLin A.transpose d) +
          σ *
            (‖cdtConstraintResidual c A d‖ ^ (2 : ℕ) - ‖c‖ ^ (2 : ℕ))) := rfl

/-- The Step-3 acceptance test `(13.6.10)`: the predicted reduction dominates half of the
penalty-weighted linearized-constraint decrease. -/
def powellYuanStep3AcceptanceCondition
    (σ pred : ℝ) (c : ConstraintPoint) (A : Jacobian) (d : Point) : Prop :=
  (σ / 2 : ℝ) * powellYuanSigmaUpdateDenominator c A d ≤
    pred

/-- Unfolding `powellYuanStep3AcceptanceCondition σ pred c A d` gives the source acceptance
inequality `(13.6.10)`. -/
theorem powellYuanStep3AcceptanceCondition_iff
    (σ pred : ℝ) (c : ConstraintPoint) (A : Jacobian) (d : Point) :
    powellYuanStep3AcceptanceCondition σ pred c A d ↔
      (σ / 2 : ℝ) *
          (‖c‖ ^ (2 : ℕ) - ‖cdtConstraintResidual c A d‖ ^ (2 : ℕ)) ≤
        pred := Iff.rfl

/-- A uniform Lipschitz-type bound for the multiplier variation `‖λ_k - λ̄_k‖ ≤ δ₂ ‖d_k‖`
used in the proof of Lemma 13.6.4. -/
def powellYuanMultiplierVariationBound
    (lam lamTrial : ℕ → Multiplier)
    (d : ℕ → Point) : Prop :=
  ∃ delta2 : ℝ, 0 < delta2 ∧
    ∀ k : ℕ, ‖lam k - lamTrial k‖ ≤ delta2 * ‖d k‖

/-- Unfolding `powellYuanMultiplierVariationBound lam lamTrial d` recovers the explicit
multiplier variation estimate from `(13.6.29)`. -/
theorem powellYuanMultiplierVariationBound_iff
    (lam lamTrial : ℕ → Multiplier)
    (d : ℕ → Point) :
    powellYuanMultiplierVariationBound lam lamTrial d ↔
      ∃ delta2 : ℝ, 0 < delta2 ∧
        ∀ k : ℕ, ‖lam k - lamTrial k‖ ≤ delta2 * ‖d k‖ := Iff.rfl

/-- A uniform bound `‖(A_k)⁺‖ * ‖B_k‖ ≤ η` for the product appearing in the proof of
Lemma 13.6.4, stated directly on the canonical pseudoinverse owner `A_k⁺ = (A_k)⁺`. -/
def powellYuanUniformProductBound
    (A : ℕ → Jacobian)
    (B : ℕ → HessianApproximation) : Prop :=
  ∃ eta : ℝ,
    ∀ k : ℕ, ‖(A k)⁺‖ * ‖B k‖ ≤ eta

/-- Unfolding `powellYuanUniformProductBound A B` recovers the explicit uniform product estimate
used in Lemma 13.6.4. -/
theorem powellYuanUniformProductBound_iff
    (A : ℕ → Jacobian)
    (B : ℕ → HessianApproximation) :
    powellYuanUniformProductBound A B ↔
      ∃ eta : ℝ,
        ∀ k : ℕ, ‖(A k)⁺‖ * ‖B k‖ ≤ eta := Iff.rfl

/-- Chapter13 Algorithm 13.6.1: the Powell-Yuan trust-region method for constrained problems.
The method records an initial point `x₁`, an initial radius `Δ₁ > 0`, a tolerance `ε > 0`, and
parameters `τ₀, τ₁, τ₂, τ₃, τ₄` satisfying
`0 < τ₃ < τ₄ < 1 < τ₁` and `0 ≤ τ₀ ≤ τ₂ < 1` with `0 < τ₂`. At each stage `k ≥ 1`, if
`powellYuanStoppingResidual c_k g_k A_k λ_k ≤ ε` then the method stops. Otherwise the recorded
state data satisfy `c_k = c (x_k)`, `g_k = g (x_k)`, and `A_k = A (x_k)` for the fixed problem
maps carried by the structure, while `λ_k` is recorded as stagewise algorithmic data, the
recorded direction `d_k` is a global minimizer of the Chapter 13 CDT owner
`cdtObjective` on `cdtFeasibleSet`, and hence feasible for the source subproblem
`(13.6.1)`-`(13.6.3)` with the recorded linearized-constraint bound `ξ_k`, the candidate and
final predicted reductions are the explicit formula
`powellYuanPredictedReduction` from `(13.6.7)`, Step 3 tests
`powellYuanStep3AcceptanceCondition` from `(13.6.10)` and replaces the incoming penalty
parameter by `powellYuanSigmaUpdate` from `(13.6.11)` when that test fails, the ratio is
`Ared_k / Pred_k` with `Pred_k ≠ 0`, the next iterate uses the acceptance threshold `τ₀` from
`(13.6.12)`, the next radius uses the recorded parameters `τ₁, τ₂, τ₃, τ₄` in `(13.6.13)`,
`B_(k+1)` satisfies the recorded update rule, `sigmaCandidate (k + 1) = σ_k`, and
`σ_(k+1) = σ_k`. -/
structure PowellYuanTrustRegionMethod where
  hessianUpdateRule (k : ℕ) (B BNext : HessianApproximation) : Prop
  tolerance : ℝ
  tau0 : ℝ
  tau1 : ℝ
  tau2 : ℝ
  tau3 : ℝ
  tau4 : ℝ
  initialPoint : Point
  initialRadius : ℝ
  constraintResidualAt : Point → ConstraintPoint
  gradientAt : Point → Point
  constraintJacobianAt : Point → Jacobian
  iterate : ℕ → Point
  constraintResidual : ℕ → ConstraintPoint
  gradient : ℕ → Point
  constraintJacobian : ℕ → Jacobian
  multiplier : ℕ → Multiplier
  trialMultiplier : ℕ → Multiplier
  hessianApproximation : ℕ → HessianApproximation
  radius : ℕ → ℝ
  constraintBound : ℕ → ℝ
  sigmaCandidate : ℕ → ℝ
  sigma : ℕ → ℝ
  direction : ℕ → Point
  projectedDirection : ℕ → Point
  predictedReductionCandidate : ℕ → ℝ
  predictedReduction : ℕ → ℝ
  actualReduction : ℕ → ℝ
  ratio : ℕ → ℝ
  tolerance_pos : 0 < tolerance
  tau3_pos : 0 < tau3
  tau3_lt_tau4 : tau3 < tau4
  tau4_lt_one : tau4 < 1
  tau1_gt_one : 1 < tau1
  tau0_nonneg : 0 ≤ tau0
  tau0_le_tau2 : tau0 ≤ tau2
  tau2_pos : 0 < tau2
  tau2_lt_one : tau2 < 1
  initialRadius_pos : 0 < initialRadius
  iterate_one : iterate 1 = initialPoint
  radius_one : radius 1 = initialRadius
  radius_pos (k : ℕ) (_ : 1 ≤ k) : 0 < radius k
  constraintResidual_spec (k : ℕ) (_ : 1 ≤ k) :
    constraintResidual k = constraintResidualAt (iterate k)
  gradient_spec (k : ℕ) (_ : 1 ≤ k) :
    gradient k = gradientAt (iterate k)
  constraintJacobian_spec (k : ℕ) (_ : 1 ≤ k) :
    constraintJacobian k = constraintJacobianAt (iterate k)
  direction_subproblem
      (k : ℕ)
      (_ : 1 ≤ k)
      (h_not_term : ¬ powellYuanTerminated
        tolerance
        (constraintResidual k)
        (gradient k)
        (constraintJacobian k)
        (multiplier k)) :
      IsCdtSolution
        (hessianApproximation k)
        (gradient k)
        (constraintJacobian k)
        (constraintResidual k)
        (radius k)
        (constraintBound k)
        (direction k)
  predictedReductionCandidate_spec
      (k : ℕ)
      (_ : 1 ≤ k)
      (h_not_term : ¬ powellYuanTerminated
        tolerance
        (constraintResidual k)
        (gradient k)
        (constraintJacobian k)
        (multiplier k)) :
      predictedReductionCandidate k =
        powellYuanPredictedReduction
          (gradient k)
          (hessianApproximation k)
          (constraintJacobian k)
          (constraintResidual k)
          (multiplier k)
          (trialMultiplier k)
          (sigmaCandidate k)
          (direction k)
          (projectedDirection k)
  sigma_eq_candidate_of_step3
      (k : ℕ)
      (_ : 1 ≤ k)
      (h_not_term : ¬ powellYuanTerminated
        tolerance
        (constraintResidual k)
        (gradient k)
        (constraintJacobian k)
        (multiplier k))
      (h_step3 : powellYuanStep3AcceptanceCondition
        (sigmaCandidate k)
        (predictedReductionCandidate k)
        (constraintResidual k)
        (constraintJacobian k)
        (direction k)) :
      sigma k = sigmaCandidate k
  sigmaUpdateDenominator_ne_zero_of_not_step3
      (k : ℕ)
      (_ : 1 ≤ k)
      (h_not_term : ¬ powellYuanTerminated
        tolerance
        (constraintResidual k)
        (gradient k)
        (constraintJacobian k)
        (multiplier k))
      (h_not_step3 : ¬ powellYuanStep3AcceptanceCondition
        (sigmaCandidate k)
        (predictedReductionCandidate k)
        (constraintResidual k)
        (constraintJacobian k)
        (direction k)) :
      powellYuanSigmaUpdateDenominator
        (constraintResidual k)
        (constraintJacobian k)
        (direction k) ≠ 0
  sigma_eq_update_of_not_step3
      (k : ℕ)
      (_ : 1 ≤ k)
      (h_not_term : ¬ powellYuanTerminated
        tolerance
        (constraintResidual k)
        (gradient k)
        (constraintJacobian k)
        (multiplier k))
      (h_not_step3 : ¬ powellYuanStep3AcceptanceCondition
        (sigmaCandidate k)
        (predictedReductionCandidate k)
        (constraintResidual k)
        (constraintJacobian k)
        (direction k)) :
      sigma k =
        powellYuanSigmaUpdate
          (sigmaCandidate k)
          (predictedReductionCandidate k)
          (constraintResidual k)
          (constraintJacobian k)
          (direction k)
  predictedReduction_spec
      (k : ℕ)
      (_ : 1 ≤ k)
      (h_not_term : ¬ powellYuanTerminated
        tolerance
        (constraintResidual k)
        (gradient k)
        (constraintJacobian k)
        (multiplier k)) :
      predictedReduction k =
        powellYuanPredictedReduction
          (gradient k)
          (hessianApproximation k)
          (constraintJacobian k)
          (constraintResidual k)
          (multiplier k)
          (trialMultiplier k)
          (sigma k)
          (direction k)
          (projectedDirection k)
  predictedReduction_ne_zero_of_not_terminated
      (k : ℕ)
      (_ : 1 ≤ k)
      (h_not_term : ¬ powellYuanTerminated
        tolerance
        (constraintResidual k)
        (gradient k)
        (constraintJacobian k)
        (multiplier k)) :
      predictedReduction k ≠ 0
  ratio_eq
      (k : ℕ)
      (_ : 1 ≤ k)
      (h_not_term : ¬ powellYuanTerminated
        tolerance
        (constraintResidual k)
        (gradient k)
        (constraintJacobian k)
        (multiplier k)) :
      ratio k = powellYuanReductionRatio (actualReduction k) (predictedReduction k)
  iterate_next_of_not_terminated
      (k : ℕ)
      (_ : 1 ≤ k)
      (h_not_term : ¬ powellYuanTerminated
        tolerance
        (constraintResidual k)
        (gradient k)
        (constraintJacobian k)
        (multiplier k)) :
      iterate (k + 1) =
        powellYuanAcceptedPoint
          tau0
          (iterate k)
          (direction k)
          (ratio k)
  radius_next_of_not_terminated
      (k : ℕ)
      (_ : 1 ≤ k)
      (h_not_term : ¬ powellYuanTerminated
        tolerance
        (constraintResidual k)
        (gradient k)
        (constraintJacobian k)
        (multiplier k)) :
      radius (k + 1) =
        powellYuanRadiusUpdate
          tau1
          tau2
          tau3
          tau4
          (radius k)
          (ratio k)
          (direction k)
  sigmaCandidate_next_of_not_terminated
      (k : ℕ)
      (_ : 1 ≤ k)
      (h_not_term : ¬ powellYuanTerminated
        tolerance
        (constraintResidual k)
        (gradient k)
        (constraintJacobian k)
        (multiplier k)) :
      sigmaCandidate (k + 1) = sigma k
  sigma_next_of_not_terminated
      (k : ℕ)
      (_ : 1 ≤ k)
      (h_not_term : ¬ powellYuanTerminated
        tolerance
        (constraintResidual k)
        (gradient k)
        (constraintJacobian k)
        (multiplier k)) :
      sigma (k + 1) = sigma k
  hessian_next_of_not_terminated
      (k : ℕ)
      (_ : 1 ≤ k)
      (h_not_term : ¬ powellYuanTerminated
        tolerance
        (constraintResidual k)
        (gradient k)
        (constraintJacobian k)
        (multiplier k)) :
      hessianUpdateRule
        k
        (hessianApproximation k)
        (hessianApproximation (k + 1))

namespace PowellYuanTrustRegionMethod

local notation "Method" => @PowellYuanTrustRegionMethod m n

/-- A Powell-Yuan method coerces to its recorded iterate sequence `k ↦ x_k`. -/
instance instCoeFun :
    CoeFun (@_root_.PowellYuanTrustRegionMethod m n) (fun _ ↦ ℕ → Point) where
  coe method := method.iterate

/-- The Step-2 stopping test for a recorded Powell-Yuan method at stage `k`. -/
def terminatedAt (method : Method) (k : ℕ) : Prop :=
  powellYuanTerminated
    method.tolerance
    (method.constraintResidual k)
    (method.gradient k)
    (method.constraintJacobian k)
    (method.multiplier k)

/-- Unfolding `method.terminatedAt k` gives the source Step-2 stopping inequality. -/
theorem terminatedAt_iff
    (method : Method) (k : ℕ) :
    method.terminatedAt k ↔
      powellYuanStoppingResidual
          (method.constraintResidual k)
          (method.gradient k)
          (method.constraintJacobian k)
          (method.multiplier k) ≤
        method.tolerance := Iff.rfl

/-- An Algorithm 13.6.1 run finitely terminates when some stage `k ≥ 1` satisfies the recorded
Step-2 stopping test. -/
def finitelyTerminates (method : Method) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ method.terminatedAt k

/-- Unfolding `method.finitelyTerminates` gives the existence of a terminating stage `k ≥ 1`. -/
theorem finitelyTerminates_iff
    (method : Method) :
    method.finitelyTerminates ↔ ∃ k : ℕ, 1 ≤ k ∧ method.terminatedAt k := Iff.rfl

/-- The next iterate at stage `k` is the accepted-point update `(13.6.12)` applied to the
recorded step data and acceptance threshold `τ₀`. -/
def acceptedPointAt (method : Method) (k : ℕ) : Point :=
  powellYuanAcceptedPoint
    method.tau0
    (method.iterate k)
    (method.direction k)
    (method.ratio k)

/-- Unfolding `method.acceptedPointAt k` gives the recorded Step-4 accepted-point update. -/
theorem acceptedPointAt_eq
    (method : Method) (k : ℕ) :
    method.acceptedPointAt k =
      powellYuanAcceptedPoint
        method.tau0
        (method.iterate k)
        (method.direction k)
        (method.ratio k) := rfl

/-- The next trust-region radius at stage `k` is the source piecewise update `(13.6.13)` applied
to the recorded parameters `τ₁, τ₂, τ₃, τ₄`, radius, ratio, and step. -/
def nextRadiusAt (method : Method) (k : ℕ) : ℝ :=
  powellYuanRadiusUpdate
    method.tau1
    method.tau2
    method.tau3
    method.tau4
    (method.radius k)
    (method.ratio k)
    (method.direction k)

/-- Unfolding `method.nextRadiusAt k` gives the recorded Step-4 radius update. -/
theorem nextRadiusAt_eq
    (method : Method) (k : ℕ) :
    method.nextRadiusAt k =
      powellYuanRadiusUpdate
        method.tau1
        method.tau2
        method.tau3
        method.tau4
        (method.radius k)
        (method.ratio k)
        (method.direction k) := rfl

/-- The Step-3 acceptance test at stage `k` is the source inequality `(13.6.10)` applied to the
incoming penalty parameter and the candidate predicted reduction. -/
def step3AcceptsAt (method : Method) (k : ℕ) : Prop :=
  powellYuanStep3AcceptanceCondition
    (method.sigmaCandidate k)
    (method.predictedReductionCandidate k)
    (method.constraintResidual k)
    (method.constraintJacobian k)
    (method.direction k)

/-- Unfolding `method.step3AcceptsAt k` gives the recorded Step-3 acceptance test. -/
theorem step3AcceptsAt_iff
    (method : Method) (k : ℕ) :
    method.step3AcceptsAt k ↔
      powellYuanStep3AcceptanceCondition
        (method.sigmaCandidate k)
        (method.predictedReductionCandidate k)
        (method.constraintResidual k)
        (method.constraintJacobian k)
        (method.direction k) := Iff.rfl

/-- `method.satisfiesAssumption1362` reuses the Chapter 13 owner
`PowellYuanAssumption1362` directly on the recorded iterate, direction, Jacobian, and Hessian
data of Algorithm 13.6.1. -/
abbrev satisfiesAssumption1362 (method : Method) :=
  PowellYuanAssumption1362
    method.iterate
    method.direction
    method.constraintJacobianAt
    method.hessianApproximation

/-- Unfolding `method.satisfiesAssumption1362` gives the direct reuse of the Chapter 13
assumption owner on the recorded Algorithm 13.6.1 data. -/
theorem satisfiesAssumption1362_eq
    (method : Method) :
    method.satisfiesAssumption1362 =
      PowellYuanAssumption1362
        method.iterate
        method.direction
        method.constraintJacobianAt
        method.hessianApproximation := rfl

/-- At every stage `k ≥ 1`, the recorded residual vector is the fixed problem residual evaluated
at `x_k`. -/
theorem constraintResidual_eq_at
    (method : Method) {k : ℕ} (hk : 1 ≤ k) :
    method.constraintResidual k = method.constraintResidualAt (method.iterate k) :=
  method.constraintResidual_spec k hk

/-- At every stage `k ≥ 1`, the recorded gradient is the fixed problem gradient evaluated at
`x_k`. -/
theorem gradient_eq_at
    (method : Method) {k : ℕ} (hk : 1 ≤ k) :
    method.gradient k = method.gradientAt (method.iterate k) :=
  method.gradient_spec k hk

/-- At every stage `k ≥ 1`, the recorded constraint Jacobian is the fixed problem Jacobian
evaluated at `x_k`. -/
theorem constraintJacobian_eq_at
    (method : Method) {k : ℕ} (hk : 1 ≤ k) :
    method.constraintJacobian k = method.constraintJacobianAt (method.iterate k) :=
  method.constraintJacobian_spec k hk

/-- At a nonterminal stage `k ≥ 1`, the recorded direction solves the source subproblem
`(13.6.1)`-`(13.6.3)` through the canonical Chapter 13 CDT owner. -/
theorem direction_isCdtSolution_at
    (method : Method) {k : ℕ} (hk : 1 ≤ k)
    (h_not_term : ¬ method.terminatedAt k) :
    IsCdtSolution
      (method.hessianApproximation k)
      (method.gradient k)
      (method.constraintJacobian k)
      (method.constraintResidual k)
      (method.radius k)
      (method.constraintBound k)
      (method.direction k) :=
  method.direction_subproblem k hk h_not_term

/-- At a nonterminal stage `k ≥ 1`, the recorded direction satisfies the source Step-2
subproblem conditions `(13.6.1)`-`(13.6.3)`. -/
theorem direction_subproblem_at
    (method : Method) {k : ℕ} (hk : 1 ≤ k)
    (h_not_term : ¬ method.terminatedAt k) :
    ‖method.direction k‖ ≤ method.radius k ∧
      ‖cdtConstraintResidual
          (method.constraintResidual k)
          (method.constraintJacobian k)
          (method.direction k)‖ ≤
        method.constraintBound k ∧
      ∀ d' : Point,
        ‖d'‖ ≤ method.radius k →
          ‖cdtConstraintResidual
              (method.constraintResidual k)
              (method.constraintJacobian k)
              d'‖ ≤
            method.constraintBound k →
            cdtObjective
                (method.hessianApproximation k)
                (method.gradient k)
                (method.direction k) ≤
              cdtObjective
                (method.hessianApproximation k)
                (method.gradient k)
                d' := by
  exact
    (isPowellYuanSubproblemSolution_iff
        (method.hessianApproximation k)
        (method.gradient k)
        (method.constraintJacobian k)
        (method.constraintResidual k)
        (method.radius k)
        (method.constraintBound k)
        (method.direction k)).1
      (method.direction_isCdtSolution_at hk h_not_term)

/-- At a nonterminal stage `k ≥ 1`, if Step 3 rejects the candidate penalty parameter, then the
denominator in `(13.6.11)` is nonzero, so the correction term is an ordinary quotient. -/
theorem sigmaUpdateDenominator_ne_zero_at
    (method : Method) {k : ℕ} (hk : 1 ≤ k)
    (h_not_term : ¬ method.terminatedAt k)
    (h_not_step3 : ¬ method.step3AcceptsAt k) :
    powellYuanSigmaUpdateDenominator
      (method.constraintResidual k)
      (method.constraintJacobian k)
      (method.direction k) ≠ 0 := by
  -- Unfold the namespace abbreviations so the stored Step-3 rejection field applies directly.
  simpa [PowellYuanTrustRegionMethod.terminatedAt, PowellYuanTrustRegionMethod.step3AcceptsAt] using
    method.sigmaUpdateDenominator_ne_zero_of_not_step3 k hk h_not_term h_not_step3

/-- At a nonterminal stage `k ≥ 1`, the source quotient `Ared_k / Pred_k` is well defined
because the recorded `Pred_k` is nonzero. -/
theorem predictedReduction_ne_zero_at
    (method : Method) {k : ℕ} (hk : 1 ≤ k)
    (h_not_term : ¬ method.terminatedAt k) :
    method.predictedReduction k ≠ 0 := by
  -- Reuse the recorded nonvanishing field after aligning the stopping-test abbreviation.
  simpa [PowellYuanTrustRegionMethod.terminatedAt] using
    method.predictedReduction_ne_zero_of_not_terminated k hk h_not_term

/-- At a nonterminal stage `k ≥ 1`, the recorded ratio is the Step-4 quotient
`Ared_k / Pred_k`. -/
theorem ratio_eq_at
    (method : Method) {k : ℕ} (hk : 1 ≤ k)
    (h_not_term : ¬ method.terminatedAt k) :
    method.ratio k =
      powellYuanReductionRatio (method.actualReduction k) (method.predictedReduction k) := by
  -- The Step-4 ratio formula is already stored as a structure field; only the stopping test
  -- abbreviation needs normalization.
  simpa [PowellYuanTrustRegionMethod.terminatedAt] using method.ratio_eq k hk h_not_term

/-- At a nonterminal stage `k ≥ 1`, the next iterate is the accepted-point update `(13.6.12)`. -/
theorem iterate_succ_eq_acceptedPoint
    (method : Method) {k : ℕ} (hk : 1 ≤ k)
    (h_not_term : ¬ method.terminatedAt k) :
    method.iterate (k + 1) = method.acceptedPointAt k := by
  -- Normalize the API wrapper on the right-hand side to the stored Step-4 iterate update.
  simpa
      [PowellYuanTrustRegionMethod.terminatedAt,
        PowellYuanTrustRegionMethod.acceptedPointAt] using
    method.iterate_next_of_not_terminated k hk h_not_term

/-- At a nonterminal stage `k ≥ 1`, the next radius is the Step-4 update `(13.6.13)`. -/
theorem radius_succ_eq_nextRadius
    (method : Method) {k : ℕ} (hk : 1 ≤ k)
    (h_not_term : ¬ method.terminatedAt k) :
    method.radius (k + 1) = method.nextRadiusAt k := by
  -- Normalize the radius wrapper to the stored Step-4 update formula.
  simpa
      [PowellYuanTrustRegionMethod.terminatedAt,
        PowellYuanTrustRegionMethod.nextRadiusAt] using
    method.radius_next_of_not_terminated k hk h_not_term

/-- At a nonterminal stage `k ≥ 1`, Step 5 copies the corrected penalty parameter forward:
`σ_(k+1) = σ_k`. -/
theorem sigma_succ_eq
    (method : Method) {k : ℕ} (hk : 1 ≤ k)
    (h_not_term : ¬ method.terminatedAt k) :
    method.sigma (k + 1) = method.sigma k := by
  -- Step 5 stores the corrected penalty parameter unchanged at the next stage.
  simpa [PowellYuanTrustRegionMethod.terminatedAt] using
    method.sigma_next_of_not_terminated k hk h_not_term

/-- At a nonterminal stage `k ≥ 1`, the incoming Step-3 penalty parameter for stage `k + 1` is
the corrected value from stage `k`. -/
theorem sigmaCandidate_succ_eq
    (method : Method) {k : ℕ} (hk : 1 ≤ k)
    (h_not_term : ¬ method.terminatedAt k) :
    method.sigmaCandidate (k + 1) = method.sigma k := by
  -- Step 5 also records the next incoming candidate penalty as the corrected current one.
  simpa [PowellYuanTrustRegionMethod.terminatedAt] using
    method.sigmaCandidate_next_of_not_terminated k hk h_not_term

end PowellYuanTrustRegionMethod

#print axioms powellYuanStoppingResidual
#print axioms powellYuanSigmaUpdateDenominator
#print axioms isPowellYuanSubproblemSolution_iff
#print axioms powellYuanPredictedReduction
#print axioms powellYuanStep3AcceptanceCondition
#print axioms powellYuanSigmaUpdate
#print axioms powellYuanReductionRatio
#print axioms powellYuanAcceptedPoint
#print axioms powellYuanRadiusUpdate

end
