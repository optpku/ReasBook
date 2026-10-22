/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Set.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Exercise_1_5
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Theorem_9_3_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Definition_6_1_extra_1

noncomputable section

section

open scoped Matrix
open scoped Matrix.Norms.L2Operator

variable {ambientDim constraintDim tangentDim : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin ambientDim)
local notation "ConstraintPoint" => EuclideanSpace ℝ (Fin constraintDim)
local notation "TangentPoint" => EuclideanSpace ℝ (Fin tangentDim)
local notation "HessianMatrix" => Matrix (Fin ambientDim) (Fin ambientDim) ℝ
local notation "ConstraintJacobianMatrix" => Matrix (Fin ambientDim) (Fin constraintDim) ℝ
local notation "NullSpaceMatrix" => Matrix (Fin ambientDim) (Fin tangentDim) ℝ
local notation "PseudoInverseMatrix" => Matrix (Fin constraintDim) (Fin ambientDim) ℝ

-- Semantic recall: `lean_leansearch` did not surface a reusable mathlib owner for the
-- constrained null-space trust-region method of Section 13.4. Following nearby Chapter 13 and
-- Chapter 6 algorithm files, this item keeps the stopping residual, the Step-2 penalty test and
-- reset, the Step-4 actual/predicted reductions, the acceptance update, and the radius-choice
-- rule explicit on the main owner.

/-- The reduced gradient `Zᵀ g` used in the null-space stopping test. -/
def nullSpaceReducedGradient (Z : NullSpaceMatrix) (g : Point) : TangentPoint :=
  Matrix.toEuclideanLin (Z.transpose) g

/-- Unfolding `nullSpaceReducedGradient Z g` gives the source formula `Zᵀ g`. -/
theorem nullSpaceReducedGradient_eq (Z : NullSpaceMatrix) (g : Point) :
    nullSpaceReducedGradient Z g = Matrix.toEuclideanLin (Z.transpose) g :=
  rfl

#print axioms nullSpaceReducedGradient

/-- The Step-2 stopping residual `‖c_k‖₂ + ‖Z_kᵀ g_k‖₂` from Algorithm 13.4.1. -/
def nullSpaceStoppingResidual
    (c : ConstraintPoint) (Z : NullSpaceMatrix) (g : Point) : ℝ :=
  ‖c‖ + ‖nullSpaceReducedGradient Z g‖

/-- Unfolding `nullSpaceStoppingResidual c Z g` gives the source stopping quantity
`‖c‖₂ + ‖Zᵀ g‖₂`. -/
theorem nullSpaceStoppingResidual_eq
    (c : ConstraintPoint) (Z : NullSpaceMatrix) (g : Point) :
    nullSpaceStoppingResidual c Z g = ‖c‖ + ‖nullSpaceReducedGradient Z g‖ :=
  rfl

#print axioms nullSpaceStoppingResidual

/-- The Step-2 penalty reset
`σ_k = ‖A_k⁺ (g_k + (1 / 2) B_k d̂_k)‖ + 2ρ` used when `(13.4.24)` fails. -/
def nullSpacePenaltyUpdate
    (APlus : PseudoInverseMatrix) (g : Point) (B : HessianMatrix) (dHat : Point) (ρ : ℝ) : ℝ :=
  ‖Matrix.toEuclideanLin APlus
      (g + (1 / 2 : ℝ) • Matrix.toEuclideanLin B dHat)‖ + (2 : ℝ) * ρ

/-- Unfolding `nullSpacePenaltyUpdate APlus g B dHat ρ` gives the source Step-2 reset formula
for `σ_k`. -/
theorem nullSpacePenaltyUpdate_eq
    (APlus : PseudoInverseMatrix) (g : Point) (B : HessianMatrix) (dHat : Point) (ρ : ℝ) :
    nullSpacePenaltyUpdate APlus g B dHat ρ =
      ‖Matrix.toEuclideanLin APlus
          (g + (1 / 2 : ℝ) • Matrix.toEuclideanLin B dHat)‖ + (2 : ℝ) * ρ :=
  rfl

#print axioms nullSpacePenaltyUpdate

/-- The current Step-2 test `(13.4.24)` accepts the incoming penalty parameter exactly when it
already dominates the reset threshold `‖A_k⁺ (g_k + (1 / 2) B_k d̂_k)‖ + 2ρ`. -/
def nullSpaceStepTwoAcceptanceCondition
    (σ : ℝ) (APlus : PseudoInverseMatrix) (g : Point) (B : HessianMatrix) (dHat : Point)
    (ρ : ℝ) : Prop :=
  nullSpacePenaltyUpdate APlus g B dHat ρ ≤ σ

/-- Unfolding `nullSpaceStepTwoAcceptanceCondition σ APlus g B dHat ρ` gives the currently
formalized Step-2 acceptance inequality for `(13.4.24)`. -/
theorem nullSpaceStepTwoAcceptanceCondition_iff
    (σ : ℝ) (APlus : PseudoInverseMatrix) (g : Point) (B : HessianMatrix) (dHat : Point)
    (ρ : ℝ) :
    nullSpaceStepTwoAcceptanceCondition σ APlus g B dHat ρ ↔
      nullSpacePenaltyUpdate APlus g B dHat ρ ≤ σ :=
  Iff.rfl

/-- The Step-4 predicted reduction `(13.4.17)` is the decrease of the recorded local model from
the origin to the trial step. -/
def nullSpacePredictedReduction
    (predictedModel : Point → ℝ) (d : Point) : ℝ :=
  predictedModel 0 - predictedModel d

/-- Unfolding `nullSpacePredictedReduction predictedModel d` gives the recorded model decrease
used for `Pred_k`. -/
theorem nullSpacePredictedReduction_eq
    (predictedModel : Point → ℝ) (d : Point) :
    nullSpacePredictedReduction predictedModel d =
      predictedModel 0 - predictedModel d :=
  rfl

#print axioms nullSpacePredictedReduction

/-- The Step-3 trial-step condition `(13.4.27)` specialized to the null-space data from stage
`k`: the recorded predicted reduction dominates the source constraint and reduced-gradient lower
bounds, using `‖c_k‖₂`, `‖Z_kᵀ g_k‖₂`, `Δ_k`, the actual operator norms of `A_k⁺` and `B_k`,
plus `‖d̂_k‖₂`. -/
def nullSpaceTrialStepCondition
    (predictedReduction ρ₁ ρ₂ : ℝ)
    (c : ConstraintPoint)
    (Z : NullSpaceMatrix)
    (g : Point)
    (trustRegionRadius : ℝ)
    (APlus : PseudoInverseMatrix)
    (B : HessianMatrix)
    (dHat : Point) : Prop :=
  ‖dHat‖ ≤ trustRegionRadius ∧
    (if ‖APlus‖₂ = 0 then
      ρ₁ * ‖c‖
    else
      ρ₁ * min ‖c‖ (trustRegionRadius / ‖APlus‖₂)) ≤
      predictedReduction ∧
    ρ₂ * min ‖nullSpaceReducedGradient Z g‖ 1 *
        min
          (Real.sqrt (trustRegionRadius ^ (2 : ℕ) - ‖dHat‖ ^ (2 : ℕ)))
          (‖nullSpaceReducedGradient Z g‖ / (1 + ‖B‖₂)) ≤
      predictedReduction

/-- Unfolding
`nullSpaceTrialStepCondition predictedReduction ρ₁ ρ₂ c Z g Δ APlus B dHat`
gives the currently formalized Step-3 condition `(13.4.27)`. -/
theorem nullSpaceTrialStepCondition_iff
    (predictedReduction ρ₁ ρ₂ : ℝ)
    (c : ConstraintPoint)
    (Z : NullSpaceMatrix)
    (g : Point)
    (trustRegionRadius : ℝ)
    (APlus : PseudoInverseMatrix)
    (B : HessianMatrix)
    (dHat : Point) :
    nullSpaceTrialStepCondition
        predictedReduction
        ρ₁
        ρ₂
        c
        Z
        g
        trustRegionRadius
        APlus
        B
        dHat ↔
      ‖dHat‖ ≤ trustRegionRadius ∧
        (if ‖APlus‖₂ = 0 then
          ρ₁ * ‖c‖
        else
          ρ₁ * min ‖c‖ (trustRegionRadius / ‖APlus‖₂)) ≤
          predictedReduction ∧
        ρ₂ * min ‖nullSpaceReducedGradient Z g‖ 1 *
            min
              (Real.sqrt (trustRegionRadius ^ (2 : ℕ) - ‖dHat‖ ^ (2 : ℕ)))
              (‖nullSpaceReducedGradient Z g‖ / (1 + ‖B‖₂)) ≤
          predictedReduction :=
  Iff.rfl

/-- `IsNullSpaceBasisFor A Z` records that `Z` is an actual basis matrix for the Step-2 null
space `ker(Aᵀ)`: the Chapter 9 owner `IsReducedNullMatrix A Z` supplies the null-space range
condition, while `Z.mulVec` is injective so the columns of `Z` are linearly independent. -/
def IsNullSpaceBasisFor (A : ConstraintJacobianMatrix) (Z : NullSpaceMatrix) : Prop :=
  IsReducedNullMatrix A Z ∧ Function.Injective Z.mulVec

/-- Unfolding `IsNullSpaceBasisFor A Z` gives the reduced-null-space owner together with the
injectivity that makes the columns of `Z` an actual basis. -/
theorem isNullSpaceBasisFor_iff (A : ConstraintJacobianMatrix) (Z : NullSpaceMatrix) :
    IsNullSpaceBasisFor A Z ↔
      IsReducedNullMatrix A Z ∧ Function.Injective Z.mulVec :=
  Iff.rfl

/-- A null-space basis matrix is in particular a reduced-null-space matrix. -/
theorem IsNullSpaceBasisFor.isReducedNullMatrix
    {A : ConstraintJacobianMatrix} {Z : NullSpaceMatrix} (h : IsNullSpaceBasisFor A Z) :
    IsReducedNullMatrix A Z :=
  h.1

/-- A null-space basis matrix has injective coordinate map, so its columns are linearly
independent. -/
theorem IsNullSpaceBasisFor.mulVec_injective
    {A : ConstraintJacobianMatrix} {Z : NullSpaceMatrix} (h : IsNullSpaceBasisFor A Z) :
    Function.Injective Z.mulVec :=
  h.2

/-- The Step-4 accepted-point update `(13.4.28)`: accept `x_k + d_k` when `r_k > β₀`, and keep
`x_k` otherwise. -/
def nullSpaceAcceptedPoint (β₀ : ℝ) (x d : Point) (r : ℝ) : Point :=
  if β₀ < r then x + d else x

/-- Unfolding `nullSpaceAcceptedPoint β₀ x d r` gives the source update `(13.4.28)`. -/
theorem nullSpaceAcceptedPoint_eq (β₀ : ℝ) (x d : Point) (r : ℝ) :
    nullSpaceAcceptedPoint β₀ x d r = if β₀ < r then x + d else x :=
  rfl

#print axioms nullSpaceAcceptedPoint

/-- The Step-4 radius-choice rule `(13.4.29)`: if `r_k < β₂`, then `Δ_(k+1)` lies in the open
interval `(β₃ * ‖d_k‖₂, β₄ * Δ_k)`; otherwise it lies in `(Δ_k, β₁ * Δ_k)`. -/
def nullSpaceRadiusUpdateCondition
    (β₁ β₂ β₃ β₄ Δ : ℝ) (d : Point) (r ΔNext : ℝ) : Prop :=
  if r < β₂ then
    ΔNext ∈ Set.Ioo (β₃ * ‖d‖) (β₄ * Δ)
  else
    ΔNext ∈ Set.Ioo Δ (β₁ * Δ)

/-- Unfolding `nullSpaceRadiusUpdateCondition β₁ β₂ β₃ β₄ Δ d r ΔNext` gives the two source
branches for choosing `Δ_(k+1)`. -/
theorem nullSpaceRadiusUpdateCondition_iff
    (β₁ β₂ β₃ β₄ Δ : ℝ) (d : Point) (r ΔNext : ℝ) :
    nullSpaceRadiusUpdateCondition β₁ β₂ β₃ β₄ Δ d r ΔNext ↔
      (if r < β₂ then
        ΔNext ∈ Set.Ioo (β₃ * ‖d‖) (β₄ * Δ)
      else
        ΔNext ∈ Set.Ioo Δ (β₁ * Δ)) :=
  Iff.rfl

#print axioms nullSpaceRadiusUpdateCondition

/-- Chapter13 Algorithm 13.4.1: a null-space trust-region method on a fixed constrained
problem. It records `x₁`, `Δ₁`, `σ₁`; fixed maps for `c`, `g`, `A`; stagewise data
`x_k`, `Δ_k`, `σ_k`, `c_k`, `A_k`, `Z_k`, `g_k`, `B_k`, `d̂_k`, `A_k⁺`, `d_k`, `Ared_k`,
`Pred_k`, `r_k`; the identities `c_k = c(x_k)`, `g_k = g(x_k)`, `A_k = A(x_k)`; a null-space
basis matrix `Z_k` for `ker(A_kᵀ)`; the canonical pseudoinverse identity `A_k⁺ = (A_k)⁺`; and
the nonterminal update rules `(13.4.24)`, `(13.4.27)`, `(13.4.16)`-`(13.4.17)`, `(13.4.28)`,
`(13.4.29)`. -/
structure NullSpaceTrustRegionMethod (n m t : ℕ) where
  β₀ : ℝ
  β₁ : ℝ
  β₂ : ℝ
  β₃ : ℝ
  β₄ : ℝ
  ρ : ℝ
  ρ₁ : ℝ
  ρ₂ : ℝ
  ε : ℝ
  initialPoint : EuclideanSpace ℝ (Fin n)
  initialRadius : ℝ
  initialIncomingSigma : ℝ
  penaltyFunction : EuclideanSpace ℝ (Fin n) → ℝ
  constraintResidualAt : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)
  gradientAt : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)
  constraintJacobianAt : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin m) ℝ
  predictedModel : ℕ → EuclideanSpace ℝ (Fin n) → ℝ
  iterate : ℕ → EuclideanSpace ℝ (Fin n)
  radius : ℕ → ℝ
  incomingSigma : ℕ → ℝ
  stageSigma : ℕ → ℝ
  constraintResidual : ℕ → EuclideanSpace ℝ (Fin m)
  constraintJacobian : ℕ → Matrix (Fin n) (Fin m) ℝ
  nullSpaceBasis : ℕ → Matrix (Fin n) (Fin t) ℝ
  gradient : ℕ → EuclideanSpace ℝ (Fin n)
  hessianApproximation : ℕ → Matrix (Fin n) (Fin n) ℝ
  dHat : ℕ → EuclideanSpace ℝ (Fin n)
  aPseudoInverse : ℕ → Matrix (Fin m) (Fin n) ℝ
  trialStep : ℕ → EuclideanSpace ℝ (Fin n)
  actualReduction : ℕ → ℝ
  predictedReduction : ℕ → ℝ
  ratio : ℕ → ℝ
  beta3_pos : 0 < β₃
  beta3_lt_beta4 : β₃ < β₄
  beta4_lt_one : β₄ < 1
  one_lt_beta1 : 1 < β₁
  beta0_nonneg : 0 ≤ β₀
  beta0_le_beta2 : β₀ ≤ β₂
  beta2_lt_one : β₂ < 1
  beta2_pos : 0 < β₂
  rho1_nonneg : 0 ≤ ρ₁
  rho2_nonneg : 0 ≤ ρ₂
  epsilon_nonneg : 0 ≤ ε
  initialRadius_pos : 0 < initialRadius
  initialIncomingSigma_pos : 0 < initialIncomingSigma
  iterate_one : iterate 1 = initialPoint
  radius_one : radius 1 = initialRadius
  incomingSigma_one : incomingSigma 1 = initialIncomingSigma
  radius_pos : ∀ k : ℕ, 1 ≤ k → 0 < radius k
  constraintResidual_spec :
    ∀ k : ℕ, 1 ≤ k →
      constraintResidual k = constraintResidualAt (iterate k)
  gradient_spec :
    ∀ k : ℕ, 1 ≤ k →
      gradient k = gradientAt (iterate k)
  constraintJacobian_spec :
    ∀ k : ℕ, 1 ≤ k →
      constraintJacobian k = constraintJacobianAt (iterate k)
  nullSpaceBasis_spec :
    ∀ k : ℕ, 1 ≤ k →
      IsNullSpaceBasisFor (constraintJacobian k) (nullSpaceBasis k)
  aPseudoInverse_spec :
    ∀ k : ℕ, 1 ≤ k →
      aPseudoInverse k = (constraintJacobian k)⁺
  stageSigma_eq_incoming_of_stepTwoAccepts :
    ∀ k : ℕ, 1 ≤ k →
      ¬ (nullSpaceStoppingResidual
          (constraintResidual k)
          (nullSpaceBasis k)
          (gradient k) ≤ ε) →
      nullSpaceStepTwoAcceptanceCondition
          (incomingSigma k)
          (aPseudoInverse k)
          (gradient k)
          (hessianApproximation k)
          (dHat k)
          ρ →
        stageSigma k = incomingSigma k
  stageSigma_eq_reset_of_not_stepTwoAccepts :
    ∀ k : ℕ, 1 ≤ k →
      ¬ (nullSpaceStoppingResidual
          (constraintResidual k)
          (nullSpaceBasis k)
          (gradient k) ≤ ε) →
      ¬ nullSpaceStepTwoAcceptanceCondition
            (incomingSigma k)
            (aPseudoInverse k)
            (gradient k)
            (hessianApproximation k)
            (dHat k)
            ρ →
        stageSigma k =
          nullSpacePenaltyUpdate
            (aPseudoInverse k)
            (gradient k)
            (hessianApproximation k)
            (dHat k)
            ρ
  trialStepCondition_of_not_terminated :
    ∀ k : ℕ, 1 ≤ k →
      ¬ (nullSpaceStoppingResidual
          (constraintResidual k)
          (nullSpaceBasis k)
          (gradient k) ≤ ε) →
        nullSpaceTrialStepCondition
          (nullSpacePredictedReduction
            (predictedModel k)
            (trialStep k))
          ρ₁
          ρ₂
          (constraintResidual k)
          (nullSpaceBasis k)
          (gradient k)
          (radius k)
          (aPseudoInverse k)
          (hessianApproximation k)
          (dHat k)
  actualReduction_spec_of_not_terminated :
    ∀ k : ℕ, 1 ≤ k →
      ¬ (nullSpaceStoppingResidual
          (constraintResidual k)
          (nullSpaceBasis k)
          (gradient k) ≤ ε) →
        actualReduction k =
          TrustRegionSubproblem.actualReduction
            (iterate k)
            penaltyFunction
            (trialStep k)
  predictedReduction_spec_of_not_terminated :
    ∀ k : ℕ, 1 ≤ k →
      ¬ (nullSpaceStoppingResidual
          (constraintResidual k)
          (nullSpaceBasis k)
          (gradient k) ≤ ε) →
        predictedReduction k =
          nullSpacePredictedReduction
            (predictedModel k)
            (trialStep k)
  ratio_eq_of_not_terminated :
    ∀ k : ℕ, 1 ≤ k →
      ¬ (nullSpaceStoppingResidual
          (constraintResidual k)
          (nullSpaceBasis k)
          (gradient k) ≤ ε) →
        ratio k = actualReduction k / predictedReduction k
  iterate_succ_of_not_terminated :
    ∀ k : ℕ, 1 ≤ k →
      ¬ (nullSpaceStoppingResidual
          (constraintResidual k)
          (nullSpaceBasis k)
          (gradient k) ≤ ε) →
        iterate (k + 1) =
          nullSpaceAcceptedPoint
            β₀
            (iterate k)
            (trialStep k)
            (ratio k)
  radius_succ_spec_of_not_terminated :
    ∀ k : ℕ, 1 ≤ k →
      ¬ (nullSpaceStoppingResidual
          (constraintResidual k)
          (nullSpaceBasis k)
          (gradient k) ≤ ε) →
        nullSpaceRadiusUpdateCondition
            β₁
            β₂
            β₃
            β₄
            (radius k)
            (trialStep k)
            (ratio k)
            (radius (k + 1))
  incomingSigma_succ_of_not_terminated :
    ∀ k : ℕ, 1 ≤ k →
      ¬ (nullSpaceStoppingResidual
          (constraintResidual k)
          (nullSpaceBasis k)
          (gradient k) ≤ ε) →
        incomingSigma (k + 1) = stageSigma k

namespace NullSpaceTrustRegionMethod

/-- A `NullSpaceTrustRegionMethod` can be evaluated as its iterate sequence `k ↦ x_k`. -/
instance instCoeFun :
    CoeFun (NullSpaceTrustRegionMethod ambientDim constraintDim tangentDim)
      (fun _ ↦ ℕ → Point) where
  coe method := method.iterate

/-- Evaluating a null-space trust-region method as a function returns its iterate sequence. -/
theorem coe_apply
    (method : NullSpaceTrustRegionMethod ambientDim constraintDim tangentDim) (k : ℕ) :
    method k = method.iterate k :=
  rfl

/-- The recorded reduced gradient at stage `k` is the source quantity `Z_kᵀ g_k`. -/
def reducedGradientAt
    (method : NullSpaceTrustRegionMethod ambientDim constraintDim tangentDim) (k : ℕ) :
    TangentPoint :=
  nullSpaceReducedGradient (method.nullSpaceBasis k) (method.gradient k)

/-- The source stopping test at stage `k` is `‖c_k‖₂ + ‖Z_kᵀ g_k‖₂ ≤ ε`. -/
def terminatedAt
    (method : NullSpaceTrustRegionMethod ambientDim constraintDim tangentDim) (k : ℕ) :
    Prop :=
  nullSpaceStoppingResidual
      (method.constraintResidual k)
      (method.nullSpaceBasis k)
      (method.gradient k) ≤
    method.ε

/-- Unfolding `method.terminatedAt k` gives the source Step-2 stopping inequality. -/
theorem terminatedAt_iff
    (method : NullSpaceTrustRegionMethod ambientDim constraintDim tangentDim) (k : ℕ) :
    method.terminatedAt k ↔
      nullSpaceStoppingResidual
          (method.constraintResidual k)
          (method.nullSpaceBasis k)
          (method.gradient k) ≤
        method.ε :=
  Iff.rfl

/-- The recorded Step-2 test at stage `k` is the concrete acceptance inequality `(13.4.24)`. -/
def stepTwoAcceptsAt
    (method : NullSpaceTrustRegionMethod ambientDim constraintDim tangentDim) (k : ℕ) :
    Prop :=
  nullSpaceStepTwoAcceptanceCondition
    (method.incomingSigma k)
    (method.aPseudoInverse k)
    (method.gradient k)
    (method.hessianApproximation k)
    (method.dHat k)
    method.ρ

/-- Unfolding `method.stepTwoAcceptsAt k` gives the recorded Step-2 condition `(13.4.24)`. -/
theorem stepTwoAcceptsAt_iff
    (method : NullSpaceTrustRegionMethod ambientDim constraintDim tangentDim) (k : ℕ) :
    method.stepTwoAcceptsAt k ↔
      nullSpaceStepTwoAcceptanceCondition
        (method.incomingSigma k)
        (method.aPseudoInverse k)
        (method.gradient k)
        (method.hessianApproximation k)
        (method.dHat k)
        method.ρ :=
  Iff.rfl

/-- The accepted point at stage `k` is the source update `(13.4.28)` applied to
`(x_k, d_k, r_k)`. -/
def acceptedPointAt
    (method : NullSpaceTrustRegionMethod ambientDim constraintDim tangentDim) (k : ℕ) :
    Point :=
  nullSpaceAcceptedPoint
    method.β₀
    (method.iterate k)
    (method.trialStep k)
    (method.ratio k)

/-- Unfolding `method.acceptedPointAt k` gives the source accepted-point formula `(13.4.28)`. -/
theorem acceptedPointAt_eq
    (method : NullSpaceTrustRegionMethod ambientDim constraintDim tangentDim) (k : ℕ) :
    method.acceptedPointAt k =
      nullSpaceAcceptedPoint
        method.β₀
        (method.iterate k)
        (method.trialStep k)
        (method.ratio k) :=
  rfl

/-- The stored Step-4 radius choice at stage `k` is exactly the source condition `(13.4.29)`. -/
def nextRadiusConditionAt
    (method : NullSpaceTrustRegionMethod ambientDim constraintDim tangentDim) (k : ℕ) :
    Prop :=
  nullSpaceRadiusUpdateCondition
    method.β₁
    method.β₂
    method.β₃
    method.β₄
    (method.radius k)
    (method.trialStep k)
    (method.ratio k)
    (method.radius (k + 1))

/-- Unfolding `method.nextRadiusConditionAt k` gives the source radius-choice rule `(13.4.29)`
for `Δ_(k+1)`. -/
theorem nextRadiusConditionAt_iff
    (method : NullSpaceTrustRegionMethod ambientDim constraintDim tangentDim) (k : ℕ) :
    method.nextRadiusConditionAt k ↔
      nullSpaceRadiusUpdateCondition
        method.β₁
        method.β₂
        method.β₃
        method.β₄
        (method.radius k)
        (method.trialStep k)
        (method.ratio k)
        (method.radius (k + 1)) :=
  Iff.rfl

/-- At a nonterminal stage `k ≥ 1`, the recorded trial step `d_k` satisfies the source Step-3
condition `(13.4.27)` through the predicted reduction of that same step. -/
theorem trialStepCondition_at
    (method : NullSpaceTrustRegionMethod ambientDim constraintDim tangentDim)
    {k : ℕ} (hk : 1 ≤ k) (h_not_term : ¬ method.terminatedAt k) :
    nullSpaceTrialStepCondition
      (nullSpacePredictedReduction
        (method.predictedModel k)
        (method.trialStep k))
      method.ρ₁
      method.ρ₂
      (method.constraintResidual k)
      (method.nullSpaceBasis k)
      (method.gradient k)
      (method.radius k)
      (method.aPseudoInverse k)
      (method.hessianApproximation k)
      (method.dHat k) :=
  method.trialStepCondition_of_not_terminated k hk h_not_term

/-- At a nonterminal stage `k ≥ 1`, the recorded `Ared_k` satisfies the source formula
`(13.4.16)`. -/
theorem actualReduction_spec_at
    (method : NullSpaceTrustRegionMethod ambientDim constraintDim tangentDim)
    {k : ℕ} (hk : 1 ≤ k) (h_not_term : ¬ method.terminatedAt k) :
    method.actualReduction k =
      TrustRegionSubproblem.actualReduction
        (method.iterate k)
        method.penaltyFunction
        (method.trialStep k) :=
  method.actualReduction_spec_of_not_terminated k hk h_not_term

/-- At a nonterminal stage `k ≥ 1`, the recorded `Pred_k` satisfies the source formula
`(13.4.17)`. -/
theorem predictedReduction_spec_at
    (method : NullSpaceTrustRegionMethod ambientDim constraintDim tangentDim)
    {k : ℕ} (hk : 1 ≤ k) (h_not_term : ¬ method.terminatedAt k) :
    method.predictedReduction k =
      nullSpacePredictedReduction
        (method.predictedModel k)
        (method.trialStep k) :=
  method.predictedReduction_spec_of_not_terminated k hk h_not_term

/-- At a nonterminal stage `k ≥ 1`, the recorded ratio is the Step-4 quotient
`Ared_k / Pred_k`. -/
theorem ratio_eq_at
    (method : NullSpaceTrustRegionMethod ambientDim constraintDim tangentDim)
    {k : ℕ} (hk : 1 ≤ k) (h_not_term : ¬ method.terminatedAt k) :
    method.ratio k = method.actualReduction k / method.predictedReduction k :=
  method.ratio_eq_of_not_terminated k hk h_not_term

end NullSpaceTrustRegionMethod

end
