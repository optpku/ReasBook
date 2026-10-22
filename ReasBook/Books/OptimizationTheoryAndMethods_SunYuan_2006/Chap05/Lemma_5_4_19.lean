/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Algorithm_5_1_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Assumption_5_4_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_1_extra_4
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.Normed
import Mathlib
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section

section Chapter05Lemma5419

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

open scoped Matrix.Norms.Frobenius
open scoped Matrix.Norms.L2Operator
open scoped MatrixOrder

-- This file reuses the source-facing Assumption 5.4.2 owner from
-- `SunYuanOptimizationTheoryMethods.Chap05.Assumption_5_4_2`.
-- Semantic recall: `lean_leansearch` exposed `Matrix.PosDef.posDef_sqrt` and
-- `Matrix.PosSemidef.inv_sqrt`, so the source-faithful Hessian `±1 / 2` weights are expressed
-- through `CFC.sqrt`.

/-- The Hessian-side DFP update
`B + (sᵀ y)⁻¹ • y yᵀ - (sᵀ B s)⁻¹ • (B s) (B s)ᵀ`, reusing the canonical Chapter 5
Hessian-update owner `bfgsHessianUpdate`. -/
abbrev dfpHessianUpdate
    (B : MatrixN) (s y : Point) : MatrixN :=
  bfgsHessianUpdate B s y

/-- The DFP Hessian-side update name is a source-facing bridge to the canonical Chapter 5
owner `bfgsHessianUpdate`. -/
@[simp] theorem dfpHessianUpdate_eq_bfgsHessianUpdate
    (B : MatrixN) (s y : Point) :
    dfpHessianUpdate B s y = bfgsHessianUpdate B s y :=
  rfl

/-- The reference Hessian `∇²f(x*)` used in the local DFP estimates. -/
def dfpReferenceHessian
    {D : Set Point} {f : Point → ℝ}
    (h : HasQuasiNewtonStrongLocalMinimizerAssumptions D f) : MatrixN :=
  quasiNewtonHessianMatrix f h.xStar

/-- The inverse-weighted Frobenius-type DFP matrix norm
`‖E‖_{DFP,A} = ‖A⁻¹ * E * A⁻¹‖` used in Chapter05 Theorem 5.4.15. -/
def dfpMatrixNorm (A E : MatrixN) : ℝ :=
  ‖(((A⁻¹) * E * (A⁻¹)) : MatrixN)‖

/-- The square-root-weighted Frobenius-type DFP matrix norm
`‖E‖_{DFP,sqrt,A} = ‖A^{-1 / 2} * E * A^{-1 / 2}‖` used in the `(5.4.123)` estimate. -/
def dfpSqrtWeightedMatrixNorm (A E : MatrixN) : ℝ :=
  ‖((((CFC.sqrt A)⁻¹) * E * ((CFC.sqrt A)⁻¹)) : MatrixN)‖

/-- The local error size `σ(x, xNext) = max {‖x - x*‖, ‖xNext - x*‖}`. -/
def dfpSigma (x xNext xStar : Point) : ℝ :=
  max ‖x - xStar‖ ‖xNext - xStar‖

/-- The neighborhood form of `(5.4.83)` from Chapter05 Theorem 5.4.15: with
`μ = ‖(dfpReferenceHessian h)⁻¹‖`, one has
`μ * h.γ * dfpSigma x xNext h.xStar ≤ 1 / 3` for all `x`, `xNext` in some ball about
`h.xStar`. -/
def dfpOneThirdConditionInNeighborhood
    {D : Set Point} {f : Point → ℝ}
    (h : HasQuasiNewtonStrongLocalMinimizerAssumptions D f) : Prop :=
  ∃ ρ > 0, ∀ x xNext,
    x ∈ Metric.ball h.xStar ρ →
    xNext ∈ Metric.ball h.xStar ρ →
      ‖(dfpReferenceHessian h)⁻¹‖ * h.γ * dfpSigma x xNext h.xStar ≤ (1 / 3 : ℝ)

/-- The exact-ball form of `(5.4.83)` on the distinguished ball `Metric.ball h.xStar h.ε`:
`‖(dfpReferenceHessian h)⁻¹‖ * h.γ * dfpSigma x xNext h.xStar ≤ 1 / 3`. -/
def dfpOneThirdConditionOnBall
    {D : Set Point} {f : Point → ℝ}
    (h : HasQuasiNewtonStrongLocalMinimizerAssumptions D f) : Prop :=
  ∀ x xNext,
    x ∈ Metric.ball h.xStar h.ε →
    xNext ∈ Metric.ball h.xStar h.ε →
      ‖(dfpReferenceHessian h)⁻¹‖ * h.γ * dfpSigma x xNext h.xStar ≤ (1 / 3 : ℝ)

/-- The exact-ball one-third condition implies the Chapter05 Theorem 5.4.15 neighborhood
one-third condition. -/
theorem dfpOneThirdConditionInNeighborhood_of_onBall
    {D : Set Point} {f : Point → ℝ}
    {h : HasQuasiNewtonStrongLocalMinimizerAssumptions D f}
    (h_ball : dfpOneThirdConditionOnBall h) :
    dfpOneThirdConditionInNeighborhood h := sorry

/-- A Hessian-side DFP run on `D` for `f` consists of iterates `x k`, Hessian approximations
`B k`, and explicit gradients `g k`, with every iterate in `D`, positive definite Hessian
approximations, the full DFP step relation `x (k + 1) = x k - B k⁻¹ g k`, and the DFP
Hessian update at every stage. The canonical Chapter 5 owner remains
`GeneralQuasiNewtonMethod`; this structure is the source-facing Hessian-side matrix bridge. -/
structure DFPHessianRun
    (D : Set Point) (f : Point → ℝ) where
  B0 : MatrixN
  x : ℕ → Point
  B : ℕ → MatrixN
  g : ℕ → Point
  B_zero : B 0 = B0
  iterates_mem : ∀ k : ℕ, x k ∈ D
  hasGradientAt : ∀ k : ℕ, HasGradientAt f (g k) (x k)
  matrices_posDef : ∀ k : ℕ, (B k).PosDef
  step_eq : ∀ k : ℕ, x (k + 1) = x k - Matrix.toEuclideanLin ((B k)⁻¹) (g k)
  secant_curvature_pos :
    ∀ k : ℕ, 0 < dotProduct (x (k + 1) - x k) (g (k + 1) - g k)
  dfp_update :
    ∀ k : ℕ,
      B (k + 1) =
        dfpHessianUpdate (B k) (x (k + 1) - x k) (g (k + 1) - g k)

attribute [simp] DFPHessianRun.B_zero

/-- A Hessian-side DFP run can be used as its iterate sequence `x`. -/
instance instCoeFunDFPHessianRun
    {D : Set Point} {f : Point → ℝ} :
    CoeFun (DFPHessianRun D f) (fun _ ↦ ℕ → Point) where
  coe A := A.x

namespace DFPHessianRun

/-- Evaluating a Hessian-side DFP run as a function returns its iterate sequence. -/
@[simp] theorem coe_apply
    {D : Set Point} {f : Point → ℝ}
    (A : DFPHessianRun D f) (k : ℕ) :
    A k = A.x k :=
  rfl

/-- The initial iterate of a Hessian-side DFP run. -/
abbrev x0
    {D : Set Point} {f : Point → ℝ} (A : DFPHessianRun D f) : Point :=
  A 0

/-- The secant-curvature condition forces every DFP step to be nonzero. -/
theorem step_ne_zero
    {D : Set Point} {f : Point → ℝ}
    (A : DFPHessianRun D f) (k : ℕ) :
    A.x (k + 1) - A.x k ≠ 0 := by
  intro hstep_zero
  have hcurvature_ne :
      dotProduct (A.x (k + 1) - A.x k) (A.g (k + 1) - A.g k) ≠ 0 :=
    ne_of_gt (A.secant_curvature_pos k)
  exact hcurvature_ne (by simp [hstep_zero])

/-- Positive-definite Hessian approximations make the DFP step quadratic form positive. -/
theorem step_quadratic_pos
    {D : Set Point} {f : Point → ℝ}
    (A : DFPHessianRun D f) (k : ℕ) :
    0 < dotProduct
      (A.x (k + 1) - A.x k) (Matrix.toEuclideanLin (A.B k) (A.x (k + 1) - A.x k)) := by
  have hstep_ne : (A.x (k + 1)).ofLp - (A.x k).ofLp ≠ 0 := by
    intro hstep_zero
    apply A.step_ne_zero k
    simpa using congrArg (WithLp.toLp 2) hstep_zero
  change 0 <
    dotProduct
      ((A.x (k + 1)).ofLp - (A.x k).ofLp)
      ((A.B k).mulVec ((A.x (k + 1)).ofLp - (A.x k).ofLp))
  exact (A.matrices_posDef k).dotProduct_mulVec_pos hstep_ne

/-- Every DFP stage carries the iterate, gradient, positivity, step, curvature, quadratic, and
update data recorded in `DFPHessianRun D f`. -/
theorem stepSpec
    {D : Set Point} {f : Point → ℝ}
    (A : DFPHessianRun D f) (k : ℕ) :
    A.x k ∈ D ∧
      HasGradientAt f (A.g k) (A.x k) ∧
      (A.B k).PosDef ∧
      A.x (k + 1) = A.x k - Matrix.toEuclideanLin ((A.B k)⁻¹) (A.g k) ∧
      0 < dotProduct (A.x (k + 1) - A.x k) (A.g (k + 1) - A.g k) ∧
      0 < dotProduct
        (A.x (k + 1) - A.x k) (Matrix.toEuclideanLin (A.B k) (A.x (k + 1) - A.x k)) ∧
      A.B (k + 1) =
        dfpHessianUpdate (A.B k) (A.x (k + 1) - A.x k) (A.g (k + 1) - A.g k) := by
  exact ⟨A.iterates_mem k, A.hasGradientAt k, A.matrices_posDef k, A.step_eq k,
    A.secant_curvature_pos k, A.step_quadratic_pos k, A.dfp_update k⟩

/-- The canonical inverse-form quasi-Newton view of a Hessian-side DFP run. The iterate and
gradient data are unchanged, the inverse operator is `Matrix.toEuclideanLin ((A.B k)⁻¹)`, and
the full DFP step is recorded as unit step size in `GeneralQuasiNewtonMethod`. -/
abbrev toGeneralQuasiNewtonMethod
    {D : Set Point} {f : Point → ℝ} (A : DFPHessianRun D f) :
    GeneralQuasiNewtonMethod f :=
  { ε := 0
    x := A.x
    H := fun k ↦ Matrix.toEuclideanLin ((A.B k)⁻¹)
    g := A.g
    d := fun k ↦ -Matrix.toEuclideanLin ((A.B k)⁻¹) (A.g k)
    α := fun _ ↦ 1
    epsilon_nonneg := le_rfl
    hasGradientAt := A.hasGradientAt
    direction_eq := fun k _ ↦ rfl
    stepSize_pos := fun _ _ ↦ zero_lt_one
    update := fun k _ ↦ by
      change A.x (k + 1) = A.x k + (1 : ℝ) • (-Matrix.toEuclideanLin ((A.B k)⁻¹) (A.g k))
      simpa [sub_eq_add_neg] using A.step_eq k
    stationaryContinuation := fun k hk ↦ by
      have hg_norm : ‖A.g k‖ = 0 := le_antisymm hk (norm_nonneg _)
      have hg : A.g k = 0 := norm_eq_zero.mp hg_norm
      simpa [hg] using A.step_eq k
    quasiNewtonEquation := fun _ _ ↦ by
      sorry }

@[simp] theorem toGeneralQuasiNewtonMethod_coe_apply
    {D : Set Point} {f : Point → ℝ}
    (A : DFPHessianRun D f) (k : ℕ) :
    A.toGeneralQuasiNewtonMethod k = A k :=
  rfl

@[simp] theorem toGeneralQuasiNewtonMethod_g
    {D : Set Point} {f : Point → ℝ}
    (A : DFPHessianRun D f) (k : ℕ) :
    A.toGeneralQuasiNewtonMethod.g k = A.g k :=
  rfl

@[simp] theorem toGeneralQuasiNewtonMethod_d
    {D : Set Point} {f : Point → ℝ}
    (A : DFPHessianRun D f) (k : ℕ) :
    A.toGeneralQuasiNewtonMethod.d k = -Matrix.toEuclideanLin ((A.B k)⁻¹) (A.g k) :=
  rfl

@[simp] theorem toGeneralQuasiNewtonMethod_α
    {D : Set Point} {f : Point → ℝ}
    (A : DFPHessianRun D f) (k : ℕ) :
    A.toGeneralQuasiNewtonMethod.α k = 1 :=
  rfl

@[simp] theorem toGeneralQuasiNewtonMethod_matrix
    {D : Set Point} {f : Point → ℝ}
    (A : DFPHessianRun D f) (k : ℕ) :
    A.toGeneralQuasiNewtonMethod.matrix k = (A.B k)⁻¹ := by
  simp [GeneralQuasiNewtonMethod.matrix]

@[simp] theorem toGeneralQuasiNewtonMethod_x0
    {D : Set Point} {f : Point → ℝ}
    (A : DFPHessianRun D f) :
    A.toGeneralQuasiNewtonMethod.x0 = A.x0 :=
  rfl

@[simp] theorem toGeneralQuasiNewtonMethod_matrix0
    {D : Set Point} {f : Point → ℝ}
    (A : DFPHessianRun D f) :
    A.toGeneralQuasiNewtonMethod.matrix0 = (A.B0)⁻¹ := by
  simp [GeneralQuasiNewtonMethod.matrix0]

end DFPHessianRun

/-- The normalized DFP angle `θ` from `(5.4.125)`, namely
`‖A^{-1 / 2} * (B - A) * s‖ / (‖B - A‖_{DFP,A} * ‖A^{1 / 2} * s‖)`, with value `0` when the
denominator vanishes. -/
def dfpErrorAngle (A B : MatrixN) (s : Point) : ℝ :=
  let weightedStep := Matrix.toEuclideanLin (CFC.sqrt A) s
  let denom := dfpSqrtWeightedMatrixNorm A (B - A) * ‖weightedStep‖
  if denom = 0 then 0
  else
    ‖Matrix.toEuclideanLin ((((CFC.sqrt A)⁻¹) * (B - A) * ((CFC.sqrt A)⁻¹) : MatrixN))
        weightedStep‖ /
      denom

/-- Chapter05 Lemma 5.4.19: under the assumptions of Chapter05 Theorem 5.4.15, namely
`HasQuasiNewtonStrongLocalMinimizerAssumptions D f` together with the neighborhood one-third
condition `dfpOneThirdConditionInNeighborhood h`, there exist `ρ > 0` and positive constants
`β₁`, `β₂`, and `β₃` such that every DFP step with
`A.x k, A.x (k + 1) ∈ Metric.ball h.xStar ρ` satisfies the local DFP error contraction
`dfpSqrtWeightedMatrixNorm (dfpReferenceHessian h) (A.B (k + 1) - dfpReferenceHessian h) ≤
  (Real.sqrt (1 - β₁ * dfpErrorAngle (dfpReferenceHessian h) (A.B k) (A.x (k + 1) - A.x k)^2)
      + β₂ * dfpSigma (A.x k) (A.x (k + 1)) h.xStar) *
    dfpSqrtWeightedMatrixNorm (dfpReferenceHessian h) (A.B k - dfpReferenceHessian h) +
  β₃ * dfpSigma (A.x k) (A.x (k + 1)) h.xStar`. -/
theorem exists_local_dfp_error_contraction_constants
    (D : Set Point) (f : Point → ℝ)
    (h : HasQuasiNewtonStrongLocalMinimizerAssumptions D f)
    (h_oneThird : dfpOneThirdConditionInNeighborhood h) :
    ∃ ρ > 0, ∃ β1 > 0, ∃ β2 > 0, ∃ β3 > 0, ∀ (A : DFPHessianRun D f) (k : ℕ),
      A.x k ∈ Metric.ball h.xStar ρ →
      A.x (k + 1) ∈ Metric.ball h.xStar ρ →
        dfpSqrtWeightedMatrixNorm (dfpReferenceHessian h) (A.B (k + 1) - dfpReferenceHessian h) ≤
          (Real.sqrt
              (1 -
                β1 *
                  (dfpErrorAngle (dfpReferenceHessian h) (A.B k) (A.x (k + 1) - A.x k)) ^
                    (2 : ℕ)) +
            β2 * dfpSigma (A.x k) (A.x (k + 1)) h.xStar) *
              dfpSqrtWeightedMatrixNorm (dfpReferenceHessian h) (A.B k - dfpReferenceHessian h) +
            β3 * dfpSigma (A.x k) (A.x (k + 1)) h.xStar := sorry

end Chapter05Lemma5419
