/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_3
import Mathlib.Analysis.CStarAlgebra.Matrix

noncomputable section

open Filter
open scoped Matrix.Norms.L2Operator

section Chapter05Theorem544

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

-- Source/core/bridge triage:
-- * `HasScaledQuasiNewtonLocalAssumptions` is the source-facing weak local theory from
--   Theorem 5.4.4, which intentionally does not assume `F xStar = 0`.
-- * `HasQuasiNewtonLocalConvergenceAssumptions` from Assumption 5.4.1 remains the stronger
--   Chapter 5 core owner, recovered here by a thin bridge when `F xStar = 0`.
-- * `ScaledQuasiNewtonSetup` is the source-facing iteration data for the damped update
--   `x (k + 1) = x k - α k • BInv k (F (x k))`.

/-- Chapter05 Theorem 5.4.4 uses the same local differentiability, convexity, invertibility, and
derivative-Lipschitz hypotheses as Theorem 5.4.3, but it does not assume in advance that the
distinguished limit point is a zero of `F`. -/
structure HasScaledQuasiNewtonLocalAssumptions
    (D : Set Point) (F : Point → Point) where
  open_domain : IsOpen D
  convex_domain : Convex ℝ D
  contDiffOn : ContDiffOn ℝ 1 F D
  xStar : Point
  xStar_mem : xStar ∈ D
  fderiv_isInvertible : (fderiv ℝ F xStar).IsInvertible
  gamma : ℝ
  lipschitz_fderiv :
    ∀ x ∈ D, ‖fderiv ℝ F x - fderiv ℝ F xStar‖ ≤ gamma * ‖x - xStar‖

namespace HasScaledQuasiNewtonLocalAssumptions

/-- Source-semantic expansion of `HasScaledQuasiNewtonLocalAssumptions D F`. -/
theorem spec
    {D : Set Point} {F : Point → Point}
    (h : HasScaledQuasiNewtonLocalAssumptions D F) :
    IsOpen D ∧
      Convex ℝ D ∧
      ContDiffOn ℝ 1 F D ∧
      h.xStar ∈ D ∧
      (fderiv ℝ F h.xStar).IsInvertible ∧
      ∀ x ∈ D, ‖fderiv ℝ F x - fderiv ℝ F h.xStar‖ ≤ h.gamma * ‖x - h.xStar‖ := by
  exact ⟨h.open_domain, h.convex_domain, h.contDiffOn, h.xStar_mem, h.fderiv_isInvertible,
    h.lipschitz_fderiv⟩

/-- When the weak local theory also satisfies `F xStar = 0`, it canonically upgrades to the
stronger owner `HasQuasiNewtonLocalConvergenceAssumptions D F` used in Theorem 5.4.3. -/
def toHasQuasiNewtonLocalConvergenceAssumptions
    {D : Set Point} {F : Point → Point}
    (h : HasScaledQuasiNewtonLocalAssumptions D F)
    (h_map_xStar : F h.xStar = 0) :
    HasQuasiNewtonLocalConvergenceAssumptions D F where
  open_domain := h.open_domain
  convex_domain := h.convex_domain
  contDiffOn := h.contDiffOn
  xStar := h.xStar
  xStar_mem := h.xStar_mem
  map_xStar := h_map_xStar
  fderiv_isInvertible := h.fderiv_isInvertible
  gamma := h.gamma
  lipschitz_fderiv := h.lipschitz_fderiv

end HasScaledQuasiNewtonLocalAssumptions

/-- A scaled quasi-Newton run on `D` records the Jacobian approximations `B k`, chosen inverses
`BInv k`, step sizes `α k`, iterate sequence `x`, the inverse identities for `B k`, and the
source update `x (k + 1) = x k - α k • BInv k (F (x k))`. -/
structure ScaledQuasiNewtonSetup
    (F : Point → Point) (D : Set Point) where
  B : ℕ → Point →L[ℝ] Point
  BInv : ℕ → Point →L[ℝ] Point
  α : ℕ → ℝ
  x : ℕ → Point
  leftInverse : ∀ k : ℕ, Function.LeftInverse (BInv k) (B k)
  rightInverse : ∀ k : ℕ, Function.RightInverse (BInv k) (B k)
  update : ∀ k : ℕ, x (k + 1) = x k - α k • BInv k (F (x k))
  iterates_mem : ∀ k : ℕ, x k ∈ D

namespace ScaledQuasiNewtonSetup

/-- The Euclidean matrix-model representative of the operator approximation `A.B k`. This is a
thin source-facing bridge from the scaled quasi-Newton owner to the Chapter 5 matrix surface. -/
abbrev matrix
    {F : Point → Point} {D : Set Point}
    (A : ScaledQuasiNewtonSetup F D) (k : ℕ) : MatrixN :=
  (Matrix.toEuclideanCLM : MatrixN ≃⋆ₐ[ℝ] Point →L[ℝ] Point).symm (A.B k)

/-- Passing `A.matrix k` through `Matrix.toEuclideanCLM` recovers the intrinsic operator
approximation `A.B k`. -/
@[simp] theorem matrix_toEuclideanCLM
    {F : Point → Point} {D : Set Point}
    (A : ScaledQuasiNewtonSetup F D) (k : ℕ) :
    (Matrix.toEuclideanCLM : MatrixN ≃⋆ₐ[ℝ] Point →L[ℝ] Point) (A.matrix k) = A.B k := by
  simp [ScaledQuasiNewtonSetup.matrix]

/-- Passing `A.matrix k` through `Matrix.toEuclideanLin` recovers the intrinsic operator
approximation `A.B k` on the underlying linear-map surface. -/
@[simp] theorem matrix_toEuclideanLin
    {F : Point → Point} {D : Set Point}
    (A : ScaledQuasiNewtonSetup F D) (k : ℕ) :
    (A.matrix k).toEuclideanLin = A.B k := by
  rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]
  exact congrArg (fun T : Point →L[ℝ] Point ↦ (T : Point →ₗ[ℝ] Point))
    (A.matrix_toEuclideanCLM k)

/-- Source-semantic expansion of `ScaledQuasiNewtonSetup F D`. -/
theorem spec
    {F : Point → Point} {D : Set Point}
    (A : ScaledQuasiNewtonSetup F D) :
    (∀ k : ℕ, Function.LeftInverse (A.BInv k) (A.B k)) ∧
      (∀ k : ℕ, Function.RightInverse (A.BInv k) (A.B k)) ∧
      (∀ k : ℕ, A.x (k + 1) = A.x k - A.α k • A.BInv k (F (A.x k))) ∧
      ∀ k : ℕ, A.x k ∈ D := by
  exact ⟨A.leftInverse, A.rightInverse, A.update, A.iterates_mem⟩

/-- Each `A.B k` in a scaled quasi-Newton run is invertible with inverse `A.BInv k`. -/
theorem B_isInvertible
    {F : Point → Point} {D : Set Point}
    (A : ScaledQuasiNewtonSetup F D) (k : ℕ) :
    (A.B k).IsInvertible := by
  exact ContinuousLinearMap.IsInvertible.of_inverse
    (show A.B k ∘L A.BInv k = ContinuousLinearMap.id ℝ Point by
      ext x i
      simpa using congrArg (fun y : Point ↦ y i) (A.rightInverse k x))
    (show A.BInv k ∘L A.B k = ContinuousLinearMap.id ℝ Point by
      ext x i
      simpa using congrArg (fun y : Point ↦ y i) (A.leftInverse k x))

end ScaledQuasiNewtonSetup

/-- Chapter05 Theorem 5.4.4 (1): let `F : ℝ^n → ℝ^n` satisfy the weak local hypotheses recorded
by `HasScaledQuasiNewtonLocalAssumptions D F`, and let `A` be a scaled quasi-Newton run on `D`
with update `A.x (k + 1) = A.x k - A.α k • A.BInv k (F (A.x k))`. If `A.x` converges to the
distinguished point `h.xStar` and the secant-error condition `(5.4.4)` holds, then `A.x`
converges to `h.xStar` `Q`-superlinearly. -/
theorem quasiNewton_superlinear_of_secantErrorRatio_tendsto_zero
    {D : Set Point}
    (F : Point → Point)
    (h : HasScaledQuasiNewtonLocalAssumptions D F)
    (A : ScaledQuasiNewtonSetup F D)
    (hx : Tendsto A.x atTop (nhds h.xStar))
    (h_secantError :
      Tendsto (quasiNewtonSecantErrorRatio F h.xStar A.B A.x) atTop (nhds 0)) :
    HasQSuperlinearConvergenceTo A.x h.xStar := sorry

/-- Chapter05 Theorem 5.4.4 (2): under the same scaled quasi-Newton hypotheses and secant-error
condition, the distinguished limit point is a zero of `F` exactly when the step sizes converge
to `1`. -/
theorem quasiNewton_zero_iff_stepsizes_tendsto_one
    {D : Set Point}
    (F : Point → Point)
    (h : HasScaledQuasiNewtonLocalAssumptions D F)
    (A : ScaledQuasiNewtonSetup F D)
    (hx : Tendsto A.x atTop (nhds h.xStar))
    (h_secantError :
      Tendsto (quasiNewtonSecantErrorRatio F h.xStar A.B A.x) atTop (nhds 0)) :
    F h.xStar = 0 ↔ Tendsto A.α atTop (nhds 1) := sorry

end Chapter05Theorem544
