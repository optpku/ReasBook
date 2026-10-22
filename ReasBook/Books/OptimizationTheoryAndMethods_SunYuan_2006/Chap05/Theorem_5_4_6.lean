/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Assumption_5_4_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_3
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Order.Filter.Basic

noncomputable section

open Filter
open scoped Matrix.Norms.L2Operator

section Chapter05Theorem546

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

-- Domain sampling:
-- * primary domain: local quasi-Newton superlinear convergence for smooth objectives on the
--   Euclidean matrix model of `ℝ^n`.
-- * sampled owner declarations in this domain:
--   `quasiNewtonSecantErrorRatio` from `Theorem_5_4_3`,
--   `HasQSuperlinearConvergenceTo` from `Chapter01.Definition_1_5_extra_1`,
--   `quasiNewtonHessianMatrix` from `Assumption_5_4_2`,
--   `Matrix.toEuclideanLin` / `Matrix.toEuclideanCLM` for the concrete matrix action bridge.
-- * best owner abstraction: `quasiNewtonSecantErrorRatio` is the core/canonical secant-error
--   owner; the Hessian-side ratio below is only a source-facing matrix-model bridge/view.
-- * primitive data for the theorem: the objective `f`, the Assumption 5.4.2 package `h`, the
--   Hessian-approximation sequence `B`, the iterate sequence `x`, and the quasi-Newton update.
-- * derived API: the Hessian-side secant-error ratio expressed by reusing the canonical owner
--   from `Theorem_5_4_3`.

/-- The Hessian-side secant-error ratio
`‖(B k - quasiNewtonHessianMatrix f xStar) (x (k + 1) - x k)‖ / ‖x (k + 1) - x k‖`,
presented as the Euclidean matrix-model view of the canonical secant-error owner
`quasiNewtonSecantErrorRatio` from `Theorem_5_4_3`. -/
abbrev quasiNewtonHessianSecantErrorRatio
    (f : Point → ℝ)
    (xStar : Point)
    (B : ℕ → MatrixN)
    (x : ℕ → Point) : ℕ → ℝ :=
  quasiNewtonSecantErrorRatio (gradient f) xStar
    (fun k ↦
      (Matrix.toEuclideanCLM : MatrixN ≃⋆ₐ[ℝ] Point →L[ℝ] Point) (B k))
    x

/-- `quasiNewtonHessianSecantErrorRatio` is exactly the Chapter 5 matrix-model specialization of
the canonical secant-error owner `quasiNewtonSecantErrorRatio`. -/
@[simp] theorem quasiNewtonHessianSecantErrorRatio_eq_secantErrorRatio
    (f : Point → ℝ)
    (xStar : Point)
    (B : ℕ → MatrixN)
    (x : ℕ → Point) :
    quasiNewtonHessianSecantErrorRatio f xStar B x =
      quasiNewtonSecantErrorRatio (gradient f) xStar
        (fun k ↦
          (Matrix.toEuclideanCLM : MatrixN ≃⋆ₐ[ℝ] Point →L[ℝ] Point) (B k))
        x :=
  rfl

/-- Evaluating `quasiNewtonHessianSecantErrorRatio f xStar B x` at `k` returns the textbook
ratio on the step `x (k + 1) - x k`. -/
@[simp] theorem quasiNewtonHessianSecantErrorRatio_apply
    (f : Point → ℝ)
    (xStar : Point)
    (B : ℕ → MatrixN)
    (x : ℕ → Point)
    (k : ℕ) :
    quasiNewtonHessianSecantErrorRatio f xStar B x k =
      ‖Matrix.toEuclideanLin
          (B k - quasiNewtonHessianMatrix f xStar) (x (k + 1) - x k)‖ /
        ‖x (k + 1) - x k‖ := by
  rw [quasiNewtonHessianSecantErrorRatio_eq_secantErrorRatio, quasiNewtonSecantErrorRatio_apply]
  have hHessian :
      (Matrix.toEuclideanCLM : MatrixN ≃⋆ₐ[ℝ] Point →L[ℝ] Point)
          (quasiNewtonHessianMatrix f xStar) =
        fderiv ℝ (gradient f) xStar := by
    rw [quasiNewtonHessianMatrix_eq]
    simp [hessianAt]
  have hCLM :
      (Matrix.toEuclideanCLM : MatrixN ≃⋆ₐ[ℝ] Point →L[ℝ] Point)
          (B k - quasiNewtonHessianMatrix f xStar) =
        (Matrix.toEuclideanCLM : MatrixN ≃⋆ₐ[ℝ] Point →L[ℝ] Point) (B k) -
          fderiv ℝ (gradient f) xStar := by
    rw [map_sub, hHessian]
  rw [← hCLM]
  simpa using
    congrArg
      (fun T : Point →ₗ[ℝ] Point ↦ ‖T (x (k + 1) - x k)‖ / ‖x (k + 1) - x k‖)
      (Matrix.coe_toEuclideanCLM_eq_toEuclideanLin (B k - quasiNewtonHessianMatrix f xStar))

/-- Chapter05 Theorem 5.4.6: let `f : ℝ^n → ℝ` satisfy
`HasQuasiNewtonStrongLocalMinimizerAssumptions D f`. Consider the quasi-Newton iteration
`x (k + 1) = x k - B k⁻¹ ∇f(x k)`, where the Hessian approximations `B k` are positive
definite. If `x` converges to the limit
point `h.xStar`, then `x` converges to `h.xStar` `Q`-superlinearly exactly when the Hessian-side
secant-error ratio
`‖(B k - quasiNewtonHessianMatrix f h.xStar) (x (k + 1) - x k)‖ / ‖x (k + 1) - x k‖`
tends to `0`. -/
theorem quasiNewton_superlinear_iff_hessianSecantErrorRatio_tendsto_zero
    {D : Set Point}
    (f : Point → ℝ)
    (h : HasQuasiNewtonStrongLocalMinimizerAssumptions D f)
    (B : ℕ → MatrixN)
    (x : ℕ → Point)
    (hB_posDef : ∀ k : ℕ, (B k).PosDef)
    (h_update :
      ∀ k : ℕ, x (k + 1) = x k - Matrix.toEuclideanLin ((B k)⁻¹) (gradient f (x k)))
    (hx : Tendsto x atTop (nhds h.xStar)) :
    HasQSuperlinearConvergenceTo x h.xStar ↔
      Tendsto (quasiNewtonHessianSecantErrorRatio f h.xStar B x) atTop (nhds 0) := sorry

end Chapter05Theorem546
