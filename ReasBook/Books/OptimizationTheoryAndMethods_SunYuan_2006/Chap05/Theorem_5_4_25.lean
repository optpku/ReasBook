/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Assumption_5_4_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_3
import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section

open Filter

section Chapter05Theorem5425

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

-- Domain sampling pass:
-- * source-facing layer here: the ratio conditions from `(5.4.135)`-`(5.4.136)`.
-- * core/canonical owners already upstream: `qErrorRatio x xStar 1` for `(5.4.134)` from
--   `Chapter01.Definition_1_5_extra_1`, `quasiNewtonHessianMatrix` for the Hessian owner from
--   `Assumption_5_4_2`, and the angle owner `InnerProductGeometry.angle` with
--   `InnerProductGeometry.cos_angle` for the squared-cosine term in `(5.4.135)`.
-- * matrix action is the mathlib owner `Matrix.toEuclideanLin`, so this file keeps only the
--   genuinely new source-facing curvature ratio from `(5.4.136)`.

/-- The source curvature ratio `(s_kᵀ B_k s_k) / (α_k s_kᵀ y_k)` from `(5.4.136)`, with
`s_k = x_(k + 1) - x_k` and `y_k = g_(k + 1) - g_k`. -/
def quasiNewtonCurvatureRatio
    (x : ℕ → Point) (B : ℕ → MatrixN) (g : ℕ → Point) (α : ℕ → ℝ) : ℕ → ℝ :=
  fun k ↦
    let s : Point := x (k + 1) - x k
    let y : Point := g (k + 1) - g k
    dotProduct s (Matrix.toEuclideanLin (B k) s) / (α k * dotProduct s y)

/-- Chapter05 Theorem 5.4.25: let `x`, `B`, `BInv`, `g`, and `α` be sequences on `ℝ^n` such
that `BInv k` is a chosen inverse for `B k`, `x (k + 1) = x k - α k • BInv k g_k`, and `g k`
is the gradient of `f` at `x k`. Assume the iterates converge to `xStar`, assume
`gradient f xStar = 0`, and assume the Hessian of `f` at `xStar` is the canonical matrix
`quasiNewtonHessianMatrix f xStar`, with the corresponding derivative and positive-definiteness
hypotheses. Assume moreover that the denominators in the source ratios `(5.4.134)`, `(5.4.135)`,
and `(5.4.136)` are eventually nonzero. Then the superlinear error ratio in `(5.4.134)` tends
to `0` if and only if the source angle condition `(5.4.135)` and the source curvature ratio
condition `(5.4.136)` both tend to `1`. -/
theorem quasiNewton_superlinearErrorRatio_tendsto_zero_iff
    (f : Point → ℝ)
    (x : ℕ → Point)
    (B BInv : ℕ → MatrixN)
    (g : ℕ → Point)
    (α : ℕ → ℝ)
    (xStar : Point)
    (h_gradient : ∀ k : ℕ, HasGradientAt f (g k) (x k))
    (h_inverse : ∀ k : ℕ, BInv k * B k = 1 ∧ B k * BInv k = 1)
    (h_update :
      ∀ k : ℕ,
        x (k + 1) = x k - α k • Matrix.toEuclideanLin (BInv k) (g k))
    (hx_tendsto : Tendsto x atTop (nhds xStar))
    (h_stationary : gradient f xStar = 0)
    (h_hessian :
      HasFDerivAt (gradient f)
        ((Matrix.toEuclideanCLM : MatrixN ≃⋆ₐ[ℝ] Point →L[ℝ] Point)
          (quasiNewtonHessianMatrix f xStar))
        xStar)
    (h_posDef : (quasiNewtonHessianMatrix f xStar).PosDef)
    (h_errorRatio_denominator_ne :
      ∀ᶠ k in atTop, ‖x k - xStar‖ ≠ 0)
    (h_searchDirection_ne :
      ∀ᶠ k in atTop, Matrix.toEuclideanLin (BInv k) (g k) ≠ 0)
    (h_hessianDirection_ne :
      ∀ᶠ k in atTop,
        Matrix.toEuclideanLin ((quasiNewtonHessianMatrix f xStar)⁻¹) (g k) ≠ 0)
    (h_curvatureRatio_denominator_ne :
      ∀ᶠ k in atTop,
        α k * dotProduct (x (k + 1) - x k) (g (k + 1) - g k) ≠ 0) :
    Tendsto (qErrorRatio x xStar 1) atTop (nhds (0 : ℝ)) ↔
      Tendsto
          (fun k : ℕ ↦
            (Real.cos
              (InnerProductGeometry.angle
                (Matrix.toEuclideanLin (BInv k) (g k))
                (-Matrix.toEuclideanLin ((quasiNewtonHessianMatrix f xStar)⁻¹) (g k)))) ^
              (2 : ℕ))
          atTop
          (nhds (1 : ℝ)) ∧
        Tendsto (quasiNewtonCurvatureRatio x B g α) atTop (nhds (1 : ℝ)) := sorry

end Chapter05Theorem5425
