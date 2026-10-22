/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Assumption_5_4_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.BFGSMethod
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_9
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Topology.Algebra.InfiniteSum.Basic

noncomputable section

open Filter
open scoped Matrix.Norms.L2Operator

section Chapter05Theorem5422

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

-- Domain sampling:
-- * `GeneralQuasiNewtonMethod` is the Chapter 5 owner for quasi-Newton trajectory data.
-- * `IsBFGSMethod` from `BFGSMethod` is the Chapter 5 bridge for the inverse-BFGS update.
-- * the additional source-facing data in this theorem are that the iterates stay in `D`, the
--   inverse-Hessian matrices remain positive definite, and every generated step is the full
--   inverse-BFGS step `xₖ₊₁ = xₖ - Hₖ gₖ`.
--
-- In this file, `GeneralQuasiNewtonMethod.IsFullStepBFGSOn` is the theorem-specific bridge/view
-- layer. The run owner itself remains the canonical `GeneralQuasiNewtonMethod`.

namespace GeneralQuasiNewtonMethod

/-- A quasi-Newton run is a full-step BFGS method on `D` when it is a BFGS run in the sense of
`IsBFGSMethod`, every iterate stays in `D`, every inverse-Hessian matrix `A.matrix k` is
positive definite, and each generated step is the full inverse-BFGS step
`x (k + 1) = x k - A.matrix k * g k`. -/
structure IsFullStepBFGSOn
    {f : Point → ℝ} (D : Set Point) (A : GeneralQuasiNewtonMethod f) : Prop where
  isBFGS : IsBFGSMethod A
  iterates_mem : ∀ k : ℕ, A k ∈ D
  matrices_posDef : ∀ k : ℕ, (A.matrix k).PosDef
  full_step (k : ℕ) (_ : A.ε < ‖A.g k‖) :
    A (k + 1) = A k - (A.matrix k).toEuclideanLin (A.g k)

namespace IsFullStepBFGSOn

/-- Every nonterminal full-step BFGS stage keeps the iterate in `D`, keeps the inverse-Hessian
matrix positive definite, uses the full inverse-BFGS step, has positive curvature, and satisfies
the inverse-BFGS update formula. -/
theorem stepSpec
    {f : Point → ℝ} {D : Set Point} {A : GeneralQuasiNewtonMethod f}
    (hA : A.IsFullStepBFGSOn D) {k : ℕ} (hNotStopped : A.ε < ‖A.g k‖) :
    A k ∈ D ∧
      (A.matrix k).PosDef ∧
      A (k + 1) = A k - (A.matrix k).toEuclideanLin (A.g k) ∧
      0 < dotProduct (A (k + 1) - A k) (A.g (k + 1) - A.g k) ∧
      A.matrix (k + 1) =
        bfgsInverseUpdate (A.matrix k) (A (k + 1) - A k) (A.g (k + 1) - A.g k) := by
  rcases hA.isBFGS.stepSpec hNotStopped with ⟨hcurv, hupdate⟩
  exact ⟨hA.iterates_mem k, hA.matrices_posDef k, hA.full_step k hNotStopped, hcurv, hupdate⟩

@[simp] theorem epsilon_eq_zero
    {f : Point → ℝ} {D : Set Point} {A : GeneralQuasiNewtonMethod f}
    (hA : A.IsFullStepBFGSOn D) :
    A.ε = 0 :=
  hA.isBFGS.epsilon_eq_zero

end IsFullStepBFGSOn
end GeneralQuasiNewtonMethod

/-- The reference inverse Hessian `∇²f(x*)⁻¹` used in the local BFGS start condition. -/
def bfgsReferenceInverse
    {D : Set Point} {f : Point → ℝ}
    (h : HasQuasiNewtonStrongLocalMinimizerAssumptions D f) : MatrixN :=
  (quasiNewtonHessianMatrix f h.xStar)⁻¹

/-- The weighted Frobenius-type BFGS matrix norm `‖E‖_W = √(trace (W * E * W * Eᵀ))`
used for the initial inverse-Hessian error in the local BFGS theorem. -/
def bfgsMatrixNorm (W E : MatrixN) : ℝ :=
  Real.sqrt (Matrix.trace (W * E * W * E.transpose))

/-- The local error size `σ(x, xNext) = max {‖x - x*‖, ‖xNext - x*‖}` from `(5.4.133)`. -/
def bfgsSigma (x xNext xStar : Point) : ℝ :=
  max ‖x - xStar‖ ‖xNext - xStar‖

/-- The neighborhood form of `(5.4.133)`: with
`μ = ‖(quasiNewtonHessianMatrix f h.xStar)⁻¹‖`, one has
`μ * h.γ * σ(x, xNext) ≤ 1 / 3` for all `x`, `xNext` in some ball about `h.xStar`. -/
def bfgsOneThirdConditionInNeighborhood
    {D : Set Point} {f : Point → ℝ}
    (h : HasQuasiNewtonStrongLocalMinimizerAssumptions D f) : Prop :=
  ∃ ρ > 0, ∀ x xNext,
    x ∈ Metric.ball h.xStar ρ →
    xNext ∈ Metric.ball h.xStar ρ →
      ‖bfgsReferenceInverse h‖ * h.γ * bfgsSigma x xNext h.xStar ≤ (1 / 3 : ℝ)

/-- Chapter05 Theorem 5.4.22: let `f : ℝ^n → ℝ` satisfy
`HasQuasiNewtonStrongLocalMinimizerAssumptions D f`; assume the neighborhood one-third
condition `bfgsOneThirdConditionInNeighborhood h`, i.e. `(5.4.133)` with
`μ = ‖∇²f(h.xStar)⁻¹‖`, `σ(x, xNext) = max {‖x - h.xStar‖, ‖xNext - h.xStar‖}`.
Then there exist `ε > 0` and `δ > 0` such that every initial pair `(x0, H0)` with
`‖x0 - h.xStar‖ < ε` and
`bfgsMatrixNorm (quasiNewtonHessianMatrix f h.xStar) (H0 - bfgsReferenceInverse h) < δ`
admits a well-defined full-step BFGS run on `D`, every such run converges linearly to
`h.xStar`, and summable error norms imply the little-`o` superlinear refinement. The run owner
is the canonical `GeneralQuasiNewtonMethod`, and the theorem-specific BFGS hypotheses are
recorded by `GeneralQuasiNewtonMethod.IsFullStepBFGSOn`. -/
theorem inverseBfgsMethod_converges_of_small_initial_errors
    (D : Set Point) (f : Point → ℝ)
    (h : HasQuasiNewtonStrongLocalMinimizerAssumptions D f)
    (h_oneThird : bfgsOneThirdConditionInNeighborhood h) :
    ∃ ε > 0, ∃ δ > 0, ∀ x0 H0,
      ‖x0 - h.xStar‖ < ε →
      bfgsMatrixNorm (quasiNewtonHessianMatrix f h.xStar) (H0 - bfgsReferenceInverse h) < δ →
      (∃ A : GeneralQuasiNewtonMethod f,
        A.x0 = x0 ∧ A.matrix0 = H0 ∧ A.IsFullStepBFGSOn D) ∧
      (∀ A : GeneralQuasiNewtonMethod f,
        A.x0 = x0 →
        A.matrix0 = H0 →
        A.IsFullStepBFGSOn D →
        LinearlyConvergesTo A h.xStar) ∧
      ∀ A : GeneralQuasiNewtonMethod f,
        A.x0 = x0 →
        A.matrix0 = H0 →
        A.IsFullStepBFGSOn D →
        Summable (fun k ↦ ‖A k - h.xStar‖) →
          ((fun k ↦ ‖A (k + 1) - h.xStar‖) =o[atTop] fun k ↦ ‖A k - h.xStar‖) := by
  sorry

end Chapter05Theorem5422
