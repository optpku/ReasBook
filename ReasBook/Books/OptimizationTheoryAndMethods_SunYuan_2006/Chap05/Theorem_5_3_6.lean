/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Assumption_5_3_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_5_extra_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Algorithm_5_1_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_1_extra_4
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Order.Filter.AtTopBot.Basic

noncomputable section

open Filter

section Chapter05Theorem536

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

-- Domain sampling for this refine pass:
-- * primary domain: Hessian-side BFGS runs with Wolfe-Powell line search on `ℝ^n`;
-- * sampled project declarations in the same owner family:
--   `GeneralQuasiNewtonMethod` and `GeneralQuasiNewtonMethod.stepSpec` from
--   `Algorithm_5_1_1`,
--   `WolfePowellCondition` and `WolfePowellParameters` from Chapter 2,
--   `GeneralQuasiNewtonMethod.IsFullStepBFGSOn`,
--   `bfgsHessianUpdate`,
--   `HasQuasiNewtonGlobalConvergenceAssumptions`;
-- * layer triage:
--   source-facing theorem: `bfgsWithWolfePowell_tendsto_to_minimizer`;
--   core/canonical owner: `GeneralQuasiNewtonMethod`;
--   bridge/view data here: `GeneralQuasiNewtonMethod.HessianBFGSOn`, adding the theorem-specific
--   Wolfe-Powell line-search data and the Hessian-side BFGS secant-curvature and update laws;
-- * primitive data owned upstream by `GeneralQuasiNewtonMethod`: the iterate / inverse-operator
--   / gradient / direction / step-size sequences and the quasi-Newton step data;
-- * primitive data added here: iterate membership in `D`, positive-definite Hessian-side
--   matrices, Wolfe-Powell parameters and accepted-step inequalities, and the Hessian-side BFGS
--   secant-curvature positivity and update `(5.1.45)`.

namespace GeneralQuasiNewtonMethod

/-- A Hessian-side BFGS/Wolfe-Powell quasi-Newton run on `D` records that every iterate stays in
`D`, every Hessian-side matrix `A.hessian k` is positive definite, each nonterminal accepted step
satisfies the Chapter 2 Wolfe-Powell inequalities on `lineSearchObjective f (A k) (A.d k)`, and
the Hessian approximations satisfy the BFGS update `(5.1.45)` together with positive secant
curvature. -/
structure HessianBFGSOn
    {f : Point → ℝ} (D : Set Point) (A : GeneralQuasiNewtonMethod f) where
  iterates_mem : ∀ k : ℕ, A k ∈ D
  hessian_posDef : ∀ k : ℕ, (A.hessian k).PosDef
  rho : ℝ
  sigma : ℝ
  wolfeParameters : WolfePowellParameters rho sigma
  wolfe (k : ℕ) (_ : A.ε < ‖A.g k‖) :
    WolfePowellCondition
      (lineSearchObjective f (A k) (A.d k))
      (deriv (lineSearchObjective f (A k) (A.d k)))
      rho sigma (A.α k)
  secant_curvature_pos :
    ∀ k : ℕ, 0 < dotProduct (A (k + 1) - A k) (A.g (k + 1) - A.g k)
  bfgs_update :
    ∀ k : ℕ,
      A.hessian (k + 1) =
        bfgsHessianUpdate
          (A.hessian k) (A (k + 1) - A k) (A.g (k + 1) - A.g k)

namespace HessianBFGSOn

/-- Every nonterminal Hessian-side BFGS/Wolfe-Powell stage carries the iterate-in-domain,
positive-definite Hessian matrix, positive step size, Wolfe-Powell line-search inequalities,
secant-curvature positivity, and BFGS Hessian-update data recorded by
`GeneralQuasiNewtonMethod.HessianBFGSOn`. -/
theorem stepSpec
    {f : Point → ℝ} {D : Set Point} {A : GeneralQuasiNewtonMethod f}
    (hA : A.HessianBFGSOn D) {k : ℕ} (hNotStopped : A.ε < ‖A.g k‖) :
    A k ∈ D ∧
      (A.hessian k).PosDef ∧
      0 < A.α k ∧
      A (k + 1) = A k - A.α k • (A.matrix k).toEuclideanLin (A.g k) ∧
      f (A (k + 1)) ≤
        f (A k) -
          hA.rho * A.α k * dotProduct (A.g k) ((A.matrix k).toEuclideanLin (A.g k)) ∧
      dotProduct (A.g (k + 1)) ((A.matrix k).toEuclideanLin (A.g k)) ≤
        hA.sigma * dotProduct (A.g k) ((A.matrix k).toEuclideanLin (A.g k)) ∧
      0 < dotProduct (A (k + 1) - A k) (A.g (k + 1) - A.g k) ∧
      A.hessian (k + 1) =
        bfgsHessianUpdate
          (A.hessian k) (A (k + 1) - A k) (A.g (k + 1) - A.g k) := by
  rcases A.stepSpec hNotStopped with ⟨_hd, _hα, hx, _hQN⟩
  have hWolfe := hA.wolfe k hNotStopped
  have hDerivZero :
      deriv (lineSearchObjective f (A.x k) (A.d k)) 0 =
        inner ℝ (A.g k) (A.d k) := by
    have hDiff : DifferentiableAt ℝ f (A.x k + (0 : ℝ) • A.d k) := by
      simpa using (A.hasGradientAt k).differentiableAt
    simpa [zero_smul, add_zero, (A.hasGradientAt k).gradient] using
      deriv_lineSearchObjective_apply f (A.x k) (A.d k) (0 : ℝ) hDiff
  have hDerivStep :
      deriv (lineSearchObjective f (A.x k) (A.d k)) (A.α k) =
        inner ℝ (A.g (k + 1)) (A.d k) := by
    have hGrad :
        HasGradientAt f (A.g (k + 1)) (A.x k + A.α k • A.d k) := by
      simpa [hx] using A.hasGradientAt (k + 1)
    simpa using hGrad.deriv_lineSearchObjective_apply
  have hStep :
      A (k + 1) = A k - A.α k • (A.matrix k).toEuclideanLin (A.g k) := by
    rw [hx, A.direction_eq_matrix hNotStopped]
    simp [sub_eq_add_neg, smul_neg]
  have hArmijo :
      f (A (k + 1)) ≤
        f (A k) - hA.rho * A.α k * dotProduct (A.g k) ((A.matrix k).toEuclideanLin (A.g k)) := by
    have hArmijo' :
        f (A (k + 1)) ≤ f (A k) + hA.rho * A.α k * inner ℝ (A.g k) (A.d k) := by
      simpa [lineSearchObjective_apply, lineSearchObjective_zero, hx, hDerivZero] using
        hWolfe.sufficientDecrease
    have hdir :
        A.d k = -(A.matrix k).toEuclideanLin (A.g k) :=
      A.direction_eq_matrix hNotStopped
    have hinnerk :
        inner ℝ (A.g k) (A.d k) =
          -dotProduct (A.g k) ((A.matrix k).toEuclideanLin (A.g k)) := by
      rw [hdir]
      simp [PiLp.inner_apply, dotProduct, mul_comm]
    calc
      f (A (k + 1)) ≤ f (A k) + hA.rho * A.α k * inner ℝ (A.g k) (A.d k) := hArmijo'
      _ =
          f (A k) +
            hA.rho * A.α k *
              (-dotProduct (A.g k) ((A.matrix k).toEuclideanLin (A.g k))) := by
        rw [hinnerk]
      _ = f (A k) - hA.rho * A.α k * dotProduct (A.g k) ((A.matrix k).toEuclideanLin (A.g k)) := by
        ring
  have hCurvature :
      dotProduct (A.g (k + 1)) ((A.matrix k).toEuclideanLin (A.g k)) ≤
        hA.sigma * dotProduct (A.g k) ((A.matrix k).toEuclideanLin (A.g k)) := by
    have hCurvature' :
        hA.sigma * inner ℝ (A.g k) (A.d k) ≤ inner ℝ (A.g (k + 1)) (A.d k) := by
      simpa [hDerivZero, hDerivStep] using hWolfe.curvature
    have hdir :
        A.d k = -(A.matrix k).toEuclideanLin (A.g k) :=
      A.direction_eq_matrix hNotStopped
    have hinnerk :
        inner ℝ (A.g k) (A.d k) =
          -dotProduct (A.g k) ((A.matrix k).toEuclideanLin (A.g k)) := by
      rw [hdir]
      simp [PiLp.inner_apply, dotProduct, mul_comm]
    have hinnerkp1 :
        inner ℝ (A.g (k + 1)) (A.d k) =
          -dotProduct (A.g (k + 1)) ((A.matrix k).toEuclideanLin (A.g k)) := by
      rw [hdir]
      simp [PiLp.inner_apply, dotProduct, mul_comm]
    rw [hinnerk, hinnerkp1] at hCurvature'
    linarith
  exact ⟨hA.iterates_mem k, hA.hessian_posDef k, hWolfe.step_pos, hStep, hArmijo, hCurvature,
    hA.secant_curvature_pos k,
    hA.bfgs_update k⟩

end HessianBFGSOn

end GeneralQuasiNewtonMethod

/-- Chapter05 Theorem 5.3.6: let `x₀` and `B₀` be a starting point and a symmetric positive
definite initial matrix, respectively. Suppose `f` satisfies Chapter05 Assumption 5.3.1. Then,
under the Wolfe-Powell inexact line-search inequalities `(2.5.3)` and `(2.5.7)`, the sequence
generated by the Hessian-side BFGS/Wolfe run `A` converges to the given minimizer `xStar` of
`f` on the level set `quasiNewtonLevelSet f A.x0`. The canonical run owner is
`GeneralQuasiNewtonMethod`; the additional Hessian-side BFGS/Wolfe content is the bridge
hypothesis `A.HessianBFGSOn D`. -/
theorem bfgsWithWolfePowell_tendsto_to_minimizer
    (f : Point → ℝ) (D : Set Point)
    (A : GeneralQuasiNewtonMethod f)
    (hA : A.HessianBFGSOn D)
    (h_assumption : HasQuasiNewtonGlobalConvergenceAssumptions D f A.x0)
    (xStar : Point) (hxStar : IsMinOn f (quasiNewtonLevelSet f A.x0) xStar) :
    Tendsto A atTop (nhds xStar) := by
  sorry

end Chapter05Theorem536
