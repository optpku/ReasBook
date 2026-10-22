/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Algorithm_5_1_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_1_extra_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_4_8

noncomputable section

section Chapter05HessianBFGSMethod

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

-- Domain sampling:
-- * primary domain: full-step Hessian-side BFGS data on the Chapter 5 quasi-Newton run owner;
-- * sampled owners: `GeneralQuasiNewtonMethod`, `GeneralQuasiNewtonMethod.hessian`,
--   `bfgsHessianUpdate`, and the nearby inverse-side bridge
--   `GeneralQuasiNewtonMethod.IsFullStepBFGSOn`;
-- * source/core/bridge triage:
--   core/canonical owner: `GeneralQuasiNewtonMethod`;
--   bridge/view owned here: `GeneralQuasiNewtonMethod.IsFullStepHessianBFGSOn`;
-- * primitive data owned upstream: the iterate, gradient, direction, step-size, and inverse
--   approximation sequences of `GeneralQuasiNewtonMethod`;
-- * primitive source-facing data added here: iterate membership in `D`, positive-definite
--   Hessian-side matrices, the full step `xₖ₊₁ = xₖ - Bₖ⁻¹ gₖ`, positive secant curvature, and
--   the Hessian-side BFGS update `(5.1.45)`.

namespace GeneralQuasiNewtonMethod

/-- A general quasi-Newton run is a full-step Hessian-side BFGS method on `D` when every
iterate stays in `D`, every Hessian-side matrix `A.hessian k` is positive definite, each step is
the full Hessian-side BFGS step `x (k + 1) = x k - Bₖ⁻¹ gₖ`, the secant curvature is positive,
and the Hessian approximation satisfies the BFGS update `(5.1.45)`. -/
structure IsFullStepHessianBFGSOn
    {f : Point → ℝ} (D : Set Point) (A : GeneralQuasiNewtonMethod f) : Prop where
  iterates_mem : ∀ k : ℕ, A k ∈ D
  hessian_posDef : ∀ k : ℕ, (A.hessian k).PosDef
  full_step : ∀ k : ℕ, A (k + 1) = A k - (A.matrix k).toEuclideanLin (A.g k)
  secant_curvature_pos :
    ∀ k : ℕ, 0 < dotProduct (A (k + 1) - A k) (A.g (k + 1) - A.g k)
  bfgs_update :
    ∀ k : ℕ,
      A.hessian (k + 1) =
        bfgsHessianUpdate
          (A.hessian k) (A (k + 1) - A k) (A.g (k + 1) - A.g k)

namespace IsFullStepHessianBFGSOn

/-- Every stage of a full-step Hessian-side BFGS run records the iterate-in-domain,
positive-definite Hessian matrix, full-step update, positive secant curvature, and Hessian-side
BFGS update carried by `GeneralQuasiNewtonMethod.IsFullStepHessianBFGSOn`. -/
theorem stepSpec
    {f : Point → ℝ} {D : Set Point} {A : GeneralQuasiNewtonMethod f}
    (hA : A.IsFullStepHessianBFGSOn D) (k : ℕ) :
    A k ∈ D ∧
      (A.hessian k).PosDef ∧
      A (k + 1) = A k - (A.matrix k).toEuclideanLin (A.g k) ∧
      0 < dotProduct (A (k + 1) - A k) (A.g (k + 1) - A.g k) ∧
      A.hessian (k + 1) =
        bfgsHessianUpdate
          (A.hessian k) (A (k + 1) - A k) (A.g (k + 1) - A.g k) := by
  exact ⟨hA.iterates_mem k, hA.hessian_posDef k, hA.full_step k, hA.secant_curvature_pos k,
    hA.bfgs_update k⟩

end IsFullStepHessianBFGSOn

end GeneralQuasiNewtonMethod

end Chapter05HessianBFGSMethod
