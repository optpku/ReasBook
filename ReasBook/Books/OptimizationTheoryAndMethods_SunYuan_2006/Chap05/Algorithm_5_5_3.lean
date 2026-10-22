/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Algorithm_5_1_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_5_extra_1

noncomputable section

-- Source/core/bridge triage for this file:
-- * source-facing owner kept here: `SelfScalingVariableMetricMethod`, which extends the Chapter 5
--   quasi-Newton run owner by the SSVM-specific parameters and update law.
-- * core/canonical owner reused here: `GeneralQuasiNewtonMethod`.
-- * bridge/view API kept here: the concrete Euclidean matrix update on `A.matrix`.

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

/-- Chapter05 Algorithm 5.5.3: a self-scaling variable-metric method on `ℝ^n` extends a general
quasi-Newton run by a fixed Broyden-class parameter `φ ≥ 0` and positive self-scaling
parameters `γ k` on every nonterminal stage. At each such stage, the source step data is the
canonical quasi-Newton step `α k • d k` and gradient difference `g (k + 1) - g k`, the two
denominator-nonzero side conditions needed for the SSVM inverse update hold, and the Euclidean
matrix representative of the inverse approximation satisfies the textbook self-scaling inverse
update formula. The inherited quasi-Newton owner retains the stopping condition
`A.terminatedAt k :↔ ‖A.g k‖ ≤ A.ε`, the positive step-size output `0 < A.α k`, the iterate
update, and the inverse-form secant equation. -/
structure SelfScalingVariableMetricMethod
    (f : Point → ℝ) extends GeneralQuasiNewtonMethod f where
  phi : ℝ
  gamma : ℕ → ℝ
  phi_nonneg : 0 ≤ phi
  gamma_pos (k : ℕ) (hNotStopped : ε < ‖g k‖) : 0 < gamma k
  secant_denom_ne_zero (k : ℕ) (hNotStopped : ε < ‖g k‖) :
    dotProduct (α k • d k) (g (k + 1) - g k) ≠ 0
  curvature_denom_ne_zero (k : ℕ) (hNotStopped : ε < ‖g k‖) :
    dotProduct (g (k + 1) - g k)
      ((Matrix.toEuclideanLin.symm (H k)).mulVec (g (k + 1) - g k)) ≠ 0
  update_eq (k : ℕ) (hNotStopped : ε < ‖g k‖) :
    Matrix.toEuclideanLin.symm (H (k + 1)) =
      ssvmInverseUpdate
        (Matrix.toEuclideanLin.symm (H k)) (α k • d k) (g (k + 1) - g k) phi (gamma k)

namespace SelfScalingVariableMetricMethod

/-- A self-scaling variable-metric method can be used as its iterate sequence `x`. -/
instance {f : Point → ℝ} :
    CoeFun (SelfScalingVariableMetricMethod f) (fun _ ↦ ℕ → Point) where
  coe A := A.x

/-- Evaluating a self-scaling variable-metric method as a function returns its iterate sequence. -/
theorem coe_apply {f : Point → ℝ} (A : SelfScalingVariableMetricMethod f) (k : ℕ) :
    A k = A.x k := rfl

/-- The explicit gradient data in a self-scaling variable-metric method agrees with the
canonical gradient of `f` at every iterate. -/
theorem gradient_eq {f : Point → ℝ} (A : SelfScalingVariableMetricMethod f) (k : ℕ) :
    gradient f (A k) = A.g k := by
  simpa using (A.toGeneralQuasiNewtonMethod.hasGradientAt k).gradient

/-- Every nonterminal SSVM stage has the underlying quasi-Newton direction, positive step size,
iterate update, inverse-form secant equation, and the additional SSVM denominator and matrix
update data from Algorithm 5.5.3. -/
theorem stepSpec
    {f : Point → ℝ} (A : SelfScalingVariableMetricMethod f) {k : ℕ}
    (hNotStopped : A.ε < ‖A.g k‖) :
    A.d k = -(A.H k (A.g k)) ∧
      0 < A.α k ∧
      A (k + 1) = A k + A.α k • A.d k ∧
      satisfiesQuasiNewtonEquation (A.H (k + 1)) (A.g (k + 1) - A.g k) (A (k + 1) - A k) ∧
      0 ≤ A.phi ∧
      0 < A.gamma k ∧
      dotProduct (A.α k • A.d k) (A.g (k + 1) - A.g k) ≠ 0 ∧
      dotProduct (A.g (k + 1) - A.g k)
        ((A.matrix k).mulVec (A.g (k + 1) - A.g k)) ≠ 0 ∧
      A.matrix (k + 1) =
        ssvmInverseUpdate
          (A.matrix k) (A.α k • A.d k) (A.g (k + 1) - A.g k)
            A.phi (A.gamma k) := by
  rcases A.toGeneralQuasiNewtonMethod.stepSpec hNotStopped with ⟨hd, hα, hx, hsecant⟩
  exact ⟨hd, hα, hx, hsecant, A.phi_nonneg, A.gamma_pos k hNotStopped,
    A.secant_denom_ne_zero k hNotStopped, A.curvature_denom_ne_zero k hNotStopped,
    A.update_eq k hNotStopped⟩

/-- The SSVM update formula on `A.matrix` is available directly from the source-facing owner. -/
theorem matrix_update_eq
    {f : Point → ℝ} (A : SelfScalingVariableMetricMethod f) {k : ℕ}
    (hNotStopped : A.ε < ‖A.g k‖) :
    A.matrix (k + 1) =
      ssvmInverseUpdate
        (A.matrix k) (A.α k • A.d k) (A.g (k + 1) - A.g k)
          A.phi (A.gamma k) :=
  A.update_eq k hNotStopped

end SelfScalingVariableMetricMethod

end
