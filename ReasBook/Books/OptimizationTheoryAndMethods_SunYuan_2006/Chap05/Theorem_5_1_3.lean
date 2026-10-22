/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Theorem_3_2_2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_1_extra_4

noncomputable section

open Filter
open scoped Matrix.Norms.L2Operator

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

-- Semantic recall:
-- * `HasLocalLipschitzHessianMatrixAt` is the Chapter 3 owner for the local Hessian model.
-- * `sr1Update` and `sr1Residual` are the Chapter 5 owners for the SR1 update formula.
--
-- This file keeps the source-facing SR1-with-skipping recursion and uniform linear independence
-- hypothesis explicit, while reusing the canonical Hessian owner directly.

/-- A local Lipschitz Hessian matrix field is bounded on some ball about `xStar`. This supplies
the bounded-neighborhood part of the source hypothesis from the Chapter 3 canonical owner. -/
theorem HasLocalLipschitzHessianMatrixAt.exists_ball_norm_bound
    {f : Point → ℝ} {G : Point → MatrixN} {xStar : Point}
    (h_hessian : HasLocalLipschitzHessianMatrixAt f G xStar) :
    ∃ ε > 0, ∃ M, 0 ≤ M ∧ ∀ x, x ∈ Metric.ball xStar ε → ‖G x‖ ≤ M := by
  sorry

/-- The inverse-Hessian SR1 recursion with skipping rule parameter `r`: at stage `k`, set
`v_k = s_k - H_k y_k`; if `r * ‖y_k‖ * ‖v_k‖ ≤ |⟪v_k, y_k⟫|`, apply the rank-one SR1 update,
and otherwise keep `H_(k+1) = H_k`. This reuses the Chapter 5 owner `sr1Update`, whose
totalized inverse matches the displayed rank-one formula even in the degenerate case
`⟪v_k, y_k⟫ = 0`. -/
def sr1InverseUpdateWithSkippingRule (H : MatrixN) (s y : Point) (r : ℝ) : MatrixN :=
  let v := sr1Residual H y s
  if _ : r * ‖y‖ * ‖v‖ ≤ |dotProduct v y| then
    sr1Update H s y
  else
    H

/-- On the guard-true branch, `sr1InverseUpdateWithSkippingRule` is exactly the Chapter 5 SR1
update. -/
theorem sr1InverseUpdateWithSkippingRule_eq_sr1Update
    (H : MatrixN) (s y : Point) (r : ℝ) :
    r * ‖y‖ * ‖sr1Residual H y s‖ ≤ |dotProduct (sr1Residual H y s) y| →
      sr1InverseUpdateWithSkippingRule H s y r = sr1Update H s y := by
  intro hskip
  simp [sr1InverseUpdateWithSkippingRule, hskip]

/-- If the skipping inequality fails, `sr1InverseUpdateWithSkippingRule` keeps the current
inverse-Hessian approximation unchanged. -/
theorem sr1InverseUpdateWithSkippingRule_eq_self_of_not_skip
    (H : MatrixN) (s y : Point) (r : ℝ)
    (hskip :
      ¬ r * ‖y‖ * ‖sr1Residual H y s‖ ≤ |dotProduct (sr1Residual H y s) y|) :
    sr1InverseUpdateWithSkippingRule H s y r = H := by
  dsimp [sr1InverseUpdateWithSkippingRule]
  rw [if_neg hskip]

/-- Even on the guard-true branch, a zero SR1 denominator forces
`sr1InverseUpdateWithSkippingRule` to keep the current matrix. -/
theorem sr1InverseUpdateWithSkippingRule_eq_self_of_zero_denominator
    (H : MatrixN) (s y : Point) (r : ℝ)
    (hdenom : dotProduct (sr1Residual H y s) y = 0) :
    sr1InverseUpdateWithSkippingRule H s y r = H := by
  by_cases hskip : r * ‖y‖ * ‖sr1Residual H y s‖ ≤ |dotProduct (sr1Residual H y s) y|
  · rw [sr1InverseUpdateWithSkippingRule_eq_sr1Update H s y r hskip]
    simp [sr1Update, hdenom]
  · simp [sr1InverseUpdateWithSkippingRule, hskip]

/-- An inverse-Hessian SR1 sequence with skipping rule parameter `r` has `0 < r < 1` and
evolves by the one-step owner `sr1InverseUpdateWithSkippingRule` at each stage. -/
def IsSR1InverseSequenceWithSkippingRule
    (H : ℕ → MatrixN) (s y : ℕ → Point) (r : ℝ) : Prop :=
  0 < r ∧
    r < 1 ∧
      ∀ k : ℕ, H (k + 1) = sr1InverseUpdateWithSkippingRule (H k) (s k) (y k) r

/-- The stage update formula extracted from `IsSR1InverseSequenceWithSkippingRule`. -/
theorem IsSR1InverseSequenceWithSkippingRule.step_eq
    {H : ℕ → MatrixN} {s y : ℕ → Point} {r : ℝ}
    (hSR1 : IsSR1InverseSequenceWithSkippingRule H s y r) (k : ℕ) :
    H (k + 1) = sr1InverseUpdateWithSkippingRule (H k) (s k) (y k) r :=
  hSR1.2.2 k

/-- A step sequence is uniformly linearly independent when there are a window length `m` and a
uniform determinant lower bound `β > 0` such that every block of `m` consecutive steps contains
`n` steps whose coordinate matrix has determinant of absolute value at least `β`. -/
def HasUniformlyLinearlyIndependentSteps (s : ℕ → Point) : Prop :=
  ∃ m : ℕ, n ≤ m ∧ ∃ β > 0, ∀ k : ℕ,
    ∃ ι : Fin n → ℕ,
      StrictMono ι ∧
        (∀ j : Fin n, k ≤ ι j) ∧
          (∀ j : Fin n, ι j < k + m) ∧
            β ≤ |Matrix.det (fun i j ↦ s (ι j) i)|

/-- Chapter05 Theorem 5.1.3: if `f` admits a local Lipschitz Hessian matrix field `G` at
`xStar` (hence `G` is bounded on some neighborhood of `xStar`), `x k → xStar`, the secant
data satisfy `s k = x (k + 1) - x k` and `y k = gradient f (x (k + 1)) - gradient f (x k)`,
the SR1 skipping rule `(5.1.26)` holds for every `k`, the steps are uniformly linearly
independent, and the limit Hessian matrix `G xStar` is invertible, then the inverse-Hessian
SR1 matrices converge in norm to `(G xStar)⁻¹`. -/
theorem sr1InverseHessian_tendsto_limitHessianInverse
    (f : Point → ℝ) (G : Point → MatrixN) (x : ℕ → Point) (s y : ℕ → Point)
    (H : ℕ → MatrixN) (xStar : Point) (r : ℝ)
    (h_hessian : HasLocalLipschitzHessianMatrixAt f G xStar)
    (h_hessian_unit : IsUnit (G xStar))
    (h_s : ∀ k : ℕ, s k = x (k + 1) - x k)
    (h_y : ∀ k : ℕ, y k = gradient f (x (k + 1)) - gradient f (x k))
    (h_tendsto : Tendsto x atTop (nhds xStar))
    (h_sr1 : IsSR1InverseSequenceWithSkippingRule H s y r)
    (h_steps : HasUniformlyLinearlyIndependentSteps s) :
    Tendsto (fun k ↦ ‖H k - (G xStar)⁻¹‖) atTop (nhds (0 : ℝ)) := sorry
