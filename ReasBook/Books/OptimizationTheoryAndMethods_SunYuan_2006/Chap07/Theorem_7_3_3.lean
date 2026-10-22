/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Definition_7_3_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Theorem_7_3_4

open Matrix

noncomputable section

variable {m n : ℕ}

-- Semantic recall: Chapter 7 already owns the regularized-normal-equation predicate
-- `solvesLevenbergMarquardtNormalEquation` and the source-faithful trust-region least-squares
-- surface from `Theorem_7_3_4`, namely the Euclidean residual objective
-- `s ↦ (1 / 2) * ‖Matrix.toEuclideanLin J s + r‖²` on the canonical closed ball
-- `Metric.closedBall 0 ‖s_k‖`. This item is the source-facing special case with radius `‖s_k‖`.

/-- A step satisfying the regularized normal equation is automatically a trust-region multiplier
for the radius `Δ = ‖s_k‖`. -/
theorem isLevenbergMarquardtTrustRegionMultiplier_self
    (J : Matrix (Fin m) (Fin n) ℝ) (r : EuclideanSpace ℝ (Fin m)) (μ : ℝ)
    (sk : EuclideanSpace ℝ (Fin n))
    (hμ : 0 < μ)
    (hsk : (Jᵀ * J + μ • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVec sk = -(Jᵀ.mulVec r)) :
    IsLevenbergMarquardtTrustRegionMultiplier J r ‖sk‖ sk μ := by
  refine
    { nonneg := le_of_lt hμ
      stationarity := by
        simpa [solvesLevenbergMarquardtNormalEquation] using hsk
      complementarySlackness := ?_
      feasible := le_rfl }
  simp

/-- Helper for Chapter07 Theorem 7.3.3: every function attains a minimum on a radius-zero closed
ball at its center. -/
lemma isMinOn_closedBall_zeroRadius
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    IsMinOn f (Metric.closedBall x 0) x := by
  -- Rewrite the minimizer predicate so the proof reduces to uniqueness of points in the ball.
  rw [isMinOn_iff]
  intro y hy
  -- A point in `closedBall x 0` has zero distance from `x`, hence it is exactly `x`.
  have hdist : dist y x = 0 := by
    have hle : dist y x ≤ 0 := by
      simpa [Metric.mem_closedBall] using hy
    exact le_antisymm hle dist_nonneg
  have hyx : y = x := eq_of_dist_eq_zero hdist
  simp [hyx]

/-- Chapter07 Theorem 7.3.3: if `μ > 0` and `s_k` satisfies the regularized normal equation
`(Jᵀ * J + μ • 1).mulVec s_k = -(Jᵀ.mulVec r)`, then `s_k` is a global solution of the
subproblem `min q^(k) (s) = (1 / 2) * ‖J s + r‖₂²` subject to `‖s‖ ≤ ‖s_k‖`, formalized with
the Euclidean residual `Matrix.toEuclideanLin J s + r`. -/
theorem levenbergMarquardtStep_isMinOn_ball_of_regularizedNormalEquation
    (J : Matrix (Fin m) (Fin n) ℝ) (r : EuclideanSpace ℝ (Fin m)) (μ : ℝ)
    (sk : EuclideanSpace ℝ (Fin n))
    (hμ : 0 < μ)
    (hsk : (Jᵀ * J + μ • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVec sk = -(Jᵀ.mulVec r)) :
    IsMinOn
      (fun s : EuclideanSpace ℝ (Fin n) ↦
        ((1 : ℝ) / 2) * ‖Matrix.toEuclideanLin J s + r‖ ^ (2 : ℕ))
      (Metric.closedBall 0 ‖sk‖) sk := by
  -- Split off the degenerate radius-zero case, since Theorem 7.3.4 requires a positive radius.
  by_cases hzero : ‖sk‖ = 0
  · -- When the radius is zero, the feasible set is the singleton `{0} = {sk}`.
    have hsk_zero : sk = 0 := by
      simpa [norm_eq_zero] using hzero
    simpa [hzero, hsk_zero] using
      isMinOn_closedBall_zeroRadius
        (f := fun s : EuclideanSpace ℝ (Fin n) ↦
          ((1 : ℝ) / 2) * ‖Matrix.toEuclideanLin J s + r‖ ^ (2 : ℕ))
        (x := (0 : EuclideanSpace ℝ (Fin n)))
  · -- In the positive-radius branch, package the normal equation as a multiplier and reuse 7.3.4.
    have hsk_ne : sk ≠ 0 := by
      intro hsk_zero
      apply hzero
      simp [hsk_zero]
    have hΔ : 0 < ‖sk‖ := norm_pos_iff.mpr hsk_ne
    have hmult : IsLevenbergMarquardtTrustRegionMultiplier J r ‖sk‖ sk μ :=
      isLevenbergMarquardtTrustRegionMultiplier_self J r μ sk hμ hsk
    have hsol :
        sk ∈ Metric.closedBall 0 ‖sk‖ ∧
          IsMinOn
            (fun s : EuclideanSpace ℝ (Fin n) ↦
              ((1 : ℝ) / 2) * ‖Matrix.toEuclideanLin J s + r‖ ^ (2 : ℕ))
            (Metric.closedBall 0 ‖sk‖) sk :=
      (levenbergMarquardtTrustRegionSolution_iff_exists_multiplier J r ‖sk‖ hΔ sk).2
        ⟨μ, hmult⟩
    exact hsol.2

end
