/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Lemma_5_3_2

noncomputable section

section Chapter05Lemma573

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Domain sampling for this refine pass:
-- * source-facing layer: Lemma 5.7.3 secant estimates on `quasiNewtonLevelSet f x0` under
--   Chapter05 Assumption 5.3.1;
-- * core/canonical project owners: `lowerLevelSetOn`, `HasLowerLevelHessianLowerBound`,
--   `HasLowerLevelHessianUpperBound`;
-- * derived API used here: the secant norm and curvature estimates from `Lemma_5_3_2`.
-- Primitive data for this file is the Chapter 5 assumption package together with the explicit
-- lower and upper Hessian constants extracted from it; the three labeled estimates here stay
-- downstream of that source-facing owner layer rather than introducing a separate Hessian-matrix
-- bridge.

/- Chapter05 Lemma 5.7.3 (1): under Chapter05 Assumption 5.3.1 and lower and upper Hessian
bounds with constants `m > 0` and `M` on `quasiNewtonLevelSet f x0`, every nonzero secant pair
`yk = gradient f (xk + sk) - gradient f xk` with
`xk, xk + sk ∈ quasiNewtonLevelSet f x0` satisfies `‖yk‖ / ‖sk‖ ≤ M`.

This is an exact recall of the canonical Chapter 5 estimate
`secantNorm_div_stepNorm_le_M_of_lowerLevelHessianBounds`. -/
#check secantNorm_div_stepNorm_le_M_of_lowerLevelHessianBounds

/-- Chapter05 Lemma 5.7.3 (2): if Chapter05 Assumption 5.3.1 and the lower Hessian bound with
modulus `m > 0` hold on `quasiNewtonLevelSet f x0`, then under the same secant setup with
`sk ≠ 0`, the curvature denominator controls the step norm by
`‖sk‖ ^ 2 / dotProduct sk yk ≤ 1 / m`. -/
theorem stepNormSq_div_secantCurvature_le_of_lowerLevelHessianLowerBound
    {D : Set Point}
    (f : Point → ℝ) (x0 xk sk yk : Point) {m : ℝ}
    (hm : 0 < m)
    (hA : HasQuasiNewtonGlobalConvergenceAssumptions D f x0)
    (hLower : HasLowerLevelHessianLowerBound D f x0 m)
    (hxk : xk ∈ quasiNewtonLevelSet f x0)
    (hxk_add_sk : xk + sk ∈ quasiNewtonLevelSet f x0)
    (hyk : yk = gradient f (xk + sk) - gradient f xk)
    (hsk : sk ≠ 0) :
    ‖sk‖ ^ (2 : ℕ) / dotProduct sk yk ≤ 1 / m := by
  have hcurv :=
    secantCurvature_pos_of_step_nonzero_of_lowerLevelHessianLowerBound
      f x0 xk sk yk hm hA hLower hxk hxk_add_sk hyk hsk
  have hbound :=
    secantCurvature_lowerBound_of_lowerLevelHessianLowerBound
      f x0 xk sk yk hA hLower hxk hxk_add_sk hyk
  have hdiv :
      m * (‖sk‖ ^ (2 : ℕ) / dotProduct sk yk) ≤ 1 := by
    calc
      m * (‖sk‖ ^ (2 : ℕ) / dotProduct sk yk)
          = (m * ‖sk‖ ^ (2 : ℕ)) / dotProduct sk yk := by
              rw [mul_div_assoc]
      _ ≤ 1 := by
        rw [div_le_iff₀ hcurv]
        simpa using hbound
  have hdiv' :
      (‖sk‖ ^ (2 : ℕ) / dotProduct sk yk) * m ≤ 1 := by
    simpa [mul_comm] using hdiv
  exact (le_div_iff₀ hm).2 hdiv'

/- Chapter05 Lemma 5.7.3 (3): if Chapter05 Assumption 5.3.1 and lower and upper Hessian bounds
with constants `0 < m` and `M` hold on `quasiNewtonLevelSet f x0`, then under the same secant
setup with `sk ≠ 0`, the secant norm satisfies `‖yk‖ ^ 2 / dotProduct sk yk ≤ M`.

This is an exact recall of the canonical Chapter 5 estimate
`secantNormSq_div_secantCurvature_le_M_of_lowerLevelHessianBounds`. -/
#check secantNormSq_div_secantCurvature_le_M_of_lowerLevelHessianBounds

end Chapter05Lemma573
