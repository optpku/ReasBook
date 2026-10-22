/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Definition_6_1_extra_3

noncomputable section

namespace TrustRegionSubproblem

variable {n : ℕ}

/-- If `g_kᵀ B_k g_k ≤ 0`, then the Cauchy point is the boundary steepest-descent step `s_k^G`. -/
theorem cauchyPoint_eq_gradientBoundaryStep_of_nonpos_curvature
    (P : TrustRegionSubproblem n) (h_curv : P.gradientCurvature ≤ 0) :
    P.cauchyPoint = P.gradientBoundaryStep := by
  rw [P.cauchyPoint_eq, P.cauchyPointScale_eq_one_of_nonpos_curvature h_curv, one_smul]

/-- Chapter06 Exercise 6.8 (1): if `g_k ≠ 0` and `g_kᵀ B_k g_k ≤ 0`, then the Cauchy point is
the boundary steepest-descent step `-(Δ_k / ‖g_k‖) • g_k`. -/
theorem cauchyPoint_eq_of_nonpos_curvature
    (P : TrustRegionSubproblem n) (h_grad : P.gradient ≠ 0)
    (h_curv : P.gradientCurvature ≤ 0) :
    P.cauchyPoint = -(P.radius / ‖P.gradient‖) • P.gradient := by
  rw [P.cauchyPoint_eq_gradientBoundaryStep_of_nonpos_curvature h_curv]
  rw [P.gradientBoundaryStep_eq_of_ne_zero h_grad]

/-- Positive curvature forces `g_k ≠ 0`. -/
theorem gradient_ne_zero_of_pos_curvature
    (P : TrustRegionSubproblem n) (h_curv : 0 < P.gradientCurvature) :
    P.gradient ≠ 0 := by
  intro h_grad
  have h_zero : P.gradientCurvature = 0 := by
    simp [TrustRegionSubproblem.gradientCurvature, h_grad]
  exact h_curv.ne' h_zero

/-- If `g_kᵀ B_k g_k > 0`, then the Cauchy point is the source factor
`min (‖g_k‖^3 / (Δ_k * g_kᵀ B_k g_k)) 1` times the boundary steepest-descent step `s_k^G`. -/
theorem cauchyPoint_eq_scale_gradientBoundaryStep_of_pos_curvature
    (P : TrustRegionSubproblem n) (h_curv : 0 < P.gradientCurvature) :
    P.cauchyPoint =
      min ((‖P.gradient‖ ^ (3 : ℕ)) / (P.radius * P.gradientCurvature)) 1 •
        P.gradientBoundaryStep := by
  rw [P.cauchyPoint_eq, P.cauchyPointScale_eq_min_of_pos_curvature h_curv]

/-- Chapter06 Exercise 6.8 (2): if `0 < g_kᵀ B_k g_k`, hence automatically `g_k ≠ 0`, then the
Cauchy point is `-(min (‖g_k‖^3 / (Δ_k * g_kᵀ B_k g_k)) 1 * Δ_k / ‖g_k‖) • g_k`. -/
theorem cauchyPoint_eq_of_pos_curvature
    (P : TrustRegionSubproblem n)
    (h_curv : 0 < P.gradientCurvature) :
    P.cauchyPoint =
      -(min ((‖P.gradient‖ ^ (3 : ℕ)) / (P.radius * P.gradientCurvature)) 1 *
          P.radius / ‖P.gradient‖) •
        P.gradient := by
  have h_grad : P.gradient ≠ 0 := P.gradient_ne_zero_of_pos_curvature h_curv
  rw [P.cauchyPoint_eq_of_ne_zero h_grad]
  rw [P.cauchyPointScale_eq_min_of_pos_curvature h_curv]

end TrustRegionSubproblem
