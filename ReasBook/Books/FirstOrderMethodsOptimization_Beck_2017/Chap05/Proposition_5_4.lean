/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Example_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Proposition_3_12
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Theorem_5_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open Metric
open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Proposition 5.4 is a `bridge/view` item over the Chapter 2 owner
`euclidean_distance_potential`. Local Chapter 5 precedent identifies `is_l_smooth_on` as the
correct owner surface for the smoothness clause, and Proposition 3.12 supplies the gradient input
in the Euclidean (`[FiniteDimensional ℝ E]`) setting. This file therefore keeps the
projection-gradient identity together with the chapter-owner smoothness statement and its explicit
norm-inequality companion. -/

-- Proof sketch: rewrite `euclidean_distance_potential C` as
-- `x ↦ ‖x‖^2 / 2 - (Metric.infDist x C)^2 / 2`. The gradient of the quadratic term is `x`, while
-- Proposition 3.12 identifies the gradient of the distance-squared term with `x - P_C(x)`.
-- Subtracting the two gradients gives `P_C(x)`.
/-- The half squared norm `x ↦ ‖x‖² / 2` has gradient witness `x` at every point of a real inner
product space. -/
theorem hasGradientAt_half_squared_norm_div_two (x : E) :
    HasGradientAt (fun y : E ↦ ‖y‖ ^ 2 / 2) x x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  convert (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_smul (1 / 2 : ℝ) using 1
  · ext y
    simp [Pi.smul_apply, div_eq_mul_inv, mul_comm]
  · ext y
    simp [InnerProductSpace.toDual_apply_apply]

/-- Companion gradient formula for `x ↦ ‖x‖² / 2`. -/
@[simp] theorem gradient_half_squared_norm_div_two (x : E) :
    ∇ (fun y : E ↦ ‖y‖ ^ 2 / 2) x = x :=
  (hasGradientAt_half_squared_norm_div_two x).gradient

variable [FiniteDimensional ℝ E]

section ProjectionGradient

variable (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

local notation "P" => projectionPoint C hC_nonempty hC_closed hC_convex

/-- Owner form for Proposition 5.4 (1): the Chapter 2 potential
`x ↦ (‖x‖² - d_C(x)²) / 2` has gradient witness `P_C(x)` at every point. -/
theorem hasGradientAt_euclidean_distance_potential (x : E) :
    HasGradientAt (euclidean_distance_potential C) (P x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hquad := (hasGradientAt_half_squared_norm_div_two x).hasFDerivAt
  have hdist :=
    (hasGradientAt_half_sq_infDist C hC_nonempty hC_closed hC_convex x).hasFDerivAt
  convert hquad.sub hdist using 1
  · ext y
    simp [euclidean_distance_potential]
    ring
  · ext y
    simp [InnerProductSpace.toDual_apply_apply]

/-- Proposition 5.4 (1): for a nonempty closed convex set `C` in a Euclidean space, the gradient
of `euclidean_distance_potential C` is the metric projection `P_C(x)`. -/
theorem gradient_euclidean_distance_potential_eq_metricProjection (x : E) :
    ∇ (euclidean_distance_potential C) x = P x :=
  (hasGradientAt_euclidean_distance_potential C hC_nonempty hC_closed hC_convex x).gradient

private theorem euclidean_distance_potential_is_l_smooth_of_nonempty_closed
    (C : Set E) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    is_l_smooth_on (euclidean_distance_potential C) Set.univ 1 := by
  rw [is_l_smooth_on_iff_lipschitzOnWith_gradient]
  refine ⟨?_, ?_⟩
  · intro x _
    have hx :=
      hasGradientAt_euclidean_distance_potential C hC_nonempty hC_closed hC_convex x
    exact hx.differentiableAt
  · rw [lipschitzOnWith_iff_norm_sub_le]
    intro x _ y _
    rw [gradient_euclidean_distance_potential_eq_metricProjection
        C hC_nonempty hC_closed hC_convex x,
      gradient_euclidean_distance_potential_eq_metricProjection
        C hC_nonempty hC_closed hC_convex y]
    simpa [dist_eq_norm] using
      (metricProjection_nonexpansive C hC_nonempty hC_closed hC_convex).dist_le_mul x y

end ProjectionGradient

-- Proof sketch: if `C = ∅`, then `euclidean_distance_potential C = x ↦ ‖x‖² / 2`, whose gradient
-- is the identity. Otherwise pass to `closure C`: `Metric.infDist` is unchanged by closure, while
-- `closure C` is nonempty, closed, and convex, so the nonempty closed case above applies.
/-- Proposition 5.4 (2): for a convex set `C` in a Euclidean space,
`euclidean_distance_potential C` is globally `1`-smooth. This removes the source's redundant
nonempty/closed hypotheses, since `d_C = d_closure C` and the empty-set case is just the half
squared norm. -/
theorem euclidean_distance_potential_is_l_smooth_on (C : Set E) (hC_convex : Convex ℝ C) :
    is_l_smooth_on (euclidean_distance_potential C) Set.univ 1 := by
  by_cases hC_nonempty : C.Nonempty
  · have hpot : euclidean_distance_potential (closure C) = euclidean_distance_potential C := by
      funext x
      simp [euclidean_distance_potential, Metric.infDist_closure]
    simpa [hpot] using
      euclidean_distance_potential_is_l_smooth_of_nonempty_closed
        (closure C) hC_nonempty.closure isClosed_closure hC_convex.closure
  · rw [Set.not_nonempty_iff_eq_empty.mp hC_nonempty, euclidean_distance_potential_empty]
    rw [is_l_smooth_on_iff_lipschitzOnWith_gradient]
    refine ⟨?_, ?_⟩
    · intro x _
      exact (hasGradientAt_half_squared_norm_div_two x).differentiableAt
    · rw [lipschitzOnWith_iff_norm_sub_le]
      intro x _ y _
      rw [(hasGradientAt_half_squared_norm_div_two x).gradient,
        (hasGradientAt_half_squared_norm_div_two y).gradient]
      simp

/-- Companion consequence for Proposition 5.4 (2): the gradient field of
`euclidean_distance_potential C` satisfies the displayed `1`-Lipschitz bound. -/
theorem norm_gradient_euclidean_distance_potential_sub_le
    (C : Set E) (hC_convex : Convex ℝ C) (x y : E) :
    ‖∇ (euclidean_distance_potential C) x - ∇ (euclidean_distance_potential C) y‖ ≤ ‖x - y‖ := by
  have hs := euclidean_distance_potential_is_l_smooth_on C hC_convex
  rw [is_l_smooth_on_iff_forall_norm_sub_le] at hs
  simpa using
    hs.2 x (by simp) y (by simp)

end
