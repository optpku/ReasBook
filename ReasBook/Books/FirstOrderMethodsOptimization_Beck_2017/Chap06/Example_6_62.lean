/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_8
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_24
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Lemma_6_26

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open Asymptotics

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Example 6.62 splits across the established chapter owners.

- `source-facing`: the Huber owner `H[μ]` from `Definition_6_8`;
- `core/canonical`: the completion-free differential owner `HasFDerivAt` together with the
  smoothness owner `is_l_smooth_on`;
- `bridge/view`: the Moreau-envelope, gradient, and proximal formulas upstream in Chapter 6.

The public gradient API in this file should stay on the source-facing Huber owner. The radial
singleton formula from `Example_6_19` is only internal bridge data used to remove auxiliary
singleton witnesses. Since `HasGradientAt` in mathlib is completion-dependent, the pointwise
formula is exposed through `HasFDerivAt` and the completion-free Riesz embedding
`InnerProductSpace.toDualMap ℝ E`, which carries the same vector formula without adding a public
`[CompleteSpace E]` assumption. -/

/-- Helper for Example 6.62: `radial_ball_clip μ x` is the radial projection of `x` onto the
closed ball of radius `μ`. -/
def radial_ball_clip (μ : PosReal) (x : E) : E :=
  if ‖x‖ ≤ μ then x else ((μ : ℝ) / ‖x‖) • x

/-- Helper for Example 6.62: the clipping map is the usual radial retraction written with
`max ‖x‖ μ`. -/
lemma radial_ball_clip_eq_radial_retraction (μ : PosReal) (x : E) :
    radial_ball_clip μ x = ((μ : ℝ) / max ‖x‖ μ) • x := by
  -- Split into the inside and outside branches of the closed ball.
  by_cases hx : ‖x‖ ≤ μ
  · rw [radial_ball_clip, if_pos hx, max_eq_right hx]
    rw [div_self (show (μ : ℝ) ≠ 0 by exact ne_of_gt μ.2), one_smul]
  · have hlt : μ < ‖x‖ := lt_of_not_ge hx
    rw [radial_ball_clip, if_neg hx, max_eq_left (le_of_lt hlt)]

/-- Helper for Example 6.62: radial clipping is the identity minus the radial shrinkage factor
from the norm proximal formula. -/
lemma radial_ball_clip_eq_sub_shrinkage (μ : PosReal) (x : E) :
    radial_ball_clip μ x = x - (1 - (μ : ℝ) / max ‖x‖ μ) • x := by
  -- Rewrite the clip as the radial retraction and simplify the scalar coefficient.
  rw [radial_ball_clip_eq_radial_retraction]
  calc
    ((μ : ℝ) / max ‖x‖ μ) • x = (1 - (1 - (μ : ℝ) / max ‖x‖ μ)) • x := by
      ring_nf
    _ = x - (1 - (μ : ℝ) / max ‖x‖ μ) • x := by
      rw [sub_smul, one_smul]

/-- Helper for Example 6.62: the norm at a nonzero point admits the expected linearization by the
radial functional, with a quadratic remainder bound. -/
lemma norm_linearization_bound (x y : E) (hx : x ≠ 0) :
    ‖‖y‖ - ‖x‖
        - (InnerProductSpace.toDualMap ℝ E (((1 / ‖x‖ : ℝ) • x))) (y - x)‖ ≤
      (1 / (2 * ‖x‖ : ℝ)) * ‖y - x‖ ^ (2 : ℕ) := by
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hnorm_le : (‖y‖ - ‖x‖) ^ (2 : ℕ) ≤ ‖y - x‖ ^ (2 : ℕ) := by
    -- The reverse triangle inequality bounds the scalar error term.
    have habs : |‖y‖ - ‖x‖| ≤ ‖y - x‖ := by
      simpa [norm_sub_rev] using abs_norm_sub_norm_le y x
    exact sq_le_sq.mpr <| by simpa using habs
  have htwo :
      2 * ‖x‖ * (‖y‖ - ‖x‖
          - (InnerProductSpace.toDualMap ℝ E (((1 / ‖x‖ : ℝ) • x))) (y - x)) =
        ‖y - x‖ ^ (2 : ℕ) - (‖y‖ - ‖x‖) ^ (2 : ℕ) := by
    -- Expanding `‖x + (y - x)‖²` isolates the quadratic remainder exactly.
    have hsquare :
        ‖y‖ ^ (2 : ℕ) = ‖x‖ ^ (2 : ℕ) + 2 * inner ℝ x (y - x) + ‖y - x‖ ^ (2 : ℕ) := by
      calc
        ‖y‖ ^ (2 : ℕ) = ‖x + (y - x)‖ ^ (2 : ℕ) := by
          congr 1
          abel_nf
        _ = ‖x‖ ^ (2 : ℕ) + 2 * inner ℝ x (y - x) + ‖y - x‖ ^ (2 : ℕ) := by
          simpa using norm_add_sq_real x (y - x)
    have hinner :
        (InnerProductSpace.toDualMap ℝ E (((1 / ‖x‖ : ℝ) • x))) (y - x) =
          (1 / ‖x‖ : ℝ) * inner ℝ x (y - x) := by
      simp
    rw [hinner]
    field_simp [hxnorm.ne']
    nlinarith [hsquare]
  have habs :
      |‖y - x‖ ^ (2 : ℕ) - (‖y‖ - ‖x‖) ^ (2 : ℕ)| ≤ ‖y - x‖ ^ (2 : ℕ) := by
    -- Both squared terms lie in `[0, ‖y - x‖²]`.
    rw [abs_sub_le_iff]
    constructor <;> nlinarith [sq_nonneg (‖y - x‖), sq_nonneg (‖y‖ - ‖x‖), hnorm_le]
  have hmain :
      |2 * ‖x‖ * (‖y‖ - ‖x‖
          - (InnerProductSpace.toDualMap ℝ E (((1 / ‖x‖ : ℝ) • x))) (y - x))| ≤
        ‖y - x‖ ^ (2 : ℕ) := by
    calc
      |2 * ‖x‖ * (‖y‖ - ‖x‖
          - (InnerProductSpace.toDualMap ℝ E (((1 / ‖x‖ : ℝ) • x))) (y - x))| =
          |‖y - x‖ ^ (2 : ℕ) - (‖y‖ - ‖x‖) ^ (2 : ℕ)| := by
            rw [htwo]
      _ ≤ ‖y - x‖ ^ (2 : ℕ) := habs
  have hpos : 0 < 2 * ‖x‖ := by positivity
  rw [Real.norm_eq_abs]
  rw [show (1 / (2 * ‖x‖ : ℝ)) * ‖y - x‖ ^ (2 : ℕ) = ‖y - x‖ ^ (2 : ℕ) / (2 * ‖x‖) by
    ring]
  exact (le_div_iff₀ hpos).2 <| by
    simpa [abs_mul, abs_of_pos hpos, mul_comm] using hmain

/-- Helper for Example 6.62: away from the origin, the norm has Fréchet derivative
`y ↦ ⟪x / ‖x‖, y⟫`. -/
lemma hasFDerivAt_norm_of_ne_zero (x : E) (hx : x ≠ 0) :
    HasFDerivAt (fun y : E ↦ ‖y‖)
      (InnerProductSpace.toDualMap ℝ E (((1 / ‖x‖ : ℝ) • x))) x := by
  -- The quadratic remainder estimate implies the remainder is little-o of `y - x`.
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  let δ : ℝ := 2 * ‖x‖ * c
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
  have hy_lt : ‖y - x‖ < δ := by
    simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev, δ] using hy
  have hy_le : ‖y - x‖ ≤ 2 * ‖x‖ * c := by
    exact le_of_lt hy_lt
  have hbound := norm_linearization_bound x y hx
  have hsmall :
      (1 / (2 * ‖x‖ : ℝ)) * ‖y - x‖ ^ (2 : ℕ) ≤ c * ‖y - x‖ := by
    -- On a small ball, the quadratic error is dominated by `c ‖y - x‖`.
    have hdiv : ‖y - x‖ / (2 * ‖x‖) ≤ c := by
      rw [div_le_iff₀ (by positivity : 0 < 2 * ‖x‖)]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hy_le
    calc
      (1 / (2 * ‖x‖ : ℝ)) * ‖y - x‖ ^ (2 : ℕ) = (‖y - x‖ / (2 * ‖x‖)) * ‖y - x‖ := by
        ring
      _ ≤ c * ‖y - x‖ := by
        exact mul_le_mul_of_nonneg_right hdiv (norm_nonneg _)
  exact le_trans hbound hsmall

/-- Helper for Example 6.62: the quadratic branch of the Huber function has derivative
`y ↦ ⟪x / μ, y⟫`. -/
lemma hasFDerivAt_huber_quadratic_branch (μ : PosReal) (x : E) :
    HasFDerivAt (fun y : E ↦ (1 / (2 * μ : ℝ)) * ‖y‖ ^ (2 : ℕ))
      (InnerProductSpace.toDualMap ℝ E (((1 / μ : ℝ) • x))) x := by
  -- Differentiate `‖y‖²`, then rescale by the quadratic Huber coefficient.
  have hsq :
      HasFDerivAt (fun y : E ↦ ‖y‖ ^ (2 : ℕ)) (2 • innerSL ℝ x) x :=
    (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hscaled :
      HasFDerivAt (fun y : E ↦ (1 / (2 * μ : ℝ)) * ‖y‖ ^ (2 : ℕ))
        ((1 / (2 * μ : ℝ)) • (2 • innerSL ℝ x)) x :=
    hsq.const_mul (1 / (2 * μ : ℝ))
  have hfrechet :
      ((1 / (2 * μ : ℝ)) • (2 • innerSL ℝ x)) =
        InnerProductSpace.toDualMap ℝ E (((1 / μ : ℝ) • x)) := by
    ext y
    simp
    field_simp [show (μ : ℝ) ≠ 0 by exact ne_of_gt μ.2]
  rw [hfrechet] at hscaled
  simpa using hscaled

/-- Helper for Example 6.62: on the boundary `‖x‖ = μ`, the Huber remainder is still controlled
by the same quadratic error with linear part `y ↦ ⟪x / μ, y⟫`. -/
lemma huber_boundary_remainder_bound (μ : PosReal) (x y : E) (hx : ‖x‖ = μ) :
    ‖H[μ] y - H[μ] x
        - (InnerProductSpace.toDualMap ℝ E (((1 / μ : ℝ) • x))) (y - x)‖ ≤
      (1 / (2 * μ : ℝ)) * ‖y - x‖ ^ (2 : ℕ) := by
  have hx_ne : x ≠ 0 := by
    intro hzero
    simp [hzero] at hx
    exact (ne_of_gt μ.2) hx.symm
  by_cases hy : ‖y‖ ≤ μ
  · -- On the quadratic side, the remainder is exactly `(1 / (2 μ)) ‖y - x‖²`.
    have hx_le : ‖x‖ ≤ μ := le_of_eq hx
    rw [huber_function_of_norm_le μ hy, huber_function_of_norm_le μ hx_le]
    have hsquare :
        ‖y‖ ^ (2 : ℕ) = ‖x‖ ^ (2 : ℕ) + 2 * inner ℝ x (y - x) + ‖y - x‖ ^ (2 : ℕ) := by
      calc
        ‖y‖ ^ (2 : ℕ) = ‖x + (y - x)‖ ^ (2 : ℕ) := by
          congr 1
          abel_nf
        _ = ‖x‖ ^ (2 : ℕ) + 2 * inner ℝ x (y - x) + ‖y - x‖ ^ (2 : ℕ) := by
          simpa using norm_add_sq_real x (y - x)
    have hinner :
        (InnerProductSpace.toDualMap ℝ E (((1 / μ : ℝ) • x))) (y - x) =
          (1 / μ : ℝ) * inner ℝ x (y - x) := by
      simp
    rw [Real.norm_eq_abs, hinner]
    have hformula :
        (1 / (2 * μ : ℝ)) * ‖y‖ ^ (2 : ℕ) - (1 / (2 * μ : ℝ)) * ‖x‖ ^ (2 : ℕ)
          - (1 / μ : ℝ) * inner ℝ x (y - x) =
            (1 / (2 * μ : ℝ)) * ‖y - x‖ ^ (2 : ℕ) := by
      field_simp [show (μ : ℝ) ≠ 0 by exact ne_of_gt μ.2]
      nlinarith [hsquare]
    have hnonneg : 0 ≤ (1 / (2 * μ : ℝ)) * ‖y - x‖ ^ (2 : ℕ) := by
      have hcoef : 0 ≤ (1 / (2 * μ : ℝ)) := by
        have htwo : (0 : ℝ) < 2 := by norm_num
        exact le_of_lt (one_div_pos.mpr (mul_pos htwo μ.2))
      exact mul_nonneg hcoef (sq_nonneg ‖y - x‖)
    rw [hformula, abs_of_nonneg hnonneg]
  · -- On the affine side, the boundary remainder is the norm remainder at the nonzero point `x`.
    have hy_lt : μ < ‖y‖ := lt_of_not_ge hy
    have hx_le : ‖x‖ ≤ μ := le_of_eq hx
    have hμ_quad : (1 / (2 * μ : ℝ)) * (μ : ℝ) ^ (2 : ℕ) = μ / 2 := by
      field_simp [show (μ : ℝ) ≠ 0 by exact ne_of_gt μ.2]
    have hinner :
        (InnerProductSpace.toDualMap ℝ E (((1 / μ : ℝ) • x))) (y - x) =
          (1 / μ : ℝ) * inner ℝ x (y - x) := by
      simp
    rw [huber_function_of_mu_lt_norm μ hy_lt, huber_function_of_norm_le μ hx_le, hx,
      Real.norm_eq_abs, hinner]
    have hbound := norm_linearization_bound x y hx_ne
    rw [hx, Real.norm_eq_abs, hinner] at hbound
    have hrewrite :
        |‖y‖ - μ / 2 - (1 / (2 * μ : ℝ)) * μ ^ (2 : ℕ) - (1 / μ : ℝ) * inner ℝ x (y - x)| =
          |‖y‖ - μ - (1 / μ : ℝ) * inner ℝ x (y - x)| := by
      have harith :
          ‖y‖ - μ / 2 - (1 / (2 * μ : ℝ)) * μ ^ (2 : ℕ) - (1 / μ : ℝ) * inner ℝ x (y - x) =
            ‖y‖ - μ - (1 / μ : ℝ) * inner ℝ x (y - x) := by
        rw [hμ_quad]
        ring_nf
      exact congrArg abs harith
    rw [hrewrite]
    exact hbound

/-- Helper for Example 6.62: the Huber function has Fréchet derivative
`y ↦ ⟪radial_ball_clip μ x / μ, y⟫` at every point. -/
lemma hasFDerivAt_huber_function_radial_ball_clip (μ : PosReal) (x : E) :
    HasFDerivAt (H[μ] : E → ℝ)
      (InnerProductSpace.toDualMap ℝ E (((1 / μ : ℝ) • radial_ball_clip μ x))) x := by
  by_cases hinside : ‖x‖ < μ
  · -- In the strict interior, the Huber function agrees locally with the quadratic branch.
    have hlocal :
        (H[μ] : E → ℝ) =ᶠ[nhds x] fun y : E ↦ (1 / (2 * μ : ℝ)) * ‖y‖ ^ (2 : ℕ) := by
      let δ : ℝ := μ - ‖x‖
      have hδ : 0 < δ := by
        dsimp [δ]
        linarith
      filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
      have hy_norm : ‖y‖ ≤ μ := by
        have hy_lt : ‖y - x‖ < δ := by
          simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev, δ] using hy
        calc
          ‖y‖ = ‖x + (y - x)‖ := by
            congr 1
            abel_nf
          _ ≤ ‖x‖ + ‖y - x‖ := norm_add_le _ _
        linarith
      exact huber_function_of_norm_le μ hy_norm
    have hclip : radial_ball_clip μ x = x := by
      simp [radial_ball_clip, le_of_lt hinside]
    simpa [hclip] using
      (hasFDerivAt_huber_quadratic_branch (E := E) μ x).congr_of_eventuallyEq hlocal
  · by_cases houtside : μ < ‖x‖
    · -- Outside the ball, the Huber function agrees locally with the affine norm branch.
      have hx_ne : x ≠ 0 := by
        intro hzero
        have houtside_zero : μ < (0 : ℝ) := by
          simpa [hzero] using houtside
        exact (not_lt_of_ge (le_of_lt (μ.2 : 0 < (μ : ℝ)))) houtside_zero
      have hlocal :
          (H[μ] : E → ℝ) =ᶠ[nhds x] fun y : E ↦ ‖y‖ - μ / 2 := by
        let δ : ℝ := (‖x‖ - μ) / 2
        have hδ : 0 < δ := by
          dsimp [δ]
          linarith
        filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
        have hy_lt : ‖y - x‖ < δ := by
          simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev, δ] using hy
        have hy_norm : μ < ‖y‖ := by
          have htri : ‖x‖ ≤ ‖y‖ + ‖y - x‖ := by
            calc
              ‖x‖ = ‖y + (x - y)‖ := by
                congr 1
                abel_nf
              _ ≤ ‖y‖ + ‖x - y‖ := norm_add_le _ _
              _ = ‖y‖ + ‖y - x‖ := by rw [norm_sub_rev]
          have hlower : ‖x‖ - ‖y - x‖ ≤ ‖y‖ := by
            linarith [htri]
          have hy_small : ‖y - x‖ < (‖x‖ - μ) / 2 := by
            simpa [δ] using hy_lt
          have hμ_lt : μ < ‖x‖ - ‖y - x‖ := by
            linarith [hy_small]
          linarith
        exact huber_function_of_mu_lt_norm μ hy_norm
      have hnorm :
          HasFDerivAt (fun y : E ↦ ‖y‖ - (μ : ℝ) / 2)
            (InnerProductSpace.toDualMap ℝ E (((1 / ‖x‖ : ℝ) • x))) x := by
        simpa using HasFDerivAt.sub_const (c := ((μ : ℝ) / 2))
          (hasFDerivAt_norm_of_ne_zero (E := E) x hx_ne)
      have hclip :
          InnerProductSpace.toDualMap ℝ E (((1 / μ : ℝ) • radial_ball_clip μ x)) =
            InnerProductSpace.toDualMap ℝ E (((1 / ‖x‖ : ℝ) • x)) := by
        rw [radial_ball_clip, if_neg (not_le_of_gt houtside), smul_smul]
        have hscalar : (1 / μ : ℝ) * ((μ : ℝ) / ‖x‖) = (1 / ‖x‖ : ℝ) := by
          field_simp [show (μ : ℝ) ≠ 0 by exact ne_of_gt μ.2, houtside.ne']
        rw [hscalar]
      rw [hclip]
      exact hnorm.congr_of_eventuallyEq hlocal
    · -- On the boundary, both branches share the same first-order term.
      have hboundary : ‖x‖ = μ := le_antisymm (le_of_not_gt houtside) (le_of_not_gt hinside)
      have hboundaryDeriv :
          HasFDerivAt (H[μ] : E → ℝ)
            (InnerProductSpace.toDualMap ℝ E (((1 / μ : ℝ) • x))) x := by
        rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
        intro c hc
        let δ : ℝ := 2 * (μ : ℝ) * c
        have hδ : 0 < δ := by
          have hμ : 0 < (μ : ℝ) := μ.2
          dsimp [δ]
          nlinarith
        filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
        have hy_lt : ‖y - x‖ < δ := by
          simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev, δ] using hy
        have hy_le : ‖y - x‖ ≤ 2 * (μ : ℝ) * c := by
          exact le_of_lt hy_lt
        have hbound := huber_boundary_remainder_bound (E := E) μ x y hboundary
        have hsmall :
            (1 / (2 * μ : ℝ)) * ‖y - x‖ ^ (2 : ℕ) ≤ c * ‖y - x‖ := by
          have hpos : 0 < (2 : ℝ) * (μ : ℝ) := by
            have htwo : (0 : ℝ) < 2 := by norm_num
            exact mul_pos htwo μ.2
          have hdiv : ‖y - x‖ / (2 * (μ : ℝ)) ≤ c := by
            rw [div_le_iff₀ hpos]
            simpa [mul_comm, mul_left_comm, mul_assoc] using hy_le
          calc
            (1 / (2 * μ : ℝ)) * ‖y - x‖ ^ (2 : ℕ) = (‖y - x‖ / (2 * (μ : ℝ))) * ‖y - x‖ := by
              ring
            _ ≤ c * ‖y - x‖ := by
              exact mul_le_mul_of_nonneg_right hdiv (norm_nonneg _)
        exact le_trans hbound hsmall
      have hclip : radial_ball_clip μ x = x := by
        simp [radial_ball_clip, hboundary.le]
      simpa [hclip] using hboundaryDeriv

/-- Helper for Example 6.62: radial clipping is exactly the singleton projection onto the closed
ball of radius `μ`. -/
lemma projection_mapping_closedBall_eq_singleton_radial_ball_clip (μ : PosReal) (x : E) :
    P[Metric.closedBall (0 : E) μ] x = {radial_ball_clip μ x} := by
  -- Reuse the closed-ball projection owner formula and rewrite its radial retraction.
  rw [projection_mapping_closedBall_eq_singleton_radialRetraction (c := (0 : E)) (x := x)
      (r := μ) (by exact le_of_lt μ.2)]
  simp [radial_ball_clip_eq_radial_retraction, sub_zero]

/-- Helper for Example 6.62: the radial clipping map satisfies the firm nonexpansive inequality
for closed-ball projections. -/
lemma radial_ball_clip_firmly_nonexpansive (μ : PosReal) (x y : E) :
    inner ℝ (radial_ball_clip μ x - radial_ball_clip μ y) (x - y) ≥
      ‖radial_ball_clip μ x - radial_ball_clip μ y‖ ^ (2 : ℕ) := by
  let C : Set E := Metric.closedBall (0 : E) μ
  have hpx_set : P[C] x = {radial_ball_clip μ x} := by
    simpa [C] using projection_mapping_closedBall_eq_singleton_radial_ball_clip (E := E) μ x
  have hpy_set : P[C] y = {radial_ball_clip μ y} := by
    simpa [C] using projection_mapping_closedBall_eq_singleton_radial_ball_clip (E := E) μ y
  have hpx : radial_ball_clip μ x ∈ P[C] x := by
    rw [hpx_set]
    simp
  have hpy : radial_ball_clip μ y ∈ P[C] y := by
    rw [hpy_set]
    simp
  have hpx_mem : radial_ball_clip μ x ∈ C := mem_of_mem_projection_mapping hpx
  have hpy_mem : radial_ball_clip μ y ∈ C := mem_of_mem_projection_mapping hpy
  have hpx_iInf : ‖x - radial_ball_clip μ x‖ = ⨅ z : C, ‖x - z‖ := by
    simpa [C, norm_sub_rev] using norm_eq_iInf_of_mem_projection_mapping hpx
  have hpy_iInf : ‖y - radial_ball_clip μ y‖ = ⨅ z : C, ‖y - z‖ := by
    simpa [C, norm_sub_rev] using norm_eq_iInf_of_mem_projection_mapping hpy
  have hpx_var :
      ∀ z ∈ C, inner ℝ (x - radial_ball_clip μ x) (z - radial_ball_clip μ x) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero (convex_closedBall (0 : E) μ) hpx_mem).1 hpx_iInf
  have hpy_var :
      ∀ z ∈ C, inner ℝ (y - radial_ball_clip μ y) (z - radial_ball_clip μ y) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero (convex_closedBall (0 : E) μ) hpy_mem).1 hpy_iInf
  have h1 :
      inner ℝ (x - radial_ball_clip μ x)
        (radial_ball_clip μ y - radial_ball_clip μ x) ≤ 0 :=
    hpx_var (radial_ball_clip μ y) hpy_mem
  have h2 :
      inner ℝ (y - radial_ball_clip μ y)
        (radial_ball_clip μ x - radial_ball_clip μ y) ≤ 0 :=
    hpy_var (radial_ball_clip μ x) hpx_mem
  -- Add the two variational inequalities and rearrange the resulting inner products.
  have h1' :
      inner ℝ (x - radial_ball_clip μ x)
        (radial_ball_clip μ x - radial_ball_clip μ y) ≥ 0 := by
    calc
      inner ℝ (x - radial_ball_clip μ x) (radial_ball_clip μ x - radial_ball_clip μ y) =
          inner ℝ (x - radial_ball_clip μ x) (-(radial_ball_clip μ y - radial_ball_clip μ x)) := by
            congr 1
            abel_nf
      _ = - inner ℝ (x - radial_ball_clip μ x) (radial_ball_clip μ y - radial_ball_clip μ x) := by
            rw [inner_neg_right]
      _ ≥ 0 := by exact neg_nonneg.mpr h1
  have h2' :
      inner ℝ (radial_ball_clip μ y - y)
        (radial_ball_clip μ x - radial_ball_clip μ y) ≥ 0 := by
    calc
      inner ℝ (radial_ball_clip μ y - y) (radial_ball_clip μ x - radial_ball_clip μ y) =
          inner ℝ (-(y - radial_ball_clip μ y)) (radial_ball_clip μ x - radial_ball_clip μ y) := by
            congr 1
            abel_nf
      _ = - inner ℝ (y - radial_ball_clip μ y) (radial_ball_clip μ x - radial_ball_clip μ y) := by
            rw [inner_neg_left]
      _ ≥ 0 := by exact neg_nonneg.mpr h2
  have hsplit :
      inner ℝ (radial_ball_clip μ x - radial_ball_clip μ y) (x - y) =
        inner ℝ (x - radial_ball_clip μ x) (radial_ball_clip μ x - radial_ball_clip μ y) +
          inner ℝ (radial_ball_clip μ x - radial_ball_clip μ y)
            (radial_ball_clip μ x - radial_ball_clip μ y) +
          inner ℝ (radial_ball_clip μ y - y)
            (radial_ball_clip μ x - radial_ball_clip μ y) := by
    calc
      inner ℝ (radial_ball_clip μ x - radial_ball_clip μ y) (x - y) =
          inner ℝ (radial_ball_clip μ x - radial_ball_clip μ y)
            ((x - radial_ball_clip μ x) + (radial_ball_clip μ x - radial_ball_clip μ y) +
              (radial_ball_clip μ y - y)) := by
                congr 1
                abel_nf
      _ = inner ℝ (x - radial_ball_clip μ x) (radial_ball_clip μ x - radial_ball_clip μ y) +
            inner ℝ (radial_ball_clip μ x - radial_ball_clip μ y)
              (radial_ball_clip μ x - radial_ball_clip μ y) +
            inner ℝ (radial_ball_clip μ y - y)
              (radial_ball_clip μ x - radial_ball_clip μ y) := by
                rw [inner_add_right, inner_add_right, real_inner_comm,
                  real_inner_comm (radial_ball_clip μ x - radial_ball_clip μ y)
                    (radial_ball_clip μ y - y)]
  calc
    ‖radial_ball_clip μ x - radial_ball_clip μ y‖ ^ (2 : ℕ) =
        inner ℝ (radial_ball_clip μ x - radial_ball_clip μ y)
          (radial_ball_clip μ x - radial_ball_clip μ y) := by
            rw [real_inner_self_eq_norm_sq]
    _ ≤ inner ℝ (radial_ball_clip μ x - radial_ball_clip μ y) (x - y) := by
          rw [hsplit]
          linarith

/-- Helper for Example 6.62: radial clipping is `1`-Lipschitz. -/
lemma radial_ball_clip_nonexpansive (μ : PosReal) :
    LipschitzWith 1 (radial_ball_clip μ : E → E) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  have hfirm := radial_ball_clip_firmly_nonexpansive (E := E) μ x y
  by_cases hzero : radial_ball_clip μ x = radial_ball_clip μ y
  · simp [hzero]
  · have hnorm_sq_le :
        ‖radial_ball_clip μ x - radial_ball_clip μ y‖ ^ (2 : ℕ) ≤
          ‖radial_ball_clip μ x - radial_ball_clip μ y‖ * ‖x - y‖ := by
      have hinner_le :
          inner ℝ (radial_ball_clip μ x - radial_ball_clip μ y) (x - y) ≤
            ‖radial_ball_clip μ x - radial_ball_clip μ y‖ * ‖x - y‖ :=
        real_inner_le_norm _ _
      linarith
    have hnorm_pos : 0 < ‖radial_ball_clip μ x - radial_ball_clip μ y‖ :=
      norm_pos_iff.mpr (sub_ne_zero.mpr hzero)
    rw [pow_two] at hnorm_sq_le
    simpa [mul_assoc] using le_of_mul_le_mul_left hnorm_sq_le hnorm_pos

section Smooth

-- Proof sketch: prove differentiability and the `(1 / μ)`-Lipschitz derivative bound for `H[μ]`
-- using the explicit clipped-ball derivative field, then unfold `is_l_smooth_on`.
/-- Example 6.62: for a positive parameter `μ`, the Huber function `H[μ]` is globally
`(1 / μ)`-smooth. -/
theorem huber_function_is_inv_mu_smooth (μ : PosReal) :
    is_l_smooth_on (H[μ] : E → ℝ) Set.univ (Real.toNNReal ((1 : ℝ) / μ)) := by
  rw [is_l_smooth_on]
  refine ⟨?_, ?_⟩
  · intro x _
    -- The explicit Fréchet derivative gives differentiability at every point.
    exact (hasFDerivAt_huber_function_radial_ball_clip (E := E) μ x).differentiableAt
  · -- The derivative field is `(1 / μ)` times the clipped-ball projection field.
    rw [lipschitzOnWith_iff_norm_sub_le]
    intro x _ y _
    have hx :
        fderiv ℝ (H[μ] : E → ℝ) x =
          InnerProductSpace.toDualMap ℝ E (((1 / μ : ℝ) • radial_ball_clip μ x)) :=
      (hasFDerivAt_huber_function_radial_ball_clip (E := E) μ x).fderiv
    have hy :
        fderiv ℝ (H[μ] : E → ℝ) y =
          InnerProductSpace.toDualMap ℝ E (((1 / μ : ℝ) • radial_ball_clip μ y)) :=
      (hasFDerivAt_huber_function_radial_ball_clip (E := E) μ y).fderiv
    rw [hx, hy]
    calc
      ‖InnerProductSpace.toDualMap ℝ E (((1 / μ : ℝ) • radial_ball_clip μ x)) -
          InnerProductSpace.toDualMap ℝ E (((1 / μ : ℝ) • radial_ball_clip μ y))‖ =
          ‖((1 / μ : ℝ) • radial_ball_clip μ x) - ((1 / μ : ℝ) • radial_ball_clip μ y)‖ := by
            simpa using (InnerProductSpace.toDualMap ℝ E).norm_map
              ((((1 / μ : ℝ) • radial_ball_clip μ x) - ((1 / μ : ℝ) • radial_ball_clip μ y)))
      _ = ‖(1 / μ : ℝ) • (radial_ball_clip μ x - radial_ball_clip μ y)‖ := by
            rw [smul_sub]
      _ = |(1 / μ : ℝ)| * ‖radial_ball_clip μ x - radial_ball_clip μ y‖ := norm_smul _ _
      _ = (1 / μ : ℝ) * ‖radial_ball_clip μ x - radial_ball_clip μ y‖ := by
            have hμ_nonneg : 0 ≤ ((1 : ℝ) / (μ : ℝ)) := by
              exact le_of_lt (one_div_pos.mpr μ.2)
            rw [abs_of_nonneg hμ_nonneg]
      _ ≤ (1 / μ : ℝ) * ‖x - y‖ := by
            have hclip : ‖radial_ball_clip μ x - radial_ball_clip μ y‖ ≤ ‖x - y‖ := by
              simpa using (radial_ball_clip_nonexpansive (E := E) μ).norm_sub_le x y
            have hμ_nonneg : 0 ≤ ((1 : ℝ) / (μ : ℝ)) := by
              exact le_of_lt (one_div_pos.mpr μ.2)
            exact mul_le_mul_of_nonneg_left hclip hμ_nonneg
      _ = (Real.toNNReal ((1 : ℝ) / μ) : ℝ) * ‖x - y‖ := by
            rw [Real.coe_toNNReal ((1 : ℝ) / μ) (le_of_lt (one_div_pos.mpr μ.2))]

end Smooth

section Gradient

-- Proof sketch: rewrite the canonical clipped derivative field using the shrinkage factor from
-- Example 6.19.
/-- The Fréchet derivative of the Huber function at `x` is the Riesz functional associated to
`(1 / μ) • (x - u)` at the canonical radial shrinkage point
`u = (1 - μ / max {‖x‖, μ}) • x`. This is the completion-free source-facing rendering of the
textbook gradient formula `∇ H_μ(x) = (1 / μ) (x - prox_{μ‖·‖}(x))`, with the proximal point
written using the Chapter 6 owner formula from Example 6.19. -/
theorem hasFDerivAt_huber_function_inv_mu_smul_sub_shrinkage
    (μ : PosReal) (x : E) :
    HasFDerivAt (H[μ] : E → ℝ)
      (InnerProductSpace.toDualMap ℝ E
        (((1 : ℝ) / μ) • (x - (1 - (μ : ℝ) / max ‖x‖ μ) • x))) x := by
  -- Rewrite the clipped vector field into the shrinkage form from the text.
  simpa [radial_ball_clip_eq_sub_shrinkage] using
    hasFDerivAt_huber_function_radial_ball_clip (E := E) μ x

-- Proof sketch: simplify the clipped derivative field on the inside and outside branches.
/-- The Fréchet derivative of the Huber function is represented by the usual radial piecewise
vector field:
`(1 / μ) • x` on the ball `‖x‖ ≤ μ` and `(1 / ‖x‖) • x` outside it, i.e. `x / ‖x‖` in the
Euclidean notation of the text. -/
theorem hasFDerivAt_huber_function_piecewise (μ : PosReal) (x : E) :
    HasFDerivAt (H[μ] : E → ℝ)
      (InnerProductSpace.toDualMap ℝ E
        (if ‖x‖ ≤ μ then ((1 : ℝ) / μ) • x else (1 / ‖x‖) • x)) x := by
  by_cases hx : ‖x‖ ≤ μ
  · -- Inside the ball, clipping is the identity.
    simpa [radial_ball_clip, hx] using
      hasFDerivAt_huber_function_radial_ball_clip (E := E) μ x
  · -- Outside the ball, clipping rescales `x` onto the sphere of radius `μ`.
    have hlt : μ < ‖x‖ := lt_of_not_ge hx
    have hscalar : (1 / μ : ℝ) * ((μ : ℝ) / ‖x‖) = (1 / ‖x‖ : ℝ) := by
      field_simp [show (μ : ℝ) ≠ 0 by exact ne_of_gt μ.2, hlt.ne']
    convert hasFDerivAt_huber_function_radial_ball_clip (E := E) μ x using 1
    ext z
    simp only [one_div, InnerProductSpace.toDualMap_apply_apply, map_smul,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, radial_ball_clip, hx, if_false,
      smul_smul]
    calc
      ‖x‖⁻¹ * inner ℝ x z = ((μ : ℝ)⁻¹ * ((μ : ℝ) / ‖x‖)) * inner ℝ x z := by
        congr 1
        simpa [one_div] using hscalar.symm

end Gradient

end
