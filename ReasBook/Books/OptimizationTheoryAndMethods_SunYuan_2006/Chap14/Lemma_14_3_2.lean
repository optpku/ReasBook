/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Extrema
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Algorithm_14_3_1

noncomputable section

section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "DualSpace" => StrongDual ℝ E

open scoped Subgradient

-- Layer triage:
-- * source-facing: this one-step distance-decrease lemma
-- * core/canonical: `subdifferential`
-- * bridge/view: `normalizedSubgradientDirection`

/-- Helper for Chapter14 Lemma 14.3.2: a nonminimizer has strictly larger objective value than a
global minimizer. -/
lemma objective_lt_at_nonminimizer_of_isMinOn
    {f : E → ℝ} {xk xStar : E}
    (hxStar : IsMinOn f Set.univ xStar)
    (hxk : ¬ IsMinOn f Set.univ xk) :
    f xStar < f xk := by
  -- Turn the global minimizer hypothesis into the pointwise order used by the contradiction.
  have hxStar' : ∀ y : E, f xStar ≤ f y := by
    simpa [isMinOn_univ_iff] using hxStar
  -- If `xk` were no larger than `xStar`, then `xk` would also minimize `f` on `Set.univ`.
  by_contra h_not_lt
  have hxk_le : f xk ≤ f xStar := le_of_not_gt h_not_lt
  have hxk' : ∀ y : E, f xk ≤ f y := by
    intro y
    exact le_trans hxk_le (hxStar' y)
  exact hxk (by simpa [isMinOn_univ_iff] using hxk')

/-- Helper for Chapter14 Lemma 14.3.2: evaluating a subgradient at the displacement from a
nonoptimal point to a minimizer is strictly negative. -/
lemma subgradient_eval_to_minimizer_lt_zero
    {f : E → ℝ} {xk xStar : E} {gk : DualSpace}
    (hxStar : IsMinOn f Set.univ xStar)
    (hxk : ¬ IsMinOn f Set.univ xk)
    (hgk : gk ∈ ∂ f(xk)) :
    gk (xStar - xk) < 0 := by
  -- Apply the defining affine support inequality at the global minimizer `xStar`.
  have h_subgrad := (mem_subdifferential_iff f xk gk).mp hgk xStar
  have h_eval_le : gk (xStar - xk) ≤ f xStar - f xk := by
    linarith
  -- The strict objective gap from the previous helper makes the support value negative.
  have h_gap : f xStar - f xk < 0 := by
    have h_obj := objective_lt_at_nonminimizer_of_isMinOn hxStar hxk
    linarith
  exact lt_of_le_of_lt h_eval_le h_gap

/-- Helper for Chapter14 Lemma 14.3.2: the squared distance after one normalized subgradient step
has the textbook expansion from equation `(14.3.9)`. -/
lemma norm_sq_subgradient_step_eq
    {xk xStar : E} {gk : DualSpace}
    (hgk_norm_pos : 0 < ‖gk‖) (α : ℝ) :
    ‖xk + α • normalizedSubgradientDirection gk - xStar‖ ^ 2 =
      ‖xk - xStar‖ ^ 2 + (2 * α / ‖gk‖) * gk (xStar - xk) + α ^ 2 := by
  let vk : E := (InnerProductSpace.toDual ℝ E).symm gk
  -- The Riesz representative has the same norm as the original dual subgradient.
  have hvk_norm : ‖vk‖ = ‖gk‖ := by
    simpa [vk] using
      (norm_toDual (𝕜 := ℝ) (E := E) ((InnerProductSpace.toDual ℝ E).symm gk)).symm
  -- Rewrite the evaluation with the subtraction order used in the textbook formula.
  have h_eval_swap : gk (xk - xStar) = -gk (xStar - xk) := by
    calc
      gk (xk - xStar) = gk (-(xStar - xk)) := by
        simp [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      _ = -gk (xStar - xk) := by
        rw [map_neg]
  -- Rewrite the updated point as a subtraction by the normalized Riesz representative.
  have hvec :
      xk + α • normalizedSubgradientDirection gk - xStar =
        (xk - xStar) - ((α / ‖gk‖) • vk) := by
    simp [normalizedSubgradientDirection_eq, vk, sub_eq_add_neg, div_eq_mul_inv, smul_smul,
      add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
  -- Expand the square and simplify the cross and quadratic terms separately.
  rw [hvec, norm_sub_sq_real]
  have h_inner :
      inner ℝ (xk - xStar) ((α / ‖gk‖) • vk) = (α / ‖gk‖) * (-gk (xStar - xk)) := by
    calc
      inner ℝ (xk - xStar) ((α / ‖gk‖) • vk)
          = (α / ‖gk‖) * inner ℝ (xk - xStar) vk := by
              rw [real_inner_smul_right]
      _ = (α / ‖gk‖) * gk (xk - xStar) := by
        rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
      _ = (α / ‖gk‖) * (-gk (xStar - xk)) := by
        rw [h_eval_swap]
  have h_norm :
      ‖(α / ‖gk‖) • vk‖ ^ 2 = α ^ 2 := by
    have hgk_norm_ne : ‖gk‖ ≠ 0 := ne_of_gt hgk_norm_pos
    calc
      ‖(α / ‖gk‖) • vk‖ ^ 2 = (‖α / ‖gk‖‖ * ‖vk‖) ^ 2 := by
        rw [norm_smul]
      _ = (|α / ‖gk‖| * ‖vk‖) ^ 2 := by
        rw [Real.norm_eq_abs]
      _ = (|α / ‖gk‖| * ‖gk‖) ^ 2 := by
        rw [hvk_norm]
      _ = |α| ^ 2 := by
        rw [abs_div, abs_of_nonneg hgk_norm_pos.le, div_eq_mul_inv, mul_assoc,
          inv_mul_cancel₀ hgk_norm_ne, mul_one]
      _ = α ^ 2 := by
        rw [sq_abs]
  rw [h_inner, h_norm, div_eq_mul_inv]
  ring

/-- Helper for Chapter14 Lemma 14.3.2: if the stepsize stays below the threshold from
equation `(14.3.11)`, then the squared distance strictly decreases. -/
lemma subgradient_step_sq_lt_of_alpha_lt_threshold
    {xk xStar : E} {gk : DualSpace} {α Tk : ℝ}
    (h_eval_lt : gk (xStar - xk) < 0)
    (hTk : Tk = -2 * gk (xStar - xk) / ‖gk‖)
    (hα_pos : 0 < α)
    (hα_lt : α < Tk) :
    ‖xk + α • normalizedSubgradientDirection gk - xStar‖ ^ 2 <
      ‖xk - xStar‖ ^ 2 := by
  -- Strict negativity of the evaluation rules out the zero subgradient and gives `‖gk‖ > 0`.
  have hgk_ne : gk ≠ 0 := by
    intro hgk_zero
    subst hgk_zero
    simpa using h_eval_lt
  have hgk_norm_pos : 0 < ‖gk‖ := norm_pos_iff.mpr hgk_ne
  -- Rewrite the squared distance using the chapter step expansion.
  rw [norm_sq_subgradient_step_eq (xk := xk) (xStar := xStar) (gk := gk) hgk_norm_pos α]
  have hprod_lt : α * (α - Tk) < 0 := by
    nlinarith
  have hscalar :
      (2 * α / ‖gk‖) * gk (xStar - xk) + α ^ 2 = α * (α - Tk) := by
    have hgk_norm_ne : ‖gk‖ ≠ 0 := ne_of_gt hgk_norm_pos
    rw [hTk, div_eq_mul_inv]
    field_simp [hgk_norm_ne]
    ring
  -- After substituting the threshold, the remaining scalar term is `α (α - Tk)`.
  have hdrop :
      ‖xk - xStar‖ ^ 2 + α * (α - Tk) < ‖xk - xStar‖ ^ 2 := by
    nlinarith
  rw [show ‖xk - xStar‖ ^ 2 + (2 * α / ‖gk‖) * gk (xStar - xk) + α ^ 2 =
      ‖xk - xStar‖ ^ 2 + α * (α - Tk) by rw [add_assoc, hscalar]]
  exact hdrop

/-- Chapter14 Lemma 14.3.2: let `f : E → ℝ` be convex, let `xStar` be a global
minimizer of `f`, let `xk` be a nonoptimal point, and let `gk ∈ ∂ f(xk)`. Then
there exists `Tk > 0` such that every positive stepsize `α < Tk` along the canonical Chapter 14
normalized subgradient direction `normalizedSubgradientDirection gk = -gk / ‖gk‖` strictly
decreases the Euclidean distance from `xk` to `xStar`. -/
theorem exists_pos_subgradient_step_dist_lt_of_isMinOn_of_not_isMinOn_of_mem_subdifferential
    (f : E → ℝ) (xk xStar : E) (gk : DualSpace)
    (h_convex : ConvexOn ℝ Set.univ f)
    (hxStar : IsMinOn f Set.univ xStar)
    (hxk : ¬ IsMinOn f Set.univ xk)
    (hgk : gk ∈ ∂ f(xk)) :
    ∃ Tk : ℝ, 0 < Tk ∧
      ∀ α : ℝ,
        ∀ hα_pos : 0 < α,
        ∀ hα_lt : α < Tk,
        ‖xk + α • normalizedSubgradientDirection gk - xStar‖ < ‖xk - xStar‖ := by
  -- The convexity hypothesis is part of the textbook statement, but the subgradient inequality
  -- already supplies the only convexity input needed in this proof.
  let _ := h_convex
  -- First recover the strict sign in equation `(14.3.10)`.
  have h_eval_lt :
      gk (xStar - xk) < 0 :=
    subgradient_eval_to_minimizer_lt_zero hxStar hxk hgk
  have hgk_ne : gk ≠ 0 := by
    intro hgk_zero
    subst hgk_zero
    simpa using h_eval_lt
  have hgk_norm_pos : 0 < ‖gk‖ := norm_pos_iff.mpr hgk_ne
  let Tk : ℝ := -2 * gk (xStar - xk) / ‖gk‖
  have hTk_pos : 0 < Tk := by
    -- The threshold is positive because the numerator is strictly positive and `‖gk‖ > 0`.
    dsimp [Tk]
    have hnum_pos : 0 < -2 * gk (xStar - xk) := by
      nlinarith
    exact div_pos hnum_pos hgk_norm_pos
  refine ⟨Tk, hTk_pos, ?_⟩
  intro α hα_pos hα_lt
  -- The threshold identity gives a strict decrease of the squared distance.
  have hsq_lt :
      ‖xk + α • normalizedSubgradientDirection gk - xStar‖ ^ 2 <
        ‖xk - xStar‖ ^ 2 := by
    exact subgradient_step_sq_lt_of_alpha_lt_threshold
      (xk := xk) (xStar := xStar) (gk := gk) h_eval_lt rfl hα_pos hα_lt
  -- Since both norms are nonnegative, the strict inequality of squares implies the strict
  -- inequality of norms.
  have h_left_nonneg : 0 ≤ ‖xk + α • normalizedSubgradientDirection gk - xStar‖ := norm_nonneg _
  have h_right_nonneg : 0 ≤ ‖xk - xStar‖ := norm_nonneg _
  nlinarith

end
