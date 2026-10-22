/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Text_8_0_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Example_13_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private theorem infDist_closedBall_zero_eq_max_sub (ρ : Set.Ioi (0 : ℝ)) (u : H) :
    Metric.infDist u (Metric.closedBall (0 : H) (ρ : ℝ)) = max (‖u‖ - (ρ : ℝ)) 0 := by
  by_cases hu : ‖u‖ ≤ (ρ : ℝ)
  · have hu_mem : u ∈ Metric.closedBall (0 : H) (ρ : ℝ) := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hu
    rw [Metric.infDist_zero_of_mem hu_mem, max_eq_right (sub_nonpos.mpr hu)]
  · have hρu : (ρ : ℝ) < ‖u‖ := lt_of_not_ge hu
    have hu_pos : 0 < ‖u‖ := lt_trans ρ.2 hρu
    have hu_ne : ‖u‖ ≠ 0 := hu_pos.ne'
    let p : H := ((ρ : ℝ) / ‖u‖) • u
    have hp_mem : p ∈ Metric.closedBall (0 : H) (ρ : ℝ) := by
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      change ‖((ρ : ℝ) / ‖u‖) • u‖ ≤ (ρ : ℝ)
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos ρ.2 hu_pos)]
      calc
        ((ρ : ℝ) / ‖u‖) * ‖u‖ = (ρ : ℝ) := by field_simp [hu_ne]
        _ ≤ (ρ : ℝ) := le_rfl
    have hp_dist : dist u p = ‖u‖ - (ρ : ℝ) := by
      calc
        dist u p = ‖u - p‖ := by rw [dist_eq_norm]
        _ = ‖(1 - (ρ : ℝ) / ‖u‖) • u‖ := by
          congr 1
          calc
            u - p = (1 : ℝ) • u - ((ρ : ℝ) / ‖u‖) • u := by simp [p]
            _ = (1 - (ρ : ℝ) / ‖u‖) • u := by rw [sub_smul]
        _ = |1 - (ρ : ℝ) / ‖u‖| * ‖u‖ := norm_smul _ _
        _ = (1 - (ρ : ℝ) / ‖u‖) * ‖u‖ := by
          have hdiv : (ρ : ℝ) / ‖u‖ ≤ 1 := by
            rw [div_le_iff₀ hu_pos, one_mul]
            exact hρu.le
          rw [abs_of_nonneg]
          exact sub_nonneg.mpr hdiv
        _ = ‖u‖ - (ρ : ℝ) := by
          field_simp [hu_ne]
    have hmax : max (‖u‖ - (ρ : ℝ)) 0 = ‖u‖ - (ρ : ℝ) :=
      max_eq_left (sub_nonneg.mpr hρu.le)
    apply le_antisymm
    · simpa [hmax, hp_dist] using
        (Metric.infDist_le_dist_of_mem hp_mem :
          Metric.infDist u (Metric.closedBall (0 : H) (ρ : ℝ)) ≤ dist u p)
    · rw [hmax, Metric.le_infDist ⟨p, hp_mem⟩]
      intro y hy
      have hy_norm : ‖y‖ ≤ (ρ : ℝ) := by
        simpa [Metric.mem_closedBall, dist_eq_norm] using hy
      have htriangle : ‖u‖ ≤ dist u y + ‖y‖ := by
        simpa [dist_eq_norm, sub_add_cancel] using norm_add_le (u - y) y
      linarith

-- Proof sketch: apply Example 13.5 with `C = Metric.closedBall (0 : H) ρ`, rewrite
-- `Metric.infDist u C` via the closed-ball distance formula, and identify the resulting scalar
-- profile with `huberFunction ρ` evaluated at `‖u‖`.
/-- Example 13.7: the Fenchel conjugate of `ι_{B(0;ρ)} + ‖·‖² / 2` is the radial Huber profile
`u ↦ huberFunction ρ ‖u‖`, viewed in `EReal`. -/
theorem fenchelConjugate_indicator_add_halfSquaredNorm_closedBall_eq_huberFunction_comp_norm
    (ρ : Set.Ioi (0 : ℝ)) :
    ((ι[Metric.closedBall (0 : H) (ρ : ℝ)] +
        halfSquaredNorm).asEReal)∗ =
      (huberFunction ρ ∘ (norm : H → ℝ)).toEReal.asEReal := by
  have hconj :=
    fenchelConjugate_indicator_add_halfSquaredNorm_eq_sqNorm_sub_sqInfDist_div_two
      (Metric.closedBall (0 : H) (ρ : ℝ))
      ⟨0, by simpa [Metric.mem_closedBall, dist_eq_norm] using (show 0 ≤ (ρ : ℝ) from ρ.2.le)⟩
  calc
    ((ι[Metric.closedBall (0 : H) (ρ : ℝ)] + halfSquaredNorm).asEReal)∗
        = fun u : H ↦
            ((((‖u‖ ^ 2 - Metric.infDist u (Metric.closedBall (0 : H) (ρ : ℝ)) ^ 2) / 2 : ℝ) :
              EReal)) := hconj
    _ = (huberFunction ρ ∘ (norm : H → ℝ)).toEReal.asEReal := by
      funext u
      by_cases hu : (ρ : ℝ) < ‖u‖
      · have hinf :
            Metric.infDist u (Metric.closedBall (0 : H) (ρ : ℝ)) = ‖u‖ - (ρ : ℝ) := by
            rw [infDist_closedBall_zero_eq_max_sub ρ u,
              max_eq_left (sub_nonneg.mpr hu.le)]
        have hhuber : huberFunction ρ ‖u‖ = (ρ : ℝ) * ‖u‖ - (ρ : ℝ) ^ 2 / 2 := by
          have hu_abs : (ρ : ℝ) < |‖u‖| := by
            simpa [abs_of_nonneg (norm_nonneg u)] using hu
          simpa [abs_of_nonneg (norm_nonneg u)] using huberFunction_eq_of_lt ρ hu_abs
        rw [Function.asEReal_apply, Function.toEReal_apply, Function.comp_apply, hhuber, hinf]
        congr 1
        ring
      · have hu_le : ‖u‖ ≤ (ρ : ℝ) := le_of_not_gt hu
        have hinf :
            Metric.infDist u (Metric.closedBall (0 : H) (ρ : ℝ)) = 0 := by
          rw [infDist_closedBall_zero_eq_max_sub ρ u,
            max_eq_right (sub_nonpos.mpr hu_le)]
        have hhuber : huberFunction ρ ‖u‖ = ‖u‖ ^ 2 / 2 := by
          have hu_abs : |‖u‖| ≤ (ρ : ℝ) := by
            simpa [abs_of_nonneg (norm_nonneg u)] using hu_le
          simpa [abs_of_nonneg (norm_nonneg u)] using huberFunction_eq_of_le ρ hu_abs
        rw [Function.asEReal_apply, Function.toEReal_apply, Function.comp_apply, hhuber, hinf]
        congr 1
        ring

end

-- Proof sketch: specialize the Hilbert-space formula to `H = ℝ`, rewrite the closed ball
-- `Metric.closedBall (0 : ℝ) ρ` through `Real.norm_eq_abs`, and note that the radial Huber
-- profile becomes `huberFunction ρ` itself.
/-- In one dimension, the Fenchel conjugate of the closed-ball indicator plus quadratic is the
canonical extended-real view of the Huber function with threshold `ρ`. -/
theorem fenchelConjugate_indicator_add_halfSquaredNorm_closedBall_eq_huberFunction
    (ρ : Set.Ioi (0 : ℝ)) :
    ((ι[Metric.closedBall (0 : ℝ) (ρ : ℝ)] +
        halfSquaredNorm).asEReal)∗ =
      (huberFunction ρ).toEReal.asEReal := by
  calc
    ((ι[Metric.closedBall (0 : ℝ) (ρ : ℝ)] + halfSquaredNorm).asEReal)∗
        = (huberFunction ρ ∘ (norm : ℝ → ℝ)).toEReal.asEReal :=
          fenchelConjugate_indicator_add_halfSquaredNorm_closedBall_eq_huberFunction_comp_norm
            ρ
    _ = (huberFunction ρ).toEReal.asEReal := by
      funext x
      by_cases hx : (ρ : ℝ) < |x|
      · simp [Function.comp_def, huberFunction, Real.norm_eq_abs, hx]
      · simp [Function.comp_def, huberFunction, Real.norm_eq_abs, hx]

end ERealFunction
