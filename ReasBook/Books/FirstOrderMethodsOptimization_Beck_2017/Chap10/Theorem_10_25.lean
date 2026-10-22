/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_21

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

variable {f g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
variable [hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf]
variable {α : ℝ} {x : ℕ → E} {L : ℕ → PosReal} {xStar : E}

local notation "F" => composite_model_objective f g

/- Theorem 10.25 is `source-facing` in the convex proximal-gradient analysis. The canonical owner
for the sublinear rate estimate is `proximal_gradient_convex_objective_gap_le` from Theorem 10.21,
so this item should be stated as its direct iteration-complexity corollary rather than by
introducing a new wrapper for the algorithm or the problem data. The explicit optimizer
`xStar ∈ XStar`, the distance bound `R`, and the ceiling-form iteration hypothesis are kept on the
theorem surface because they are the source-facing data of the textbook statement. -/

-- Proof sketch: apply `proximal_gradient_convex_objective_gap_le` at the iterate `k` and the
-- optimal point `xStar`, then bound `‖x 0 - xStar‖²` by `R²` using `hR`. The ceiling hypothesis
-- implies `α L_f R² / (2 ε) ≤ k`, so rearranging gives `α L_f R² / (2 k) ≤ ε`, and substituting
-- this into the Theorem 10.21 estimate yields the claimed accuracy bound.
/-- Theorem 10.25: under Assumption 10.1, if `f` is convex and the proximal-gradient iterates use
either the constant rule `L_k = L_f` or backtracking procedure B2, then any iterate index
`k ≥ ⌈α L_f R^2 / (2 ε)⌉` satisfies `F(x^k) - F_opt ≤ ε`, where `R` bounds the distance from the
initial point `x^0` to some optimizer `xStar ∈ X^*`. -/
theorem proximal_gradient_convex_objective_gap_le_of_ceiling_iteration_bound
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.SourceSublinearRateStepsizeRule x L htraj α)
    (hxStar : xStar ∈ XStar)
    (ε : PosReal) (R : ℝ) (hR : ‖x 0 - xStar‖ ≤ R)
    (k : ℕ)
    (hiter : Nat.ceil (α * (Lf : ℝ) * R ^ (2 : ℕ) / (2 * (ε : ℝ))) ≤ k) :
    F (x k) - (FOpt : EReal) ≤ ((ε : ℝ) : EReal) := by
  have hLf_pos : 0 < (Lf : ℝ) := by
    exact hproblem.sublinearRateStepsizeRule_lf_pos
      (sourceSublinearRateRule_sublinearRateStepsizeRule htraj hrule)
  have hα_pos : 0 < α := by
    exact hproblem.sublinearRateStepsizeRule_alpha_pos
      (sourceSublinearRateRule_sublinearRateStepsizeRule htraj hrule)
  have hαLf_pos : 0 < α * (Lf : ℝ) := mul_pos hα_pos hLf_pos
  by_cases hk : k = 0
  · subst hk
    have hq_nonpos :
        α * (Lf : ℝ) * R ^ (2 : ℕ) / (2 * (ε : ℝ)) ≤ (0 : ℝ) := by
      simpa using (Nat.le_of_ceil_le hiter : _ ≤ ((0 : ℕ) : ℝ))
    have hden_eps_pos : (0 : ℝ) < 2 * (ε : ℝ) := by
      exact mul_pos (by norm_num) ε.prop
    have hnum_nonpos : α * (Lf : ℝ) * R ^ (2 : ℕ) ≤ ((0 : ℕ) : ℝ) := by
      simpa using (div_le_iff₀ hden_eps_pos).1 hq_nonpos
    have hR_sq_nonneg : 0 ≤ R ^ (2 : ℕ) := by positivity
    have hR_sq_nonpos : R ^ (2 : ℕ) ≤ 0 := by
      by_contra hR_sq_pos
      have hnum_pos : ((0 : ℕ) : ℝ) < α * (Lf : ℝ) * R ^ (2 : ℕ) := by
        simpa using
          (show (0 : ℝ) < α * (Lf : ℝ) * R ^ (2 : ℕ) from
            mul_pos (mul_pos hα_pos hLf_pos) (lt_of_not_ge hR_sq_pos))
      exact (not_lt_of_ge hnum_nonpos) hnum_pos
    have hR_sq_eq_zero : R ^ (2 : ℕ) = 0 := by
      exact le_antisymm hR_sq_nonpos hR_sq_nonneg
    have hR_zero : R = 0 := by
      rw [pow_two] at hR_sq_eq_zero
      nlinarith
    have hnorm_zero : ‖x 0 - xStar‖ = 0 := by
      rw [hR_zero] at hR
      exact le_antisymm hR (norm_nonneg _)
    have hx0_eq : x 0 = xStar := by
      exact sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)
    have hFx0_eq : F (x 0) = (FOpt : EReal) := by
      simpa [hx0_eq] using
        hproblem.objective_eq_optimalValue_of_mem_optimalSet hxStar
    have hzero_le_eps : ((0 : ℝ) : EReal) ≤ ((ε : ℝ) : EReal) := by
      exact EReal.coe_le_coe_iff.mpr (le_of_lt ε.prop)
    simpa [hFx0_eq] using hzero_le_eps
  · have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
    have hk_one : 1 ≤ k := Nat.succ_le_of_lt hk_pos
    have hk_real_pos : 0 < (k : ℝ) := by
      exact_mod_cast hk_pos
    have hden_eps_pos : 0 < 2 * (ε : ℝ) := by
      exact mul_pos (by norm_num) ε.prop
    have hden_k_pos : 0 < 2 * (k : ℝ) := by
      exact mul_pos (by norm_num) hk_real_pos
    have hgap :=
      proximal_gradient_convex_objective_gap_le htraj hrule hxStar k hk_one
    have hq_le :
        α * (Lf : ℝ) * R ^ (2 : ℕ) / (2 * (ε : ℝ)) ≤ (k : ℝ) :=
      Nat.le_of_ceil_le hiter
    have hR_sq_le : ‖x 0 - xStar‖ ^ (2 : ℕ) ≤ R ^ (2 : ℕ) := by
      nlinarith [norm_nonneg (x 0 - xStar), hR]
    have hcoef_nonneg : 0 ≤ α * (Lf : ℝ) := le_of_lt hαLf_pos
    have hnum_le :
        α * (Lf : ℝ) * ‖x 0 - xStar‖ ^ (2 : ℕ) ≤
          α * (Lf : ℝ) * R ^ (2 : ℕ) := by
      simpa [mul_assoc] using mul_le_mul_of_nonneg_left hR_sq_le hcoef_nonneg
    have hbound_num :
        α * (Lf : ℝ) * ‖x 0 - xStar‖ ^ (2 : ℕ) ≤
          (ε : ℝ) * (2 * (k : ℝ)) := by
      calc
        α * (Lf : ℝ) * ‖x 0 - xStar‖ ^ (2 : ℕ) ≤
            α * (Lf : ℝ) * R ^ (2 : ℕ) := hnum_le
        _ ≤ (k : ℝ) * (2 * (ε : ℝ)) := by
          exact (div_le_iff₀ hden_eps_pos).1 hq_le
        _ = (ε : ℝ) * (2 * (k : ℝ)) := by ring
    have hbound_real :
        α * (Lf : ℝ) * ‖x 0 - xStar‖ ^ (2 : ℕ) / (2 * (k : ℝ)) ≤ (ε : ℝ) := by
      exact (div_le_iff₀ hden_k_pos).2 <| by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hbound_num
    have hbound :
        (((α * (Lf : ℝ) * ‖x 0 - xStar‖ ^ (2 : ℕ) / (2 * (k : ℝ)) : ℝ) : EReal)) ≤
          ((ε : ℝ) : EReal) := by
      exact EReal.coe_le_coe_iff.mpr hbound_real
    exact hgap.trans hbound

end
