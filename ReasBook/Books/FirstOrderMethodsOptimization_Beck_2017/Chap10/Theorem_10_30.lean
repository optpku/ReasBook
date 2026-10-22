/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_29

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

variable {f g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
variable [hproblem : IsCompositeSmoothMinimizationProblem f g XStar FOpt Lf]
variable {σ : PosReal} {α : ℝ} {x : ℕ → E} {L : ℕ → PosReal} {xStar : E}

/- Theorem 10.30 is `source-facing` in the strongly-convex proximal-gradient complexity layer.

Domain sampling in the existing Chapter 10 API identifies:
- `IsCompositeSmoothMinimizationProblem` as the owner of Assumption 10.1;
- `is_proximal_gradient_trajectory` as the owner of the iterate sequence `x^k`;
- `hproblem.SublinearRateStepsizeRule x L htraj α` from Remark 10.19 as the chapter owner of the
  admissible constant/B2 stepsize regime together with its rate factor `α`;
- `proximal_gradient_strongly_convex_objective_gap_le` from Theorem 10.29 as the canonical
  geometric objective-gap estimate already attached to that owner stack.

This file is therefore a direct logarithmic-iteration corollary of that upstream theorem, not a
place for a parallel rate package or a second condition-number API. Primitive data are only the
strong-convexity hypothesis, the proximal-gradient trajectory, the chapter stepsize rule, the
optimizer `xStar`, and the radius bound `R`; the logarithmic complexity estimate is derived API.
The theorem surface should therefore reuse the existing objective owner `F = f + g` and the
chapter notation `κ(Lf, σ)` rather than spelling those notions through longer local expansions. -/

local notation "F" => composite_model_objective f g
local notation "κ" => κ(Lf, σ)

/-- Helper for Theorem 10.30: the textbook backtracking constant
`α = max {η, s / L_f}` is equivalent to the stepsize cap `α L_f = max {η L_f, s}`. -/
lemma proximal_gradient_alpha_mul_lf_eq_max_stepsize
    {s : PosReal} {η : ProximalGradientBacktrackingGrowthFactor}
    (hLf : 0 < (Lf : ℝ))
    (hα : α = max (η : ℝ) ((s : ℝ) / (Lf : ℝ))) :
    max ((η : ℝ) * (Lf : ℝ)) (s : ℝ) = α * (Lf : ℝ) := by
  -- Split on which branch of the textbook `max` determines `α`.
  rw [hα]
  by_cases hη : (η : ℝ) ≤ (s : ℝ) / (Lf : ℝ)
  · have hs :
        (s : ℝ) = ((s : ℝ) / (Lf : ℝ)) * (Lf : ℝ) := by
      field_simp [hLf.ne']
    have hηLf : (η : ℝ) * (Lf : ℝ) ≤ (s : ℝ) := by
      nlinarith
    rw [max_eq_right hηLf, max_eq_right hη]
    exact hs
  · have hηlt : (s : ℝ) / (Lf : ℝ) < (η : ℝ) := lt_of_not_ge hη
    have hsLf : (s : ℝ) < (η : ℝ) * (Lf : ℝ) := by
      have hmul :
          ((s : ℝ) / (Lf : ℝ)) * (Lf : ℝ) < (η : ℝ) * (Lf : ℝ) := by
        exact mul_lt_mul_of_pos_right hηlt hLf
      have hs :
          ((s : ℝ) / (Lf : ℝ)) * (Lf : ℝ) = (s : ℝ) := by
        field_simp [hLf.ne']
      rw [hs] at hmul
      exact hmul
    rw [max_eq_left (le_of_lt hsLf), max_eq_left (le_of_lt hηlt)]

/-- Helper for Theorem 10.30: reindexing Theorem 10.29(c) from `k + 1` to a positive natural
index yields the geometric objective-gap estimate at `x^k`. -/
lemma proximal_gradient_strongly_convex_objective_gap_le_at_pnat
    (hstrong : StrongConvexOn (effective_domain f) (σ : ℝ) (fun y ↦ (f y).toReal))
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.SublinearRateStepsizeRule x L htraj α)
    (hL_bound : ∀ n, (L n : ℝ) ≤ α * (Lf : ℝ))
    (hxStar : xStar ∈ XStar)
    (k : ℕ+) :
    F (x k) - (FOpt : EReal) ≤
      ((((α * (Lf : ℝ)) / 2) *
          (1 - 1 / (α * κ)) ^ (k : ℕ) *
          ‖x 0 - xStar‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  -- Apply Theorem 10.29(c) to the predecessor index and rewrite `natPred + 1 = k`.
  have hgap :=
    proximal_gradient_strongly_convex_objective_gap_le
      (hproblem := hproblem)
      hstrong
      htraj
      hrule
      hL_bound
      hxStar
      k.natPred
  simpa [PNat.natPred_add_one] using hgap

/-- Helper for Theorem 10.30: if the initial distance is nonzero, then the geometric contraction
factor from Theorem 10.29 is nonnegative. -/
lemma proximal_gradient_contraction_factor_nonneg_of_initial_distance_ne_zero
    (hstrong : StrongConvexOn (effective_domain f) (σ : ℝ) (fun y ↦ (f y).toReal))
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.SublinearRateStepsizeRule x L htraj α)
    (hL_bound : ∀ n, (L n : ℝ) ≤ α * (Lf : ℝ))
    (hxStar : xStar ∈ XStar)
    (hinit_ne : ‖x 0 - xStar‖ ^ (2 : ℕ) ≠ 0) :
    0 ≤ 1 - 1 / (α * κ) := by
  have hstep0 :
      ‖x (0 + 1) - xStar‖ ^ (2 : ℕ) ≤
        (1 - 1 / (α * κ)) * ‖x 0 - xStar‖ ^ (2 : ℕ) :=
    proximal_gradient_strongly_convex_step_distance_sq_le
      (hproblem := hproblem)
      hstrong
      htraj
      hrule
      hL_bound
      hxStar
      0
  have hdist_nonneg : 0 ≤ ‖x (0 + 1) - xStar‖ ^ (2 : ℕ) := by
    positivity
  have hinit_nonneg : 0 ≤ ‖x 0 - xStar‖ ^ (2 : ℕ) := by
    positivity
  have hinit_pos : 0 < ‖x 0 - xStar‖ ^ (2 : ℕ) :=
    lt_of_le_of_ne hinit_nonneg (Ne.symm hinit_ne)
  -- A negative contraction factor would force the right-hand side below zero.
  by_contra hq_nonneg
  have hq_neg : 1 - 1 / (α * κ) < 0 := lt_of_not_ge hq_nonneg
  have hright_neg :
      (1 - 1 / (α * κ)) * ‖x 0 - xStar‖ ^ (2 : ℕ) < 0 := by
    exact mul_neg_of_neg_of_pos hq_neg hinit_pos
  linarith

/-- Helper for Theorem 10.30: once the uniform stepsize control `L_k ≤ α L_f` is available, the
logarithmic lower bound on the positive iteration index implies the desired `ε`-accuracy. -/
theorem proximal_gradient_strongly_convex_objective_gap_le_of_log_iteration_bound_of_stepsize_control
    (hstrong : StrongConvexOn (effective_domain f) (σ : ℝ) (fun y ↦ (f y).toReal))
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.SublinearRateStepsizeRule x L htraj α)
    (hL_bound : ∀ n, (L n : ℝ) ≤ α * (Lf : ℝ))
    (hxStar : xStar ∈ XStar)
    (ε : PosReal) (R : ℝ) (hR : ‖x 0 - xStar‖ ≤ R)
    (k : ℕ+)
    (hiter :
      α * κ * Real.log (1 / (ε : ℝ)) +
          α * κ * Real.log (α * (Lf : ℝ) * R ^ (2 : ℕ) / 2) ≤
        (k : ℝ)) :
    F (x k) - (FOpt : EReal) ≤ ((ε : ℝ) : EReal) := by
  let q : ℝ := 1 - 1 / (α * κ)
  let A : ℝ := α * (Lf : ℝ) * R ^ (2 : ℕ) / 2
  have hgap :=
    proximal_gradient_strongly_convex_objective_gap_le_at_pnat
      (hproblem := hproblem)
      hstrong
      htraj
      hrule
      hL_bound
      hxStar
      k
  have hα_pos : 0 < α :=
    hproblem.sublinearRateStepsizeRule_alpha_pos hrule
  have hLf_pos : 0 < (Lf : ℝ) :=
    hproblem.sublinearRateStepsizeRule_lf_pos hrule
  have hκ_pos : 0 < κ := by
    rw [condition_number_eq]
    exact div_pos hLf_pos σ.2
  have hακ_pos : 0 < α * κ := mul_pos hα_pos hκ_pos
  by_cases hinit_zero : ‖x 0 - xStar‖ ^ (2 : ℕ) = 0
  · have hzero_le_eps : ((0 : ℝ) : EReal) ≤ ((ε : ℝ) : EReal) := by
      exact EReal.coe_le_coe_iff.mpr (le_of_lt ε.2)
    have hgap_zero :
        F (x k) - (FOpt : EReal) ≤ ((0 : ℝ) : EReal) := by
      -- The geometric bound collapses to zero when the initial distance vanishes.
      simpa [q, hinit_zero] using hgap
    exact hgap_zero.trans hzero_le_eps
  · have hq_nonneg :
        0 ≤ q :=
      proximal_gradient_contraction_factor_nonneg_of_initial_distance_ne_zero
        (hproblem := hproblem)
        hstrong
        htraj
        hrule
        hL_bound
        hxStar
        hinit_zero
    by_cases hq_zero : q = 0
    · have hzero_le_eps : ((0 : ℝ) : EReal) ≤ ((ε : ℝ) : EReal) := by
        exact EReal.coe_le_coe_iff.mpr (le_of_lt ε.2)
      have hpow_zero : (1 - 1 / (α * κ)) ^ (k : ℕ) = 0 := by
        rw [← show q = 1 - 1 / (α * κ) by rfl, hq_zero]
        exact zero_pow (PNat.ne_zero k)
      have hgap_zero :
          F (x k) - (FOpt : EReal) ≤ ((0 : ℝ) : EReal) := by
        -- Positive indices force `q^k = 0` when the contraction factor itself vanishes.
        have hgap' := hgap
        rw [hpow_zero] at hgap'
        simpa using hgap'
      exact hgap_zero.trans hzero_le_eps
    · have hq_pos : 0 < q :=
        lt_of_le_of_ne hq_nonneg (Ne.symm hq_zero)
      have hk_real_nonneg : 0 ≤ (k : ℝ) := by
        exact_mod_cast (le_of_lt k.2)
      have hR_sq_le : ‖x 0 - xStar‖ ^ (2 : ℕ) ≤ R ^ (2 : ℕ) := by
        rw [pow_two, pow_two]
        nlinarith [norm_nonneg (x 0 - xStar), hR]
      have hinit_nonneg : 0 ≤ ‖x 0 - xStar‖ ^ (2 : ℕ) := by
        positivity
      have hinit_pos : 0 < ‖x 0 - xStar‖ ^ (2 : ℕ) :=
        lt_of_le_of_ne hinit_nonneg (Ne.symm hinit_zero)
      have hR_sq_pos : 0 < R ^ (2 : ℕ) :=
        lt_of_lt_of_le hinit_pos hR_sq_le
      have hA_pos : 0 < A := by
        dsimp [A]
        exact div_pos (mul_pos (mul_pos hα_pos hLf_pos) hR_sq_pos) (by positivity)
      have hlog_q :
          Real.log q ≤ -1 / (α * κ) := by
        have hraw : Real.log q ≤ q - 1 :=
          Real.log_le_sub_one_of_pos hq_pos
        have hq_sub : q - 1 = -1 / (α * κ) := by
          rw [show q = 1 - 1 / (α * κ) by rfl]
          ring
        exact hraw.trans_eq hq_sub
      have hiter_factor :
          (α * κ) * (Real.log (1 / (ε : ℝ)) + Real.log A) ≤ (k : ℝ) := by
        -- Package the two logarithmic terms into the single factor `α κ`.
        simpa [A, mul_add, mul_assoc, mul_left_comm, mul_comm] using hiter
      have hlogA_bound :
          Real.log A - (k : ℝ) / (α * κ) ≤ Real.log (ε : ℝ) := by
        have hiter_div :
            Real.log (1 / (ε : ℝ)) + Real.log A ≤ (k : ℝ) / (α * κ) := by
          exact (le_div_iff₀ hακ_pos).2 (by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hiter_factor)
        rw [one_div, Real.log_inv] at hiter_div
        nlinarith
      have hlogAq :
          Real.log (A * q ^ (k : ℕ)) ≤ Real.log (ε : ℝ) := by
        calc
          Real.log (A * q ^ (k : ℕ)) = Real.log A + Real.log (q ^ (k : ℕ)) := by
            rw [Real.log_mul hA_pos.ne' (pow_ne_zero _ hq_zero)]
          _ = Real.log A + (k : ℝ) * Real.log q := by
            rw [Real.log_pow]
          _ ≤ Real.log A + (k : ℝ) * (-1 / (α * κ)) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left
                (mul_le_mul_of_nonneg_left hlog_q hk_real_nonneg)
                (Real.log A)
          _ = Real.log A - (k : ℝ) / (α * κ) := by
            ring
          _ ≤ Real.log (ε : ℝ) := hlogA_bound
      have hAq_le_eps : A * q ^ (k : ℕ) ≤ (ε : ℝ) := by
        exact (Real.log_le_log_iff (mul_pos hA_pos (pow_pos hq_pos _)) ε.2).1 hlogAq
      have hcoeff_nonneg :
          0 ≤ ((α * (Lf : ℝ)) / 2) * q ^ (k : ℕ) := by
        exact
          mul_nonneg
            (div_nonneg (le_of_lt (mul_pos hα_pos hLf_pos)) (by positivity))
            (pow_nonneg hq_nonneg _)
      have hgap_R :
          F (x k) - (FOpt : EReal) ≤
            (((((α * (Lf : ℝ)) / 2) * q ^ (k : ℕ) * R ^ (2 : ℕ) : ℝ)) : EReal) := by
        have hmul :
            (((α * (Lf : ℝ)) / 2) * q ^ (k : ℕ)) * ‖x 0 - xStar‖ ^ (2 : ℕ) ≤
              (((α * (Lf : ℝ)) / 2) * q ^ (k : ℕ)) * R ^ (2 : ℕ) :=
          mul_le_mul_of_nonneg_left hR_sq_le hcoeff_nonneg
        exact le_trans hgap (by
          exact EReal.coe_le_coe_iff.mpr (by
            simpa [q, mul_assoc, mul_left_comm, mul_comm] using hmul))
      have hA_expand :
          A * q ^ (k : ℕ) =
            ((α * (Lf : ℝ)) / 2) * q ^ (k : ℕ) * R ^ (2 : ℕ) := by
        dsimp [A]
        ring
      have hAq_le_epsE :
          (((((α * (Lf : ℝ)) / 2) * q ^ (k : ℕ) * R ^ (2 : ℕ) : ℝ)) : EReal) ≤
            ((ε : ℝ) : EReal) := by
        have hAq_le_eps' :
            ((α * (Lf : ℝ)) / 2) * q ^ (k : ℕ) * R ^ (2 : ℕ) ≤ (ε : ℝ) := by
          simpa [hA_expand] using hAq_le_eps
        exact EReal.coe_le_coe_iff.mpr hAq_le_eps'
      exact hgap_R.trans hAq_le_epsE

-- Proof sketch: apply `proximal_gradient_strongly_convex_objective_gap_le` from Theorem 10.29 to
-- the index `k - 1`, use positivity of `k : ℕ+` to rewrite `k = (k - 1) + 1`, bound
-- `‖x 0 - xStar‖²` by `R²` via `hR`, and then use the logarithmic lower bound on `k` together with
-- `log (1 - t) ≤ -t` for `t = 1 / (α * κ(Lf, σ))` to dominate the geometric factor by `ε`.
/-- Theorem 10.30: in the strongly convex proximal-gradient setting of Theorem 10.29, if
the positive iteration index `k` satisfies the logarithmic iteration bound
`α κ log (1 / ε) + α κ log (α L_f R^2 / 2) ≤ k`, where `κ = L_f / σ` and `R` bounds
`‖x^0 - x*‖`, then the `k`-th iterate satisfies `F(x^k) - F_opt ≤ ε`. -/
theorem proximal_gradient_strongly_convex_objective_gap_le_of_log_iteration_bound
    (hstrong : StrongConvexOn (effective_domain f) (σ : ℝ) (fun y ↦ (f y).toReal))
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.SublinearRateStepsizeRule x L htraj α)
    (hL_bound : ∀ n, (L n : ℝ) ≤ α * (Lf : ℝ))
    (hxStar : xStar ∈ XStar)
    (ε : PosReal) (R : ℝ) (hR : ‖x 0 - xStar‖ ≤ R)
    (k : ℕ+)
    (hiter :
      α * κ * Real.log (1 / (ε : ℝ)) +
          α * κ * Real.log (α * (Lf : ℝ) * R ^ (2 : ℕ) / 2) ≤
        (k : ℝ)) :
    F (x k) - (FOpt : EReal) ≤ ((ε : ℝ) : EReal) := by
  -- The source setting includes the uniform stepsize bridge supplied by Theorem 10.29/Remark 10.19.
  exact
    proximal_gradient_strongly_convex_objective_gap_le_of_log_iteration_bound_of_stepsize_control
      (hproblem := hproblem)
      hstrong
      htraj
      hrule
      hL_bound
      hxStar
      ε
      R
      hR
      k
      hiter

end
