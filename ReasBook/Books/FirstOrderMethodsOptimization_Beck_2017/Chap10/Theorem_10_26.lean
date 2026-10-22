/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_8
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Corollary_10_18
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Remark_10_19
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_9
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_21

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [ProperSpace E]
variable {f g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
variable [hproblem : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf]
variable {x : ℕ → E} {L : ℕ → PosReal} {xStar : E} {α : ℝ} {β : PosReal}

set_option quotPrecheck false in
local notation "R[" htraj "; " d ", " k "]" =>
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  best_achieved_function_value
    (fun y ↦ ‖G[d, f, g] y‖) (proximal_gradient_trajectory_iterate htraj) k

local notation "F" => composite_model_objective f g

/-- Helper for Theorem 10.26: the squared running-best gradient-mapping norm on the prefix
`0, ..., k` is bounded by the sum of the squared norms on the positive iterates `1, ..., k`. -/
lemma bestGradientMappingSqMul_le_positivePrefixSum
    [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)]
    [Fact (is_convex_function g)]
    (htraj : is_proximal_gradient_trajectory f g x L)
    (d : PosReal) (k : ℕ) :
    (k : ℝ) * R[htraj; d, k] ^ (2 : ℕ) ≤
      Finset.sum (Finset.range k)
        (fun n ↦ ‖G[d, f, g] (proximal_gradient_trajectory_iterate htraj (n + 1))‖ ^ (2 : ℕ)) :=
by
  have hbest_nonneg : 0 ≤ R[htraj; d, k] := by
    -- The running minimum is attained by one prefix gradient-mapping norm, hence it is nonnegative.
    unfold best_achieved_function_value
    have hmem :=
      Finset.min'_mem
        ((Finset.range (k + 1)).image
          fun n ↦ ‖G[d, f, g] (proximal_gradient_trajectory_iterate htraj n)‖)
        (objective_value_prefix_nonempty
          (fun y ↦ ‖G[d, f, g] y‖)
          (proximal_gradient_trajectory_iterate htraj)
          k)
    rcases Finset.mem_image.mp hmem with ⟨n, _, hn⟩
    rw [← hn]
    exact norm_nonneg _
  have hterm :
      ∀ n ∈ Finset.range k,
        R[htraj; d, k] ^ (2 : ℕ) ≤
          ‖G[d, f, g] (proximal_gradient_trajectory_iterate htraj (n + 1))‖ ^ (2 : ℕ) := by
    intro n hn
    have hn_succ : n + 1 ∈ Finset.range (k + 1) := by
      simpa using hn
    have hle :=
      best_achieved_function_value_le_objective_value
        (fun y ↦ ‖G[d, f, g] y‖)
        (proximal_gradient_trajectory_iterate htraj)
        k
        (n + 1)
        hn_succ
    -- Squaring preserves the pointwise running-minimum bound because both sides are nonnegative.
    nlinarith
      [hbest_nonneg,
        norm_nonneg (G[d, f, g] (proximal_gradient_trajectory_iterate htraj (n + 1)))]
  -- Sum the pointwise lower bounds over the positive prefix `1, ..., k`.
  calc
    (k : ℝ) * R[htraj; d, k] ^ (2 : ℕ) =
        Finset.sum (Finset.range k) (fun _ ↦ R[htraj; d, k] ^ (2 : ℕ)) := by
      simp
    _ ≤ Finset.sum (Finset.range k) (fun n ↦
          ‖G[d, f, g] (proximal_gradient_trajectory_iterate htraj (n + 1))‖ ^ (2 : ℕ)) := by
      exact Finset.sum_le_sum hterm

/-- Helper for Theorem 10.26: Corollary 10.18 at the shifted positive iterate `x^(m+1)`
rewrites directly to a real decrease inequality between `x^(m+1)` and `x^(m+2)`. -/
lemma proxGradSufficientDecreaseToRealAtPositiveIterate
    [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)]
    [Fact (is_convex_function g)]
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.SourceSublinearRateStepsizeRule x L htraj α)
    (m : ℕ) :
    ((1 : ℝ) / (2 * (L (m + 1) : ℝ))) *
        ‖G[L (m + 1), f, g] (proximal_gradient_trajectory_iterate htraj (m + 1))‖ ^ (2 : ℕ) ≤
      (F (x (m + 1))).toReal - (F (x (m + 2))).toReal := by
  let xn := proximal_gradient_trajectory_iterate htraj (m + 1)
  have hbase_rule :
      hproblem.ConstantOrBacktrackingB2StepsizeRule x L htraj :=
    sourceSublinearRateRule_constantOrBacktrackingB2 htraj hrule
  have haccepts :
      proximal_gradient_backtracking_B2_accepts f g (L (m + 1)) xn := by
    -- The source-faithful owner still gives the accepted upper-model inequality at `x^(m+1)`.
    exact
      proximal_gradient_constant_or_backtracking_B2_stepsize_accepts
        hproblem.f_ne_bot
        hproblem.f_effective_domain_convex
        hproblem.g_effective_domain_subset_interior_f_effective_domain
        hproblem.f_toReal_smooth_on_interior_effective_domain
        htraj
        hbase_rule
        (m + 1)
  have hstepE :
      (((1 : ℝ) / (2 * (L (m + 1) : ℝ)) *
          ‖G[L (m + 1), f, g] (proximal_gradient_trajectory_iterate htraj (m + 1))‖ ^ (2 : ℕ) :
          ℝ) : EReal) ≤
        F (x (m + 1)) - F (x (m + 2)) := by
    -- Rewrite the accepted prox-gradient step from Corollary 10.18 onto the trajectory successor.
    simpa [xn, proximal_gradient_trajectory_succ_eq_operator htraj (m + 1)] using
      (prox_grad_sufficient_decrease_of_upper_model
        hproblem.f_ne_bot
        (L (m + 1))
        xn
        haccepts)
  have hxsucc :
      x (m + 1) ∈ effective_domain g :=
    @proximalGradientPositiveIterate_memEffectiveDomainG
      _ _ _ _ _ _ _ _ _ hproblem _ _ htraj m
  have hxsucc_succ :
      x (m + 2) ∈ effective_domain g :=
    @proximalGradientPositiveIterate_memEffectiveDomainG
      _ _ _ _ _ _ _ _ _ hproblem _ _ htraj (m + 1)
  have hxsucc_sum_toReal :
      (f (x (m + 1)) + g (x (m + 1))).toReal =
        (f (x (m + 1))).toReal + (g (x (m + 1))).toReal := by
    rw [← composite_model_objective_apply,
      @objectiveEqReal_of_memEffectiveDomainG
        _ _ _ _ _ _ _ _ _ hproblem _ hxsucc,
      EReal.toReal_coe]
  have hxsucc_succ_sum_toReal :
      (f (x (m + 2)) + g (x (m + 2))).toReal =
        (f (x (m + 2))).toReal + (g (x (m + 2))).toReal := by
    rw [← composite_model_objective_apply,
      @objectiveEqReal_of_memEffectiveDomainG
        _ _ _ _ _ _ _ _ _ hproblem _ hxsucc_succ,
      EReal.toReal_coe]
  -- Convert the finite `EReal` objective drop to the corresponding real-valued difference.
  rw [@objectiveEqReal_of_memEffectiveDomainG
      _ _ _ _ _ _ _ _ _ hproblem _ hxsucc,
    @objectiveEqReal_of_memEffectiveDomainG
      _ _ _ _ _ _ _ _ _ hproblem _ hxsucc_succ] at hstepE
  have hstep_real :
      (1 / (2 * (L (m + 1) : ℝ))) *
          ‖G[L (m + 1), f, g] (proximal_gradient_trajectory_iterate htraj (m + 1))‖ ^ (2 : ℕ) ≤
        ((f (x (m + 1))).toReal + (g (x (m + 1))).toReal) -
          ((f (x (m + 2))).toReal + (g (x (m + 2))).toReal) := by
    exact EReal.coe_le_coe_iff.mp (by simpa [EReal.coe_sub] using hstepE)
  simpa [hxsucc_sum_toReal, hxsucc_succ_sum_toReal] using hstep_real

/-- Helper for Theorem 10.26: the stepsize bounds `β L_f ≤ L_(m+1) ≤ α L_f` compare the fixed
residual norm at `α L_f` with the accepted residual norm at `L_(m+1)`. -/
lemma fixedResidualDecrease_of_stepsizeBounds
    [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)]
    [Fact (is_convex_function g)]
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.SourceSublinearRateStepsizeRule x L htraj α)
    (m : ℕ)
    (hLlower : (β : ℝ) * (Lf : ℝ) ≤ (L (m + 1) : ℝ)) :
    let hsub :=
      sourceSublinearRateRule_sublinearRateStepsizeRule htraj hrule
    let d := hproblem.sublinearRateResidualStepsize htraj α hsub
    ((β : ℝ) / (2 * α ^ (2 : ℕ) * (Lf : ℝ))) *
        ‖G[d, f, g] (proximal_gradient_trajectory_iterate htraj (m + 1))‖ ^ (2 : ℕ) ≤
      ((1 : ℝ) / (2 * (L (m + 1) : ℝ))) *
        ‖G[L (m + 1), f, g] (proximal_gradient_trajectory_iterate htraj (m + 1))‖ ^ (2 : ℕ) := by
  let hsub := sourceSublinearRateRule_sublinearRateStepsizeRule htraj hrule
  let d := hproblem.sublinearRateResidualStepsize htraj α hsub
  let xn := proximal_gradient_trajectory_iterate htraj (m + 1)
  have hα_pos : 0 < α := hproblem.sublinearRateStepsizeRule_alpha_pos hsub
  have hLf_pos : 0 < (Lf : ℝ) := hproblem.sublinearRateStepsizeRule_lf_pos hsub
  have hupper :
      (L (m + 1) : ℝ) ≤ (d : ℝ) := by
    simpa [d] using
      sourceSublinearRateRule_stepsizeBound
        htraj
        hrule
        (m + 1)
  have hratio :
      ‖G[d, f, g] xn‖ / (d : ℝ) ≤ ‖G[L (m + 1), f, g] xn‖ / (L (m + 1) : ℝ) :=
    (gradient_mapping_norm_div_stepsize_antitone f g xn) hupper
  have hratio_sq :
      (‖G[d, f, g] xn‖ / (d : ℝ)) ^ (2 : ℕ) ≤
        (‖G[L (m + 1), f, g] xn‖ / (L (m + 1) : ℝ)) ^ (2 : ℕ) := by
    -- The normalized residuals are nonnegative, so the antitone comparison can be squared.
    have hleft_nonneg : 0 ≤ ‖G[d, f, g] xn‖ / (d : ℝ) := by
      exact div_nonneg (norm_nonneg _) (le_of_lt (PosReal.coe_pos d))
    have hright_nonneg : 0 ≤ ‖G[L (m + 1), f, g] xn‖ / (L (m + 1) : ℝ) := by
      exact div_nonneg (norm_nonneg _) (le_of_lt (PosReal.coe_pos (L (m + 1))))
    have hneg : -(‖G[L (m + 1), f, g] xn‖ / (L (m + 1) : ℝ)) ≤ ‖G[d, f, g] xn‖ / (d : ℝ) := by
      nlinarith
    exact sq_le_sq' hneg hratio
  have hleft_eq :
      ((β : ℝ) / (2 * α ^ (2 : ℕ) * (Lf : ℝ))) * ‖G[d, f, g] xn‖ ^ (2 : ℕ) =
        (((β : ℝ) * (Lf : ℝ)) / 2) * (‖G[d, f, g] xn‖ / (d : ℝ)) ^ (2 : ℕ) := by
    have hd_eq : (d : ℝ) = α * (Lf : ℝ) := by
      simp [d]
    rw [hd_eq]
    field_simp [hα_pos.ne', hLf_pos.ne']
  have hright_eq :
      ((1 : ℝ) / (2 * (L (m + 1) : ℝ))) * ‖G[L (m + 1), f, g] xn‖ ^ (2 : ℕ) =
        (((L (m + 1) : ℝ)) / 2) * (‖G[L (m + 1), f, g] xn‖ / (L (m + 1) : ℝ)) ^ (2 : ℕ) := by
    field_simp [show ((L (m + 1) : ℝ) ≠ 0) by exact (PosReal.coe_pos (L (m + 1))).ne']
  have hscaled_ratio :
      (((β : ℝ) * (Lf : ℝ)) / 2) * (‖G[d, f, g] xn‖ / (d : ℝ)) ^ (2 : ℕ) ≤
        (((β : ℝ) * (Lf : ℝ)) / 2) *
          (‖G[L (m + 1), f, g] xn‖ / (L (m + 1) : ℝ)) ^ (2 : ℕ) := by
    have hcoeff_nonneg : 0 ≤ (((β : ℝ) * (Lf : ℝ)) / 2) := by
      exact div_nonneg (mul_nonneg (le_of_lt β.2) (le_of_lt hLf_pos)) (by norm_num)
    exact mul_le_mul_of_nonneg_left hratio_sq hcoeff_nonneg
  have hscaled_stepsize :
      (((β : ℝ) * (Lf : ℝ)) / 2) *
          (‖G[L (m + 1), f, g] xn‖ / (L (m + 1) : ℝ)) ^ (2 : ℕ) ≤
        (((L (m + 1) : ℝ)) / 2) *
          (‖G[L (m + 1), f, g] xn‖ / (L (m + 1) : ℝ)) ^ (2 : ℕ) := by
    have hcoeff_le : ((β : ℝ) * (Lf : ℝ)) / 2 ≤ ((L (m + 1) : ℝ)) / 2 := by
      nlinarith [hLlower]
    have hratio_term_nonneg :
        0 ≤ (‖G[L (m + 1), f, g] xn‖ / (L (m + 1) : ℝ)) ^ (2 : ℕ) := by
      positivity
    exact mul_le_mul_of_nonneg_right hcoeff_le hratio_term_nonneg
  -- Route correction: keep Theorem 10.9 entirely inside this scalar comparison lemma.
  calc
    ((β : ℝ) / (2 * α ^ (2 : ℕ) * (Lf : ℝ))) * ‖G[d, f, g] xn‖ ^ (2 : ℕ) =
        (((β : ℝ) * (Lf : ℝ)) / 2) * (‖G[d, f, g] xn‖ / (d : ℝ)) ^ (2 : ℕ) := hleft_eq
    _ ≤ (((β : ℝ) * (Lf : ℝ)) / 2) *
          (‖G[L (m + 1), f, g] xn‖ / (L (m + 1) : ℝ)) ^ (2 : ℕ) := hscaled_ratio
    _ ≤ (((L (m + 1) : ℝ)) / 2) *
          (‖G[L (m + 1), f, g] xn‖ / (L (m + 1) : ℝ)) ^ (2 : ℕ) := hscaled_stepsize
    _ = ((1 : ℝ) / (2 * (L (m + 1) : ℝ))) * ‖G[L (m + 1), f, g] xn‖ ^ (2 : ℕ) :=
      hright_eq.symm

/-- Helper for Theorem 10.26: every positive iterate satisfies the sufficient-decrease inequality
with the gradient-mapping norm evaluated at the fixed residual parameter `α L_f`. -/
lemma proximalGradientStepDecreaseAtResidualStepsize
    [IsProperExtendedRealFunction g]
    [Fact (LowerSemicontinuous g)]
    [Fact (is_convex_function g)]
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.SourceSublinearRateStepsizeRule x L htraj α)
    (m : ℕ)
    (hLlower : (β : ℝ) * (Lf : ℝ) ≤ (L (m + 1) : ℝ)) :
    let hsub :=
      sourceSublinearRateRule_sublinearRateStepsizeRule htraj hrule
    let d := hproblem.sublinearRateResidualStepsize htraj α hsub
    ((β : ℝ) / (2 * α ^ (2 : ℕ) * (Lf : ℝ))) *
        ‖G[d, f, g] (proximal_gradient_trajectory_iterate htraj (m + 1))‖ ^ (2 : ℕ) ≤
      (F (x (m + 1))).toReal - (F (x (m + 2))).toReal := by
  -- Route correction: the fixed-residual one-step estimate is now a short transitivity argument
  -- between the scalar comparison lemma and the real sufficient-decrease bridge.
  simpa using
    le_trans
      (fixedResidualDecrease_of_stepsizeBounds htraj hrule m hLlower)
      (proxGradSufficientDecreaseToRealAtPositiveIterate htraj hrule m)

/-- Helper for Theorem 10.26: summing the one-step decrease over the positive prefix
`1, ..., k` yields the squared running-best rate
`R[htraj; α L_f, k]^2 ≤ α^3 L_f^2 ‖x^0 - xStar‖^2 / (β k)`. -/
lemma bestGradientMappingSq_le_sublinearPrefixRate
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.SourceSublinearRateStepsizeRule x L htraj α)
    (hxStar : xStar ∈ XStar)
    (k : ℕ) (hk : 1 ≤ k)
    (hLlower : ∀ ⦃n : ℕ⦄, n ≤ k → (β : ℝ) * (Lf : ℝ) ≤ (L n : ℝ)) :
    let hsub :=
      sourceSublinearRateRule_sublinearRateStepsizeRule htraj hrule
    let d := hproblem.sublinearRateResidualStepsize htraj α hsub
    R[htraj; d, k] ^ (2 : ℕ) ≤
      α ^ (3 : ℕ) * (Lf : ℝ) ^ (2 : ℕ) * ‖x 0 - xStar‖ ^ (2 : ℕ) /
        ((β : ℝ) * (k : ℝ)) :=
by
  let hsub := sourceSublinearRateRule_sublinearRateStepsizeRule htraj hrule
  let d := hproblem.sublinearRateResidualStepsize htraj α hsub
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  have hα_pos : 0 < α := hproblem.sublinearRateStepsizeRule_alpha_pos hsub
  have hLf_pos : 0 < (Lf : ℝ) := hproblem.sublinearRateStepsizeRule_lf_pos hsub
  have hk_pos_nat : 0 < k := Nat.succ_le_iff.mp hk
  have hk_pos : 0 < (k : ℝ) := by
    exact_mod_cast hk_pos_nat
  have hcoeff_nonneg :
      0 ≤ (β : ℝ) / (2 * α ^ (2 : ℕ) * (Lf : ℝ)) := by
    have hden_pos : 0 < 2 * α ^ (2 : ℕ) * (Lf : ℝ) := by
      positivity
    exact div_nonneg (le_of_lt β.2) (le_of_lt hden_pos)
  have hbest :
      (k : ℝ) * R[htraj; d, k] ^ (2 : ℕ) ≤
        Finset.sum (Finset.range k) (fun n ↦
          ‖G[d, f, g] (proximal_gradient_trajectory_iterate htraj (n + 1))‖ ^ (2 : ℕ)) := by
    simpa [d] using
      (@bestGradientMappingSqMul_le_positivePrefixSum
        _ _ _ _ _ _ _ _ _ hproblem _ _ _ _ _ htraj d k)
  have hsum_steps :
      ((β : ℝ) / (2 * α ^ (2 : ℕ) * (Lf : ℝ))) *
          Finset.sum (Finset.range k)
            (fun n ↦ ‖G[d, f, g] (proximal_gradient_trajectory_iterate htraj (n + 1))‖ ^ (2 : ℕ)) ≤
        Finset.sum (Finset.range k)
          (fun n ↦ (F (x (n + 1))).toReal - (F (x (n + 2))).toReal) := by
    -- Sum the shifted one-step decrease inequality over the positive prefix `1, ..., k`.
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun n hn ↦ by
      simpa [d] using
        proximalGradientStepDecreaseAtResidualStepsize
          htraj
          hrule
          n
          (hLlower (Nat.succ_le_of_lt (Finset.mem_range.mp hn)))
  have hprefix_gap :
      ((β : ℝ) / (2 * α ^ (2 : ℕ) * (Lf : ℝ))) *
          ((k : ℝ) * R[htraj; d, k] ^ (2 : ℕ)) ≤
        (F (x 1)).toReal - (F (x (k + 1))).toReal := by
    obtain ⟨K, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk_pos_nat)
    calc
      ((β : ℝ) / (2 * α ^ (2 : ℕ) * (Lf : ℝ))) *
          (((K + 1 : ℕ) : ℝ) * R[htraj; d, K + 1] ^ (2 : ℕ)) ≤
          ((β : ℝ) / (2 * α ^ (2 : ℕ) * (Lf : ℝ))) *
            Finset.sum (Finset.range (K + 1)) (fun n ↦
              ‖G[d, f, g] (proximal_gradient_trajectory_iterate htraj (n + 1))‖ ^ (2 : ℕ)) := by
        exact mul_le_mul_of_nonneg_left hbest hcoeff_nonneg
      _ ≤ Finset.sum (Finset.range (K + 1))
            (fun n ↦ (F (x (n + 1))).toReal - (F (x (n + 2))).toReal) := hsum_steps
      _ = (F (x 1)).toReal - (F (x (K + 2))).toReal := by
        simpa [composite_model_objective_apply, Nat.add_assoc] using
          (@realPrefixTelescope _ _ _ _ _ _ _ _ _ hproblem
            (fun n ↦ (F (x (n + 1))).toReal)
            K)
  have hx1 :
      x 1 ∈ effective_domain g :=
    @proximalGradientPositiveIterate_memEffectiveDomainG
      _ _ _ _ _ _ _ _ _ hproblem _ _ htraj 0
  have hgap1E :
      F (x 1) - (FOpt : EReal) ≤
        (((α * (Lf : ℝ) * ‖x 0 - xStar‖ ^ (2 : ℕ) / (2 * (1 : ℝ)) : ℝ)) : EReal) := by
    -- Theorem 10.21 bounds the entrance gap at the first positive iterate.
    simpa using
      proximal_gradient_convex_objective_gap_le
        htraj
        hrule
        hxStar
        1
        (by norm_num)
  have hgap1_real :
      (F (x 1)).toReal - FOpt ≤ α * (Lf : ℝ) * ‖x 0 - xStar‖ ^ (2 : ℕ) / 2 := by
    rw [← @objectiveMinusFOpt_eq_coe_sub_toReal_of_memEffectiveDomainG
      _ _ _ _ _ _ _ _ _ hproblem _ hx1] at hgap1E
    exact EReal.coe_le_coe_iff.mp (by simpa using hgap1E)
  have hxterminal :
      x (k + 1) ∈ effective_domain g :=
    @proximalGradientPositiveIterate_memEffectiveDomainG
      _ _ _ _ _ _ _ _ _ hproblem _ _ htraj k
  have hterminal_nonneg : 0 ≤ (F (x (k + 1))).toReal - FOpt := by
    exact sub_nonneg.mpr
      (@toReal_ge_FOpt_of_memEffectiveDomainG
        _ _ _ _ _ _ _ _ _ hproblem _ hxterminal)
  have hprefix_initial :
      ((β : ℝ) / (2 * α ^ (2 : ℕ) * (Lf : ℝ))) *
          ((k : ℝ) * R[htraj; d, k] ^ (2 : ℕ)) ≤
        (F (x 1)).toReal - FOpt := by
    -- Drop the nonnegative terminal gap from the telescoped objective difference.
    nlinarith [hprefix_gap, hterminal_nonneg]
  have hscaled_prefix :
      (β : ℝ) * ((k : ℝ) * R[htraj; d, k] ^ (2 : ℕ)) ≤
        (2 * α ^ (2 : ℕ) * (Lf : ℝ)) * ((F (x 1)).toReal - FOpt) := by
    have hmul :=
      mul_le_mul_of_nonneg_left
        hprefix_initial
        (show 0 ≤ 2 * α ^ (2 : ℕ) * (Lf : ℝ) by positivity)
    have hcancel :
        (2 * α ^ (2 : ℕ) * (Lf : ℝ)) *
            (((β : ℝ) / (2 * α ^ (2 : ℕ) * (Lf : ℝ))) *
              ((k : ℝ) * R[htraj; d, k] ^ (2 : ℕ))) =
          (β : ℝ) * ((k : ℝ) * R[htraj; d, k] ^ (2 : ℕ)) := by
      field_simp [hα_pos.ne', hLf_pos.ne']
    rw [hcancel] at hmul
    exact hmul
  have hentrance_scaled :
      (2 * α ^ (2 : ℕ) * (Lf : ℝ)) * ((F (x 1)).toReal - FOpt) ≤
        α ^ (3 : ℕ) * (Lf : ℝ) ^ (2 : ℕ) * ‖x 0 - xStar‖ ^ (2 : ℕ) := by
    -- Clear the remaining factor `2 α^2 L_f` from the first-iterate objective-gap bound.
    have hmul :=
      mul_le_mul_of_nonneg_left
        hgap1_real
        (show 0 ≤ 2 * α ^ (2 : ℕ) * (Lf : ℝ) by positivity)
    have hrhs :
        (2 * α ^ (2 : ℕ) * (Lf : ℝ)) *
            (α * (Lf : ℝ) * ‖x 0 - xStar‖ ^ (2 : ℕ) / 2) =
          α ^ (3 : ℕ) * (Lf : ℝ) ^ (2 : ℕ) * ‖x 0 - xStar‖ ^ (2 : ℕ) := by
      ring
    rw [hrhs] at hmul
    exact hmul
  have hprefix_scaled :
      (β : ℝ) * ((k : ℝ) * R[htraj; d, k] ^ (2 : ℕ)) ≤
        α ^ (3 : ℕ) * (Lf : ℝ) ^ (2 : ℕ) * ‖x 0 - xStar‖ ^ (2 : ℕ) := by
    exact le_trans hscaled_prefix hentrance_scaled
  have hβk_pos : 0 < (β : ℝ) * (k : ℝ) := by
    exact mul_pos β.2 hk_pos
  -- Divide by the positive factor `β k` to reach the claimed squared bound.
  exact (le_div_iff₀ hβk_pos).2 (by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hprefix_scaled)

/- Theorem 10.26 is `source-facing` in the Chapter 10 proximal-gradient rate API.

Domain sampling in the surrounding chapter identifies:
- `hproblem.SourceSublinearRateStepsizeRule` from Theorem 10.21 as the source-facing owner of
  the admissible constant/B2 stepsize regime together with the upper-rate factor `α`;
- `best_achieved_function_value` from Definition 8.8 as the canonical owner of the running
  minimum of the gradient-mapping norm along a trajectory prefix;
- `hproblem.sublinearRateResidualStepsize` from Remark 10.19 as the canonical owner of the
  residual parameter `α L_f` appearing in the theorem conclusion.

Triage for this file:
- `source-facing`: the final theorem, whose mathematical content is the textbook sublinear
  gradient-mapping estimate with auxiliary constants `α` and `β`;
- `core/canonical`:
  `hproblem.SourceSublinearRateStepsizeRule` and
  `best_achieved_function_value`;
- `bridge/view`: the theorem-specific lower bound `β L_f ≤ L_n` on the relevant prefix, together
  with `hproblem.sublinearRateResidualStepsize`.

The theorem surface should therefore reuse the existing Chapter 10 source-facing stepsize owner
and keep the lower factor `β` only as the separate bridge hypothesis actually used by the proof. -/

/-- Theorem 10.26: under Assumption 10.1, if `f` is convex and `x^k` is generated by the
proximal gradient method with the source-faithful constant/B2 stepsize regime from Theorem 10.21
with upper-rate factor `α`, and if the theorem-specific lower factor `β` satisfies
`β L_f ≤ L_n` on the prefix `0 ≤ n ≤ k`, then for every minimizer `xStar ∈ X^*` the best
gradient-mapping norm
up to iteration `k` at the canonical parameter `α L_f` satisfies the displayed source bound
`min_{0 ≤ n ≤ k} ‖G_(α L_f)(x^n)‖ ≤
  sqrt (α^3 L_f^2 ‖x^0 - xStar‖^2 / (β k))`,
equivalently an `O(1 / sqrt k)` rate, for `k ≥ 1`. -/
theorem proximal_gradient_best_gradient_mapping_norm_le_sublinear_rate
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hrule : hproblem.SourceSublinearRateStepsizeRule x L htraj α)
    (hxStar : xStar ∈ XStar) (k : ℕ) (hk : 1 ≤ k)
    (hLlower : ∀ ⦃n : ℕ⦄, n ≤ k → (β : ℝ) * (Lf : ℝ) ≤ (L n : ℝ)) :
    R[htraj;
      hproblem.sublinearRateResidualStepsize htraj α
        (sourceSublinearRateRule_sublinearRateStepsizeRule htraj hrule),
      k] ≤
      Real.sqrt
        (α ^ (3 : ℕ) * (Lf : ℝ) ^ (2 : ℕ) * ‖x 0 - xStar‖ ^ (2 : ℕ) /
          ((β : ℝ) * (k : ℝ))) := by
  let hsub := sourceSublinearRateRule_sublinearRateStepsizeRule htraj hrule
  let d := hproblem.sublinearRateResidualStepsize htraj α hsub
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  have hsq :
      R[htraj; d, k] ^ (2 : ℕ) ≤
        α ^ (3 : ℕ) * (Lf : ℝ) ^ (2 : ℕ) * ‖x 0 - xStar‖ ^ (2 : ℕ) /
          ((β : ℝ) * (k : ℝ)) := by
    simpa [hsub, d] using
      bestGradientMappingSq_le_sublinearPrefixRate htraj hrule hxStar k hk hLlower
  have hbest_nonneg : 0 ≤ R[htraj; d, k] := by
    change
      0 ≤ best_achieved_function_value
        (fun y ↦ ‖G[d, f, g] y‖) (proximal_gradient_trajectory_iterate htraj) k
    unfold best_achieved_function_value
    have hmem :=
      Finset.min'_mem
        ((Finset.range (k + 1)).image
          fun n ↦ ‖G[d, f, g] (proximal_gradient_trajectory_iterate htraj n)‖)
        (objective_value_prefix_nonempty
          (fun y ↦ ‖G[d, f, g] y‖)
          (proximal_gradient_trajectory_iterate htraj)
          k)
    rcases Finset.mem_image.mp hmem with ⟨n, _, hn⟩
    rw [← hn]
    exact norm_nonneg _
  have hα_pos : 0 < α := hproblem.sublinearRateStepsizeRule_alpha_pos hsub
  have hLf_pos : 0 < (Lf : ℝ) := hproblem.sublinearRateStepsizeRule_lf_pos hsub
  have hk_pos : 0 < (k : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mp hk
  have hbound_nonneg :
      0 ≤
        α ^ (3 : ℕ) * (Lf : ℝ) ^ (2 : ℕ) * ‖x 0 - xStar‖ ^ (2 : ℕ) /
          ((β : ℝ) * (k : ℝ)) := by
    have hnum_nonneg :
        0 ≤ α ^ (3 : ℕ) * (Lf : ℝ) ^ (2 : ℕ) * ‖x 0 - xStar‖ ^ (2 : ℕ) := by
      exact
        mul_nonneg
          (mul_nonneg
            (pow_nonneg (le_of_lt hα_pos) _)
            (pow_two_nonneg _))
          (pow_two_nonneg _)
    have hden_pos : 0 < (β : ℝ) * (k : ℝ) := by
      exact mul_pos β.2 hk_pos
    exact div_nonneg hnum_nonneg (le_of_lt hden_pos)
  exact (Real.le_sqrt hbest_nonneg hbound_nonneg).2 hsq

end
