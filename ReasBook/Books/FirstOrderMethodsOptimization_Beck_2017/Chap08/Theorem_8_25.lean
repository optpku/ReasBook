/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Algorithm_8_3
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_7
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_12
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_8
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Lemma_8_24

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace (toDualMap)

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → EReal} {C XStar : Set E} {fOpt : ℝ}
variable (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
variable (g : ℕ → C → E) (t : ℕ → ℝ) (x0 : C)

local notation "x[" k "]" =>
  projected_subgradient_method C h_problem.feasible_nonempty h_problem.feasible_closed
    h_problem.feasible_convex g t x0 k
local notation "x̄" =>
  projected_subgradient_method_iterate C h_problem.feasible_nonempty h_problem.feasible_closed
    h_problem.feasible_convex g t x0
local notation "x̄[" k "]" => x̄ k

/- Theorem 8.25 is `source-facing`: it is the convergence criterion for the concrete projected
subgradient iterates under a general positive stepsize rule. The canonical owners already present
in the chapter are the recursive iterate sequence `projected_subgradient_method`, the running-best
objective owner `best_achieved_function_value`, the standing problem assumptions
`IsConstrainedConvexProblem`, and the subgradient bound package `SubgradientNormBoundOn`.
Accordingly, the theorem is stated directly in terms of those owners and the textbook's ratio
condition on the partial sums of `t_k` and `t_k^2`, without introducing a surrogate wrapper for
dynamic stepsize schedules. -/

-- Proof sketch: apply Lemma 8.24 to an arbitrary optimal point `xStar ∈ XStar`, then use the
-- uniform bound from `h_bound` and the prefix-minimality of `best_achieved_function_value` to
-- derive
-- `f_best^k - fOpt ≤ ‖x0 - xStar‖^2 / (2 ∑_{n ≤ k} t_n) +
--   h_bound.L_f^2 * (∑_{n ≤ k} t_n^2) / (2 ∑_{n ≤ k} t_n)`.
-- The hypothesis on the ratio of partial sums forces the second term to vanish, and positivity of
-- the stepsizes implies `∑_{n ≤ k} t_n → ∞`, so the first term also tends to `0`.
/-- Helper for Theorem 8.25: every positive-stepsize prefix sum `∑_{n=0}^k t n` is strictly
positive. -/
private lemma positiveStepsizePrefixSum_pos
    (h_stepsize_pos : ∀ n, 0 < t n) (k : ℕ) :
    0 < Finset.sum (Finset.range (k + 1)) (fun n ↦ t n) := by
  -- The first positive stepsize already appears in every prefix sum.
  have hmem : 0 ∈ Finset.range (k + 1) := by
    simp
  have hle :
      t 0 ≤ Finset.sum (Finset.range (k + 1)) (fun n ↦ t n) := by
    simpa using
      (Finset.single_le_sum (fun n _ ↦ le_of_lt (h_stepsize_pos n)) hmem)
  exact lt_of_lt_of_le (h_stepsize_pos 0) hle

/-- Helper for Theorem 8.25: the bounded-subgradient hypothesis controls the weighted prefix sum
of squared selected subgradient norms by `L_f^2 ∑_{n=0}^k t_n^2`. -/
private lemma weightedSubgradientNormSqSum_le
    (h_bound : SubgradientNormBoundOn f C)
    (h_subgrad :
      ∀ n, toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f x̄[n])
    (k : ℕ) :
    Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n (x[n])‖ ^ (2 : ℕ)) ≤
      h_bound.L_f ^ (2 : ℕ) *
        Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ (2 : ℕ)) := by
  -- Bound each summand separately using the Chapter 8 norm cap on selected subgradients.
  calc
    Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n (x[n])‖ ^ (2 : ℕ)) ≤
        Finset.sum (Finset.range (k + 1))
          (fun n ↦ (t n) ^ (2 : ℕ) * h_bound.L_f ^ (2 : ℕ)) := by
          refine Finset.sum_le_sum ?_
          intro n hn
          have hx_feasible : x̄[n] ∈ C := by
            simpa [projected_subgradient_method_iterate] using (x[n]).property
          have hnorm :
              ‖g n (x[n])‖ ≤ h_bound.L_f := by
            simpa using h_bound.norm_le hx_feasible (h_subgrad n)
          have hsq : ‖g n (x[n])‖ ^ (2 : ℕ) ≤ h_bound.L_f ^ (2 : ℕ) := by
            nlinarith [hnorm, norm_nonneg (g n (x[n])), le_of_lt h_bound.L_f_pos]
          exact mul_le_mul_of_nonneg_left hsq (sq_nonneg (t n))
    _ = h_bound.L_f ^ (2 : ℕ) *
        Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ (2 : ℕ)) := by
          calc
            Finset.sum (Finset.range (k + 1))
                (fun n ↦ (t n) ^ (2 : ℕ) * h_bound.L_f ^ (2 : ℕ)) =
                Finset.sum (Finset.range (k + 1))
                  (fun n ↦ h_bound.L_f ^ (2 : ℕ) * (t n) ^ (2 : ℕ)) := by
                    refine Finset.sum_congr rfl ?_
                    intro n hn
                    ring
            _ = h_bound.L_f ^ (2 : ℕ) *
                Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ (2 : ℕ)) := by
                    symm
                    exact
                      Finset.mul_sum (Finset.range (k + 1))
                        (fun n ↦ (t n) ^ (2 : ℕ)) (h_bound.L_f ^ (2 : ℕ))

/-- Helper for Theorem 8.25: Lemma 8.24 and the uniform subgradient bound give the textbook
finite-k estimate for the running-best objective gap. -/
private lemma bestValueGap_le_prefixRatioBound
    (h_bound : SubgradientNormBoundOn f C)
    (h_subgrad :
      ∀ n, toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f x̄[n])
    (h_stepsize_pos : ∀ n, 0 < t n)
    {xStar : E} (hxStar : xStar ∈ XStar) (k : ℕ) :
    best_achieved_function_value (fun y ↦ (f y).toReal) x̄ k - fOpt ≤
      ((1 / 2 : ℝ) * ‖(x0 : E) - xStar‖ ^ (2 : ℕ)) /
          Finset.sum (Finset.range (k + 1)) (fun n ↦ t n) +
        (h_bound.L_f ^ (2 : ℕ) / 2) *
          ((Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ (2 : ℕ))) /
            Finset.sum (Finset.range (k + 1)) (fun n ↦ t n)) := by
  let S : ℕ → ℝ := fun j ↦ Finset.sum (Finset.range (j + 1)) (fun n ↦ t n)
  let Q : ℕ → ℝ := fun j ↦ Finset.sum (Finset.range (j + 1)) (fun n ↦ (t n) ^ (2 : ℕ))
  let bestGap : ℕ → ℝ := fun j ↦ best_achieved_function_value (fun y ↦ (f y).toReal) x̄ j - fOpt
  have h_stepsize_nonneg : ∀ n, 0 ≤ t n := fun n ↦ le_of_lt (h_stepsize_pos n)
  have hS_pos : 0 < S k :=
    positiveStepsizePrefixSum_pos t h_stepsize_pos k
  have hS_best :
      Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * bestGap k) = S k * bestGap k := by
    symm
    dsimp [S]
    exact Finset.sum_mul (Finset.range (k + 1)) (fun n ↦ t n) (bestGap k)
  have hbest_sum_le :
      S k * bestGap k ≤
        Finset.sum (Finset.range (k + 1)) (fun n ↦ t n * ((f x̄[n]).toReal - fOpt)) := by
    -- Compare the running best with each term in the prefix and sum the resulting inequalities.
    rw [← hS_best]
    refine Finset.sum_le_sum ?_
    intro n hn
    have hbest_le :
        best_achieved_function_value (fun y ↦ (f y).toReal) x̄ k ≤ (f x̄[n]).toReal :=
      best_achieved_function_value_le_objective_value
        (fun y ↦ (f y).toReal) x̄ k n hn
    exact
      mul_le_mul_of_nonneg_left
        (sub_le_sub_right hbest_le fOpt)
        (h_stepsize_nonneg n)
  have hweighted :=
    projected_subgradient_method_weighted_objective_gap_sum_le
      (f := f) (C := C) (XStar := XStar) (fOpt := fOpt) (h_problem := h_problem)
      (g := g) (t := t) (x0 := x0) h_subgrad h_stepsize_nonneg hxStar k
  have hnormsum :=
    weightedSubgradientNormSqSum_le
      (h_problem := h_problem) (g := g) (t := t) (x0 := x0) h_bound h_subgrad k
  have hmain :
      S k * bestGap k ≤
        (1 / 2 : ℝ) * ‖(x0 : E) - xStar‖ ^ (2 : ℕ) +
          (1 / 2 : ℝ) * (h_bound.L_f ^ (2 : ℕ) * Q k) := by
    -- Lemma 8.24 supplies the weighted-gap bound, and the norm estimate replaces each
    -- `‖g_n‖²` by `L_f²`.
    have hrhs_bound :
        (1 / 2 : ℝ) *
            Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ (2 : ℕ) * ‖g n (x[n])‖ ^ (2 : ℕ)) ≤
          (1 / 2 : ℝ) * (h_bound.L_f ^ (2 : ℕ) * Q k) := by
      simpa [Q] using
        mul_le_mul_of_nonneg_left hnormsum (by norm_num : 0 ≤ (1 / 2 : ℝ))
    refine hbest_sum_le.trans ?_
    refine hweighted.trans ?_
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left hrhs_bound ((1 / 2 : ℝ) * ‖(x0 : E) - xStar‖ ^ (2 : ℕ))
  have hdiv :
      bestGap k ≤
        ((1 / 2 : ℝ) * ‖(x0 : E) - xStar‖ ^ (2 : ℕ) +
            (1 / 2 : ℝ) * (h_bound.L_f ^ (2 : ℕ) * Q k)) / S k := by
    -- Divide by the strictly positive prefix sum to isolate the best-gap term.
    rw [le_div_iff₀ hS_pos]
    simpa [S, Q, bestGap, mul_comm, mul_left_comm, mul_assoc] using hmain
  calc
    best_achieved_function_value (fun y ↦ (f y).toReal) x̄ k - fOpt = bestGap k := by
      rfl
    _ ≤
        ((1 / 2 : ℝ) * ‖(x0 : E) - xStar‖ ^ (2 : ℕ) +
            (1 / 2 : ℝ) * (h_bound.L_f ^ (2 : ℕ) * Q k)) / S k := hdiv
    _ =
        ((1 / 2 : ℝ) * ‖(x0 : E) - xStar‖ ^ (2 : ℕ)) / S k +
          (h_bound.L_f ^ (2 : ℕ) / 2) * (Q k / S k) := by
          field_simp [ne_of_gt hS_pos]
    _ =
        ((1 / 2 : ℝ) * ‖(x0 : E) - xStar‖ ^ (2 : ℕ)) /
            Finset.sum (Finset.range (k + 1)) (fun n ↦ t n) +
          (h_bound.L_f ^ (2 : ℕ) / 2) *
            ((Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ (2 : ℕ))) /
              Finset.sum (Finset.range (k + 1)) (fun n ↦ t n)) := by
          simp [S, Q]

/-- Helper for Theorem 8.25: if `∑_{n=0}^k t_n^2 / ∑_{n=0}^k t_n → 0` and all `t_n` are
positive, then the prefix sums `∑_{n=0}^k t_n` tend to `+∞`. -/
private lemma stepsizePrefixSum_tendsto_atTop_of_ratio_tendsto_zero
    (h_stepsize_pos : ∀ n, 0 < t n)
    (h_ratio :
      Filter.Tendsto
        (fun k ↦
          (Finset.sum (Finset.range (k + 1)) fun n ↦ (t n) ^ (2 : ℕ)) /
            Finset.sum (Finset.range (k + 1)) fun n ↦ t n)
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun k ↦ Finset.sum (Finset.range (k + 1)) fun n ↦ t n)
      Filter.atTop Filter.atTop := by
  let S : ℕ → ℝ := fun k ↦ Finset.sum (Finset.range (k + 1)) (fun n ↦ t n)
  let Q : ℕ → ℝ := fun k ↦ Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ (2 : ℕ))
  have hS_pos : ∀ k, 0 < S k := by
    intro k
    exact positiveStepsizePrefixSum_pos t h_stepsize_pos k
  have hS_mono : Monotone S := by
    -- Each next prefix sum adds the nonnegative summand `t (k + 1)`.
    refine monotone_nat_of_le_succ ?_
    intro k
    have hsucc : S (k + 1) = S k + t (k + 1) := by
      simp [S, Finset.sum_range_succ]
    calc
      S k ≤ S k + t (k + 1) := by
        exact le_add_of_nonneg_right (le_of_lt (h_stepsize_pos (k + 1)))
      _ = S (k + 1) := hsucc.symm
  refine Filter.tendsto_atTop.2 ?_
  intro b
  by_cases hb : b < S 0
  · exact
      (Filter.eventually_ge_atTop 0).mono fun n hn ↦
        le_trans (le_of_lt hb) (hS_mono hn)
  · have hS0_le_b : S 0 ≤ b := le_of_not_gt hb
    have hexists : ∃ N, b ≤ S N := by
      by_contra hbounded
      push Not at hbounded
      have hbound : ∀ k, S k ≤ b := by
        intro k
        exact le_of_lt (hbounded k)
      have hb_pos : 0 < b := lt_of_lt_of_le (hS_pos 0) hS0_le_b
      let c : ℝ := (t 0) ^ (2 : ℕ) / b
      have hc_pos : 0 < c := by
        dsimp [c]
        have ht_sq_pos : 0 < (t 0) ^ (2 : ℕ) := by
          simpa [pow_two] using sq_pos_of_pos (h_stepsize_pos 0)
        exact div_pos ht_sq_pos hb_pos
      have hratio_lower : ∀ k, c ≤ Q k / S k := by
        intro k
        have hQ_lower :
            (t 0) ^ (2 : ℕ) ≤ Q k := by
          have hmem : 0 ∈ Finset.range (k + 1) := by
            simp
          simpa [Q] using
            (Finset.single_le_sum (fun n _ ↦ sq_nonneg (t n)) hmem)
        have hQ_nonneg : 0 ≤ Q k := by
          simpa [Q] using Finset.sum_nonneg (fun n _ ↦ sq_nonneg (t n))
        calc
          c = (t 0) ^ (2 : ℕ) / b := by
            rfl
          _ ≤ Q k / b := by
            exact (div_le_div_iff_of_pos_right hb_pos).2 hQ_lower
          _ ≤ Q k / S k := by
            exact div_le_div_of_nonneg_left hQ_nonneg (hS_pos k) (hbound k)
      have hc_le_zero : c ≤ 0 := by
        have hratio' :
            Filter.Tendsto (fun k ↦ Q k / S k) Filter.atTop (nhds 0) := by
          simpa [S, Q] using h_ratio
        exact
          le_of_tendsto_of_tendsto tendsto_const_nhds hratio'
            (Filter.Eventually.of_forall hratio_lower)
      exact (not_le_of_gt hc_pos) hc_le_zero
    rcases hexists with ⟨N, hN⟩
    exact (Filter.eventually_ge_atTop N).mono fun n hn ↦ le_trans hN (hS_mono hn)

/-- Theorem 8.25: under Assumptions 8.7 and 8.12, if the projected subgradient method uses
positive stepsizes and the ratio
`(∑_{n=0}^k t_n^2) / (∑_{n=0}^k t_n)` tends to `0`, then the best objective
value achieved by the first `k + 1` iterates has objective gap converging to
`0`. -/
theorem projected_subgradient_method_best_value_gap_tendsto_zero_of_stepsize_ratio
    (h_bound : SubgradientNormBoundOn f C)
    (h_subgrad :
      ∀ n, toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f x̄[n])
    (h_stepsize_pos : ∀ n, 0 < t n)
    (h_ratio :
      Filter.Tendsto
        (fun k ↦
          (Finset.sum (Finset.range (k + 1)) fun n ↦ (t n) ^ (2 : ℕ)) /
            Finset.sum (Finset.range (k + 1)) fun n ↦ t n)
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun k ↦
        best_achieved_function_value (fun y ↦ (f y).toReal) x̄ k - fOpt)
      Filter.atTop (nhds 0) := by
  rcases h_problem.optimal_set_nonempty with ⟨xStar, hxStar⟩
  let S : ℕ → ℝ := fun k ↦ Finset.sum (Finset.range (k + 1)) (fun n ↦ t n)
  let Q : ℕ → ℝ := fun k ↦ Finset.sum (Finset.range (k + 1)) (fun n ↦ (t n) ^ (2 : ℕ))
  let bestGap : ℕ → ℝ :=
    fun k ↦ best_achieved_function_value (fun y ↦ (f y).toReal) x̄ k - fOpt
  have hS_atTop :
      Filter.Tendsto S Filter.atTop Filter.atTop :=
    stepsizePrefixSum_tendsto_atTop_of_ratio_tendsto_zero t h_stepsize_pos h_ratio
  have hbest_nonneg : ∀ k, 0 ≤ bestGap k := by
    intro k
    -- The running best remains above the optimal value because every iterate is feasible.
    have hbest_lower :
        fOpt ≤ best_achieved_function_value (fun y ↦ (f y).toReal) x̄ k := by
      unfold best_achieved_function_value
      apply Finset.le_min'
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨n, hn, rfl⟩
      have hx_image : f x̄[n] ∈ f '' C := by
        refine ⟨x̄[n], ?_, rfl⟩
        simpa [projected_subgradient_method_iterate] using (x[n]).property
      have hlower : (fOpt : EReal) ≤ f x̄[n] :=
        h_problem.optimal_value_isGLB.left hx_image
      have hx_dom : x̄[n] ∈ effective_domain f := by
        exact
          interior_subset
            (h_problem.feasible_subset_interior_effective_domain
              (by simpa [projected_subgradient_method_iterate] using (x[n]).property))
      have htop : f x̄[n] ≠ ⊤ := ne_of_lt hx_dom
      have hbot : f x̄[n] ≠ ⊥ := h_problem.ne_bot _
      have hreal :
          (fOpt : EReal) ≤ (((f x̄[n]).toReal : ℝ) : EReal) := by
        simpa [EReal.coe_toReal htop hbot] using hlower
      exact EReal.coe_le_coe_iff.mp hreal
    dsimp [bestGap]
    linarith
  have hfirst_tendsto :
      Filter.Tendsto
        (fun k ↦ ((1 / 2 : ℝ) * ‖(x0 : E) - xStar‖ ^ (2 : ℕ)) / S k)
        Filter.atTop (nhds 0) :=
    hS_atTop.const_div_atTop ((1 / 2 : ℝ) * ‖(x0 : E) - xStar‖ ^ (2 : ℕ))
  have hsecond_tendsto :
      Filter.Tendsto
        (fun k ↦ (h_bound.L_f ^ (2 : ℕ) / 2) * (Q k / S k))
        Filter.atTop (nhds 0) := by
    have hratio' : Filter.Tendsto (fun k ↦ Q k / S k) Filter.atTop (nhds 0) := by
      simpa [Q, S] using h_ratio
    simpa using hratio'.const_mul (h_bound.L_f ^ (2 : ℕ) / 2)
  have hupper_tendsto :
      Filter.Tendsto
        (fun k ↦
          ((1 / 2 : ℝ) * ‖(x0 : E) - xStar‖ ^ (2 : ℕ)) / S k +
            (h_bound.L_f ^ (2 : ℕ) / 2) * (Q k / S k))
        Filter.atTop (nhds 0) :=
    by simpa using hfirst_tendsto.add hsecond_tendsto
  refine squeeze_zero hbest_nonneg ?_ hupper_tendsto
  intro k
  simpa [bestGap, S, Q] using
    bestValueGap_le_prefixRatioBound
      (h_problem := h_problem) (g := g) (t := t) (x0 := x0)
      h_bound h_subgrad h_stepsize_pos hxStar k

/-- Theorem 8.25, source-facing convergence form: under Assumptions 8.7 and 8.12, if the
projected subgradient method uses positive stepsizes and the ratio
`(∑_{n=0}^k t_n^2) / (∑_{n=0}^k t_n)` tends to `0`, then the best objective
value achieved by the first `k + 1` iterates converges to the optimal value
`fOpt`. -/
theorem projected_subgradient_method_best_value_tendsto_of_stepsize_ratio
    (h_bound : SubgradientNormBoundOn f C)
    (h_subgrad :
      ∀ n, toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f x̄[n])
    (h_stepsize_pos : ∀ n, 0 < t n)
    (h_ratio :
      Filter.Tendsto
        (fun k ↦
          (Finset.sum (Finset.range (k + 1)) fun n ↦ (t n) ^ (2 : ℕ)) /
            Finset.sum (Finset.range (k + 1)) fun n ↦ t n)
        Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun k ↦ best_achieved_function_value (fun y ↦ (f y).toReal) x̄ k)
      Filter.atTop (nhds fOpt) := by
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (projected_subgradient_method_best_value_gap_tendsto_zero_of_stepsize_ratio
      h_problem g t x0 h_bound h_subgrad h_stepsize_pos h_ratio).const_add fOpt

end
