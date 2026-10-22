/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_8
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_61
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Lemma_10_66

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped DualNorm

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- `prompt_add/` is absent in this workspace, so the relevant local guidance comes from the
nearby Chapter 5 and Chapter 10 owner files. Theorem 10.67 is `source-facing` in the
non-Euclidean gradient-method API.

Domain sampling against the local project identifies the canonical owners already available:
- `non_euclidean_gradient_method` and
  `non_euclidean_gradient_method_is_admissible` from Algorithm 10.61 for the generated
  trajectory and the chosen primal counterparts;
- `best_achieved_function_value` from Definition 8.8 for the generic running minimum over a
  prefix of iterates;
- `ProximalGradientConstantStepsizeParameter`,
  `uses_non_euclidean_backtracking_B4_rule`, and
  `uses_non_euclidean_exact_line_search_stepsize_rule` from the nearby Chapter 10 files for the
  three admissible stepsize mechanisms;
- `uses_non_euclidean_gradient_stepsize_rule` and
  `non_euclidean_gradient_sufficient_decrease_by_stepsize_rule` from Lemma 10.66 for the
  chapter's source-facing admissible stepsize owner and its one-step sufficient-decrease bridge;
- the Chapter 10 dual-norm surface `‖fderiv ℝ f x‖_*` for the source quantity `‖f'(x^k)‖_*`;
- `MapClusterPt` for sequential limit points.

The theorem therefore stays directly on the existing trajectory owner and reuses the generic
running-minimum owner `best_achieved_function_value` for the prefix dual norms, rather than
introducing a second local prefix-minimum API or a packaged stepsize owner. -/

section SufficientDecreaseRule

variable {f : E → ℝ} {Lf : NNReal} {x : ℕ → E} {L : ℕ → PosReal} {xDagger : ℕ → E} {M : ℝ}

namespace uses_non_euclidean_gradient_stepsize_rule

-- Proof sketch: split `hstepsize` into the constant-step, B4-backtracking, and exact-line-search
-- branches, and in each branch read off the corresponding positive formula for `M`.
/-- The sufficient-decrease parameter `M` recorded by the admissible non-Euclidean stepsize-rule
owner is strictly positive. -/
theorem parameter_pos
    (hstepsize : uses_non_euclidean_gradient_stepsize_rule f Lf x L xDagger M) :
    0 < M := by
  -- Split the admissible stepsize owner into its three textbook branches.
  rcases hstepsize with hconst | hrest
  · rcases hconst with ⟨barL, _, rfl⟩
    -- In the constant branch, positivity comes from `barL > L_f / 2` and `barL^2 > 0`.
    have hnum : 0 < (barL : ℝ) - (Lf : ℝ) / 2 := by
      exact sub_pos.mpr barL.lower_bound
    have hden : 0 < (barL : ℝ) ^ (2 : ℕ) := by
      simpa [pow_two] using sq_pos_of_pos (PosReal.coe_pos (barL : PosReal))
    exact div_pos hnum hden
  · rcases hrest with hB4 | hexact
    · rcases hB4 with ⟨s, γ, η, _, rfl⟩
      -- In the backtracking branch, both the numerator `γ` and the `max` denominator are
      -- strictly positive.
      have hnum : 0 < (γ : ℝ) := γ.1.2
      have hden :
          0 <
            max (s : ℝ)
              (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ)))) := by
        exact lt_of_lt_of_le s.2 (le_max_left (s : ℝ)
          (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ)))))
      exact div_pos hnum hden
    · rcases hexact with ⟨hLf, _, rfl⟩
      -- In the exact-line-search branch, the denominator is `2 L_f > 0`.
      have hden : 0 < 2 * (Lf : ℝ) := by
        positivity
      exact one_div_pos.mpr hden

end uses_non_euclidean_gradient_stepsize_rule

end SufficientDecreaseRule

section GeneratedTrajectory

variable {f : E → ℝ} {Lf : NNReal}
variable {counterpart : ℕ → E → E} {L : ℕ → PosReal} {x0 : E} {M : ℝ}

local notation "x" => non_euclidean_gradient_method f counterpart L x0
local notation "xDagger" => non_euclidean_gradient_method_counterpart_sequence f counterpart L x0

variable (hf : is_l_smooth_on f Set.univ Lf)
variable (hadm : non_euclidean_gradient_method_is_admissible f counterpart L x0)
variable (hstepsize : uses_non_euclidean_gradient_stepsize_rule f Lf x L xDagger M)

/-- Helper for Theorem 10.67: every generated non-Euclidean gradient step satisfies the
one-step sufficient-decrease estimate from Lemma 10.66. -/
lemma non_euclidean_gradient_step_decrease_ge_dual_norm_sq
    (hf : is_l_smooth_on f Set.univ Lf)
    (hadm : non_euclidean_gradient_method_is_admissible f counterpart L x0)
    (hstepsize : uses_non_euclidean_gradient_stepsize_rule f Lf x L xDagger M)
    (k : ℕ) :
    f (x k) - f (x (k + 1)) ≥
      M * ‖fderiv ℝ f (x k)‖_* ^ (2 : ℕ) := by
  -- Specialize Lemma 10.66 to the generated trajectory and its admissible counterpart sequence.
  simpa using
    non_euclidean_gradient_sufficient_decrease_by_stepsize_rule
      hf x L xDagger
      (fun n ↦ by
        -- The recursive update is exactly Algorithm 10.61 on the generated trajectory.
        simpa using
          (non_euclidean_gradient_method_succ n))
      (fun n ↦ by
        -- Admissibility places the chosen counterpart in the primal-counterpart set.
        simpa using
          (non_euclidean_gradient_method_counterpart_sequence_mem_primalCounterparts hadm n))
      hstepsize k

/-- Helper for Theorem 10.67: if the Fréchet derivative vanishes at iterate `k`, then the next
iterate coincides with the current one. -/
lemma non_euclidean_gradient_iterate_succ_eq_self_of_fderiv_eq_zero
    (k : ℕ)
    (hk : fderiv ℝ f (x k) = 0) :
    x (k + 1) = x k := by
  -- The update factor is zero when the derivative norm vanishes.
  rw [non_euclidean_gradient_method_succ]
  simp [hk]

/-- Helper for Theorem 10.67: the squared running-best dual norm on the prefix `0, …, k`
controls the finite sum of the squared dual norms on that same prefix. -/
lemma best_achieved_dual_norm_sq_mul_le_prefix_sum_sq
    (k : ℕ) :
    (k + 1 : ℝ) *
        (best_achieved_function_value (fun y : E ↦ ‖fderiv ℝ f y‖_*) x k) ^ (2 : ℕ) ≤
      Finset.sum (Finset.range (k + 1)) (fun n ↦ ‖fderiv ℝ f (x n)‖_* ^ (2 : ℕ)) := by
  have hbest_nonneg :
      0 ≤ best_achieved_function_value (fun y : E ↦ ‖fderiv ℝ f y‖_*) x k := by
    -- The running minimum is itself one of the attained dual norms, hence nonnegative.
    unfold best_achieved_function_value
    have hmem :=
      Finset.min'_mem
        ((Finset.range (k + 1)).image fun n ↦ ‖fderiv ℝ f (x n)‖_*)
        (objective_value_prefix_nonempty (fun y : E ↦ ‖fderiv ℝ f y‖_*) x k)
    rcases Finset.mem_image.mp hmem with ⟨n, _, hn⟩
    rw [← hn]
    exact norm_nonneg _
  have hterm :
      ∀ n ∈ Finset.range (k + 1),
        (best_achieved_function_value (fun y : E ↦ ‖fderiv ℝ f y‖_*) x k) ^ (2 : ℕ) ≤
          ‖fderiv ℝ f (x n)‖_* ^ (2 : ℕ) := by
    intro n hn
    -- Each prefix value dominates the running minimum, so the same is true after squaring.
    have hle :=
      best_achieved_function_value_le_objective_value
        (fun y : E ↦ ‖fderiv ℝ f y‖_*) x k n hn
    nlinarith [hbest_nonneg, norm_nonneg (fderiv ℝ f (x n)), hle]
  -- Summing the pointwise lower bound over the whole prefix gives the desired estimate.
  calc
    (k + 1 : ℝ) *
        (best_achieved_function_value (fun y : E ↦ ‖fderiv ℝ f y‖_*) x k) ^ (2 : ℕ) =
      Finset.sum (Finset.range (k + 1))
        (fun _ ↦ (best_achieved_function_value (fun y : E ↦ ‖fderiv ℝ f y‖_*) x k) ^ (2 : ℕ)) := by
      simp
    _ ≤ Finset.sum (Finset.range (k + 1)) (fun n ↦ ‖fderiv ℝ f (x n)‖_* ^ (2 : ℕ)) := by
      exact Finset.sum_le_sum hterm

/-- Helper for Theorem 10.67: summing the one-step objective drops over the prefix
`0, …, k` telescopes to the gap between the initial and terminal objective values. -/
lemma non_euclidean_gradient_objective_telescope
    (k : ℕ) :
    Finset.sum (Finset.range (k + 1)) (fun n ↦ f (x n) - f (x (n + 1))) =
      f x0 - f (x (k + 1)) := by
  -- This is the exact source telescoping identity for the objective decreases.
  have htel := Finset.sum_range_sub (fun n ↦ f (x n)) (k + 1)
  calc
    Finset.sum (Finset.range (k + 1)) (fun n ↦ f (x n) - f (x (n + 1))) =
        Finset.sum (Finset.range (k + 1)) (fun n ↦ -(f (x (n + 1)) - f (x n))) := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      ring
    _ = -Finset.sum (Finset.range (k + 1)) (fun n ↦ f (x (n + 1)) - f (x n)) := by
      rw [Finset.sum_neg_distrib]
    _ = -(f (x (k + 1)) - f (x 0)) := by
      rw [htel]
    _ = f x0 - f (x (k + 1)) := by
      have hx0 : x 0 = x0 := by
        simp
      rw [hx0]
      ring

/-- Helper for Theorem 10.67: summing the sufficient-decrease inequality over the prefix
`0, …, k` bounds the total squared dual norm by the initial objective gap to any lower bound
`fOpt`. -/
lemma non_euclidean_gradient_prefix_sq_norm_sum_le_objective_gap
    (hf : is_l_smooth_on f Set.univ Lf)
    (hadm : non_euclidean_gradient_method_is_admissible f counterpart L x0)
    (hstepsize : uses_non_euclidean_gradient_stepsize_rule f Lf x L xDagger M)
    {fOpt : ℝ}
    (hfOpt : IsGLB (Set.range f) fOpt)
    (k : ℕ) :
    M * Finset.sum (Finset.range (k + 1)) (fun n ↦ ‖fderiv ℝ f (x n)‖_* ^ (2 : ℕ)) ≤
      f x0 - fOpt := by
  have hsum :
      Finset.sum (Finset.range (k + 1))
          (fun n ↦ M * ‖fderiv ℝ f (x n)‖_* ^ (2 : ℕ)) ≤
        Finset.sum (Finset.range (k + 1))
          (fun n ↦ f (x n) - f (x (n + 1))) := by
    -- Summing the source one-step sufficient-decrease estimate gives the prefix control.
    exact Finset.sum_le_sum fun n _ ↦
      non_euclidean_gradient_step_decrease_ge_dual_norm_sq hf hadm hstepsize n
  have hsum' :
      M * Finset.sum (Finset.range (k + 1))
          (fun n ↦ ‖fderiv ℝ f (x n)‖_* ^ (2 : ℕ)) ≤
        Finset.sum (Finset.range (k + 1))
          (fun n ↦ f (x n) - f (x (n + 1))) := by
    simpa [Finset.mul_sum] using hsum
  rw [non_euclidean_gradient_objective_telescope k] at hsum'
  have hfOpt_le_terminal : fOpt ≤ f (x (k + 1)) := by
    exact hfOpt.1 ⟨x (k + 1), rfl⟩
  -- Replacing the terminal objective value by the global lower bound matches the textbook gap.
  linarith

/-- Helper for Theorem 10.67: the summed sufficient-decrease estimate and the running-minimum
comparison yield the squared rate inequality before taking square roots. -/
lemma non_euclidean_gradient_best_dual_norm_sq_mul_le_initial_gap
    (hf : is_l_smooth_on f Set.univ Lf)
    (hadm : non_euclidean_gradient_method_is_admissible f counterpart L x0)
    (hstepsize : uses_non_euclidean_gradient_stepsize_rule f Lf x L xDagger M)
    {fOpt : ℝ}
    (hfOpt : IsGLB (Set.range f) fOpt)
    (k : ℕ) :
    M * ((k + 1 : ℝ) *
        (best_achieved_function_value (fun y : E ↦ ‖fderiv ℝ f y‖_*) x k) ^ (2 : ℕ)) ≤
      f x0 - fOpt := by
  have hM_nonneg : 0 ≤ M := by
    exact le_of_lt (uses_non_euclidean_gradient_stepsize_rule.parameter_pos hstepsize)
  have hbest :
      (k + 1 : ℝ) *
          (best_achieved_function_value (fun y : E ↦ ‖fderiv ℝ f y‖_*) x k) ^ (2 : ℕ) ≤
        Finset.sum (Finset.range (k + 1)) (fun n ↦ ‖fderiv ℝ f (x n)‖_* ^ (2 : ℕ)) := by
    simpa using (best_achieved_dual_norm_sq_mul_le_prefix_sum_sq k)
  have hprefix :=
    non_euclidean_gradient_prefix_sq_norm_sum_le_objective_gap hf hadm hstepsize hfOpt k
  -- Multiplying the running-minimum comparison by the positive coefficient `M` matches the
  -- summed decrease inequality.
  exact le_trans (mul_le_mul_of_nonneg_left hbest hM_nonneg) hprefix

/-- Helper for Theorem 10.67: clause (c) follows the source route by proving the squared estimate
first and then clearing the square roots. -/
lemma non_euclidean_gradient_best_dual_norm_up_to_le_rate_core
    (hf : is_l_smooth_on f Set.univ Lf)
    (hadm : non_euclidean_gradient_method_is_admissible f counterpart L x0)
    (hstepsize : uses_non_euclidean_gradient_stepsize_rule f Lf x L xDagger M)
    {fOpt : ℝ}
    (hfOpt : IsGLB (Set.range f) fOpt)
    (k : ℕ) :
    best_achieved_function_value (fun y : E ↦ ‖fderiv ℝ f y‖_*) x k ≤
      Real.sqrt (f x0 - fOpt) / Real.sqrt (M * (k + 1 : ℝ)) := by
  set best : ℝ := best_achieved_function_value (fun y : E ↦ ‖fderiv ℝ f y‖_*) x k with hbest_def
  have hsq_gap :
      M * ((k + 1 : ℝ) * best ^ (2 : ℕ)) ≤ f x0 - fOpt := by
    simpa [hbest_def] using
      non_euclidean_gradient_best_dual_norm_sq_mul_le_initial_gap
        hf hadm hstepsize hfOpt k
  have hbest_nonneg : 0 ≤ best := by
    rw [hbest_def]
    -- The running minimum is attained by one prefix dual norm and is therefore nonnegative.
    unfold best_achieved_function_value
    have hmem :=
      Finset.min'_mem
        ((Finset.range (k + 1)).image fun n ↦ ‖fderiv ℝ f (x n)‖_*)
        (objective_value_prefix_nonempty (fun y : E ↦ ‖fderiv ℝ f y‖_*) x k)
    rcases Finset.mem_image.mp hmem with ⟨n, _, hn⟩
    rw [← hn]
    exact norm_nonneg _
  have hgap_nonneg : 0 ≤ f x0 - fOpt := by
    exact sub_nonneg.mpr (hfOpt.1 ⟨x0, rfl⟩)
  have hden_pos : 0 < M * (k + 1 : ℝ) := by
    exact mul_pos
      (uses_non_euclidean_gradient_stepsize_rule.parameter_pos hstepsize)
      (by positivity)
  -- Route correction: isolate the explicit-hyp squared inequality first, then take square roots
  -- in one short normalization step instead of mixing `include` generalization with telescoping.
  rw [le_div_iff₀ (Real.sqrt_pos.2 hden_pos)]
  have hsqrt_den_sq :
      Real.sqrt (M * (k + 1 : ℝ)) ^ (2 : ℕ) = M * (k + 1 : ℝ) := by
    simpa [pow_two] using Real.sq_sqrt (le_of_lt hden_pos)
  have hsqrt_gap_sq :
      Real.sqrt (f x0 - fOpt) ^ (2 : ℕ) = f x0 - fOpt := by
    simpa [pow_two] using Real.sq_sqrt hgap_nonneg
  have hsq :
      (best * Real.sqrt (M * (k + 1 : ℝ))) ^ (2 : ℕ) ≤
        Real.sqrt (f x0 - fOpt) ^ (2 : ℕ) := by
    -- Squaring both sides reduces the rate estimate to the already established squared gap bound.
    nlinarith [hsq_gap, hsqrt_den_sq, hsqrt_gap_sq]
  have hleft_nonneg : 0 ≤ best * Real.sqrt (M * (k + 1 : ℝ)) := by
    exact mul_nonneg hbest_nonneg (Real.sqrt_nonneg _)
  have hright_nonneg : 0 ≤ Real.sqrt (f x0 - fOpt) := by
    exact Real.sqrt_nonneg _
  -- Nonnegativity lets the squared comparison recover the unsquared rate inequality.
  nlinarith [hsq, hleft_nonneg, hright_nonneg]

/-- Helper for Theorem 10.67: if the objective values are antitone and bounded below, then the
successive objective drops converge to `0`. -/
lemma non_euclidean_gradient_objective_step_tendsto_zero_of_bddBelow
    (hf : is_l_smooth_on f Set.univ Lf)
    (hadm : non_euclidean_gradient_method_is_admissible f counterpart L x0)
    (hstepsize : uses_non_euclidean_gradient_stepsize_rule f Lf x L xDagger M)
    (hbelow : BddBelow (Set.range fun k ↦ f (x k))) :
    Filter.Tendsto (fun k ↦ f (x k) - f (x (k + 1))) Filter.atTop (nhds 0) := by
  have hMpos :
      0 < M :=
    uses_non_euclidean_gradient_stepsize_rule.parameter_pos hstepsize
  have hanti : Antitone (fun k ↦ f (x k)) := by
    refine antitone_nat_of_succ_le ?_
    intro k
    have hdecrease :
        f (x k) - f (x (k + 1)) ≥
          M * ‖fderiv ℝ f (x k)‖_* ^ (2 : ℕ) :=
      non_euclidean_gradient_step_decrease_ge_dual_norm_sq hf hadm hstepsize k
    have hterm_nonneg :
        0 ≤ M * ‖fderiv ℝ f (x k)‖_* ^ (2 : ℕ) := by
      exact mul_nonneg (le_of_lt hMpos) (sq_nonneg ‖fderiv ℝ f (x k)‖_*)
    exact sub_nonneg.mp (le_trans hterm_nonneg hdecrease)
  let ℓ : ℝ := ⨅ k, f (x k)
  -- The bounded antitone objective sequence converges to its infimum.
  have hobj :
      Filter.Tendsto (fun k ↦ f (x k)) Filter.atTop (nhds ℓ) :=
    tendsto_atTop_ciInf hanti hbelow
  have hobj_shift :
      Filter.Tendsto (fun k ↦ f (x (k + 1))) Filter.atTop (nhds ℓ) := by
    have hshift :
        Filter.Tendsto (fun k : ℕ ↦ k + 1) Filter.atTop Filter.atTop :=
      (show StrictMono (fun k : ℕ ↦ k + 1) from
        fun a b hab ↦ Nat.add_lt_add_right hab 1).tendsto_atTop
    simpa [ℓ] using hobj.comp hshift
  -- Subtracting the shifted copy leaves a sequence converging to `ℓ - ℓ = 0`.
  simpa [ℓ] using hobj.sub hobj_shift

/-- Helper for Theorem 10.67: a cluster point produces a lower bound for the full objective
sequence. -/
lemma non_euclidean_gradient_objective_bddBelow_of_cluster_point
    (hf : is_l_smooth_on f Set.univ Lf)
    (hadm : non_euclidean_gradient_method_is_admissible f counterpart L x0)
    (hstepsize : uses_non_euclidean_gradient_stepsize_rule f Lf x L xDagger M)
    {xBar : E}
    (hxBar : MapClusterPt xBar Filter.atTop x) :
    BddBelow (Set.range fun k ↦ f (x k)) := by
  obtain ⟨ψ, hψmono, hψtendsto⟩ := MapClusterPt.tendsto_subseq hxBar
  have hMpos :
      0 < M :=
    uses_non_euclidean_gradient_stepsize_rule.parameter_pos hstepsize
  have hanti : Antitone (fun k ↦ f (x k)) := by
    refine antitone_nat_of_succ_le ?_
    intro k
    have hdecrease :
        f (x k) - f (x (k + 1)) ≥
          M * ‖fderiv ℝ f (x k)‖_* ^ (2 : ℕ) :=
      non_euclidean_gradient_step_decrease_ge_dual_norm_sq hf hadm hstepsize k
    have hterm_nonneg :
        0 ≤ M * ‖fderiv ℝ f (x k)‖_* ^ (2 : ℕ) := by
      exact mul_nonneg (le_of_lt hMpos) (sq_nonneg ‖fderiv ℝ f (x k)‖_*)
    exact sub_nonneg.mp (le_trans hterm_nonneg hdecrease)
  have hdiff :=
    (is_l_smooth_on_iff.mp hf).1 xBar (by simp)
  -- Continuity transports the subsequence convergence to the objective values.
  have hobj_tendsto :
      Filter.Tendsto (fun n ↦ f (x (ψ n))) Filter.atTop (nhds (f xBar)) :=
    let hcont : ContinuousAt f xBar := hdiff.continuousAt
    hcont.tendsto.comp hψtendsto
  rcases hobj_tendsto.bddBelow_range with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  intro y hy
  rcases hy with ⟨k, rfl⟩
  have hψ_ge : k ≤ ψ k := StrictMono.id_le hψmono k
  -- The antitone objective sequence dominates every term of the convergent subsequence.
  exact le_trans (hc ⟨k, rfl⟩) (hanti hψ_ge)

/-- Helper for Theorem 10.67: global `L_f`-smoothness gives the textbook cluster-point estimate
`‖f'(x̄)‖_* ≤ L_f ‖y - x̄‖ + ‖f'(y)‖_*`. -/
lemma non_euclidean_gradient_fderiv_norm_le_cluster_rhs
    (hf : is_l_smooth_on f Set.univ Lf)
    {xBar y : E} :
    ‖fderiv ℝ f xBar‖_* ≤
      (Lf : ℝ) * ‖y - xBar‖ + ‖fderiv ℝ f y‖_* := by
  have hLip :=
    (is_l_smooth_on_iff.mp hf).2 xBar (by simp) y (by simp)
  have htriangle :
      ‖fderiv ℝ f xBar‖_* ≤
        ‖fderiv ℝ f xBar - fderiv ℝ f y‖_* + ‖fderiv ℝ f y‖_* := by
    -- Rewrite `f'(x̄)` as `(f'(x̄) - f'(y)) + f'(y)` and apply the triangle inequality.
    simpa [sub_eq_add_neg, add_assoc] using
      (norm_add_le (fderiv ℝ f xBar - fderiv ℝ f y) (fderiv ℝ f y))
  calc
    ‖fderiv ℝ f xBar‖_* ≤
        ‖fderiv ℝ f xBar - fderiv ℝ f y‖_* + ‖fderiv ℝ f y‖_* := htriangle
    _ ≤ (Lf : ℝ) * ‖xBar - y‖ + ‖fderiv ℝ f y‖_* := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right hLip ‖fderiv ℝ f y‖_*
    _ = (Lf : ℝ) * ‖y - xBar‖ + ‖fderiv ℝ f y‖_* := by
      rw [norm_sub_rev]

-- Proof sketch: apply Lemma 10.66 at each iteration of the generated trajectory. The resulting
-- inequality `f(x^k) - f(x^(k+1)) ≥ M ‖f'(x^k)‖_*²` is nonnegative because `M > 0`, so the
-- objective values form a nonincreasing sequence.
/-- Theorem 10.67 (1): clause (a). If `f` is globally `L_f`-smooth and the iterates are generated
by the non-Euclidean gradient method with one of the three admissible stepsize rules from Lemma
10.66, then the objective sequence `f(x^k)` is nonincreasing. -/
theorem non_euclidean_gradient_objective_values_antitone
    (hf : is_l_smooth_on f Set.univ Lf)
    (hadm : non_euclidean_gradient_method_is_admissible f counterpart L x0)
    (hstepsize : uses_non_euclidean_gradient_stepsize_rule f Lf x L xDagger M)
    :
    Antitone (fun k ↦ f (x k)) := by
  have hMpos :
      0 < M :=
    uses_non_euclidean_gradient_stepsize_rule.parameter_pos hstepsize
  refine antitone_nat_of_succ_le ?_
  intro k
  have hdecrease :
      f (x k) - f (x (k + 1)) ≥
        M * ‖fderiv ℝ f (x k)‖_* ^ (2 : ℕ) :=
    non_euclidean_gradient_step_decrease_ge_dual_norm_sq hf hadm hstepsize k
  have hterm_nonneg :
      0 ≤ M * ‖fderiv ℝ f (x k)‖_* ^ (2 : ℕ) := by
    -- The sufficient-decrease coefficient is positive and the squared dual norm is nonnegative.
    exact mul_nonneg (le_of_lt hMpos) (sq_nonneg ‖fderiv ℝ f (x k)‖_*)
  -- A nonnegative one-step drop is exactly the successor monotonicity inequality.
  exact sub_nonneg.mp (le_trans hterm_nonneg hdecrease)

-- Proof sketch: Lemma 10.66 gives
-- `f(x^k) - f(x^(k+1)) ≥ M ‖f'(x^k)‖_*²` with `M > 0`. Hence strict decrease holds when
-- `f'(x^k) ≠ 0`. If `f'(x^k) = 0`, then the update factor `‖f'(x^k)‖_* / L_k` vanishes, so the
-- recursion gives `x^(k+1) = x^k` and therefore equality of objective values.
/-- Theorem 10.67 (2): clause (a). Under the same hypotheses, one step is strictly decreasing
exactly when the Fréchet derivative at the current iterate is nonzero. -/
theorem non_euclidean_gradient_step_strict_decrease_iff_fderiv_ne_zero
    (hf : is_l_smooth_on f Set.univ Lf)
    (hadm : non_euclidean_gradient_method_is_admissible f counterpart L x0)
    (hstepsize : uses_non_euclidean_gradient_stepsize_rule f Lf x L xDagger M)
    (k : ℕ) :
    f (x (k + 1)) < f (x k) ↔
      fderiv ℝ f (x k) ≠ 0 := by
  constructor
  · intro hlt hkzero
    have hsame :=
      non_euclidean_gradient_iterate_succ_eq_self_of_fderiv_eq_zero k hkzero
    -- Vanishing derivative forces a fixed point, contradicting strict decrease.
    simpa [hsame] using hlt
  · intro hkzero
    have hMpos :
        0 < M :=
      uses_non_euclidean_gradient_stepsize_rule.parameter_pos hstepsize
    have hdecrease :
        f (x k) - f (x (k + 1)) ≥
          M * ‖fderiv ℝ f (x k)‖_* ^ (2 : ℕ) :=
      non_euclidean_gradient_step_decrease_ge_dual_norm_sq hf hadm hstepsize k
    have hsq_pos :
        0 < ‖fderiv ℝ f (x k)‖_* ^ (2 : ℕ) := by
      exact pow_pos (norm_pos_iff.mpr hkzero) 2
    have hdrop_pos :
        0 < f (x k) - f (x (k + 1)) := by
      -- A nonzero derivative makes the sufficient-decrease lower bound strictly positive.
      exact lt_of_lt_of_le (mul_pos hMpos hsq_pos) hdecrease
    exact sub_pos.mp hdrop_pos

-- Proof sketch: clause (1) makes `f(x^k)` monotone. If its range is bounded below, then
-- `f(x^k) - f(x^(k+1)) → 0`. Combining this with the sufficient-decrease estimate from
-- Lemma 10.66 forces the dual norms `‖f'(x^k)‖_*` to converge to `0`.
/-- Theorem 10.67 (3): clause (b). If the objective values of the non-Euclidean gradient method
are bounded below, then the dual norms of the Fréchet derivatives converge to `0`. -/
theorem non_euclidean_gradient_dual_norm_tendsto_zero_of_objective_bddBelow
    (hf : is_l_smooth_on f Set.univ Lf)
    (hadm : non_euclidean_gradient_method_is_admissible f counterpart L x0)
    (hstepsize : uses_non_euclidean_gradient_stepsize_rule f Lf x L xDagger M)
    (hbelow :
      BddBelow (Set.range fun k ↦ f (x k))) :
    Filter.Tendsto
      (fun k ↦ ‖fderiv ℝ f (x k)‖_*)
      Filter.atTop (nhds 0) := by
  have hMpos :
      0 < M :=
    uses_non_euclidean_gradient_stepsize_rule.parameter_pos hstepsize
  have hstep_tendsto_zero :=
    non_euclidean_gradient_objective_step_tendsto_zero_of_bddBelow hf hadm hstepsize hbelow
  have hscaled_sq_tendsto_zero :
      Filter.Tendsto
        (fun k ↦ M * ‖fderiv ℝ f (x k)‖_* ^ (2 : ℕ))
        Filter.atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hstep_tendsto_zero ?_ ?_
    · intro k
      exact mul_nonneg (le_of_lt hMpos) (sq_nonneg ‖fderiv ℝ f (x k)‖_*)
    · intro k
      exact non_euclidean_gradient_step_decrease_ge_dual_norm_sq hf hadm hstepsize k
  have hsq_eq :
      (fun k ↦ ‖fderiv ℝ f (x k)‖_* ^ (2 : ℕ)) =
        fun k ↦ (1 / M) * (M * ‖fderiv ℝ f (x k)‖_* ^ (2 : ℕ)) := by
    funext k
    field_simp [hMpos.ne']
  have hsq_tendsto_zero :
      Filter.Tendsto
        (fun k ↦ ‖fderiv ℝ f (x k)‖_* ^ (2 : ℕ))
        Filter.atTop (nhds 0) := by
    rw [hsq_eq]
    simpa using hscaled_sq_tendsto_zero.const_mul (1 / M)
  have hnorm_eq_sqrt :
      ∀ k, ‖fderiv ℝ f (x k)‖_* = Real.sqrt (‖fderiv ℝ f (x k)‖_* ^ (2 : ℕ)) := by
    intro k
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
    exact norm_nonneg _
  have hsqrt_tendsto_zero :
      Filter.Tendsto
        (fun k ↦ Real.sqrt (‖fderiv ℝ f (x k)‖_* ^ (2 : ℕ)))
        Filter.atTop (nhds 0) := by
    let hsqrt_cont : ContinuousAt Real.sqrt 0 := Real.continuous_sqrt.continuousAt
    simpa only [Function.comp, Real.sqrt_zero] using
      hsqrt_cont.tendsto.comp hsq_tendsto_zero
  -- Nonnegativity lets us recover the dual norm from the square root of its square.
  have hEq :
      (fun k ↦ ‖fderiv ℝ f (x k)‖_*) =
        fun k ↦ Real.sqrt (‖fderiv ℝ f (x k)‖_* ^ (2 : ℕ)) := by
    funext k
    exact hnorm_eq_sqrt k
  rw [hEq]
  exact hsqrt_tendsto_zero

-- Proof sketch: sum the sufficient-decrease inequality from Lemma 10.66 over `n = 0, ..., k`,
-- telescope the objective values, and bound the sum below by `(k + 1)` times the squared running
-- minimum dual norm.
/-- Theorem 10.67 (4): clause (c). If `fOpt` is the optimal value of `min_x f(x)`, then the best
dual norm up to iteration `k` satisfies the sublinear estimate
`min_{0 ≤ n ≤ k} ‖f'(x^n)‖_* ≤ √(f(x^0) - fOpt) / √(M (k + 1))`. -/
theorem non_euclidean_gradient_best_dual_norm_up_to_le_rate
    (hf : is_l_smooth_on f Set.univ Lf)
    (hadm : non_euclidean_gradient_method_is_admissible f counterpart L x0)
    (hstepsize : uses_non_euclidean_gradient_stepsize_rule f Lf x L xDagger M)
    {fOpt : ℝ}
    (hfOpt : IsGLB (Set.range f) fOpt)
    (k : ℕ) :
    best_achieved_function_value (fun y : E ↦ ‖fderiv ℝ f y‖_*) x k ≤
      Real.sqrt (f x0 - fOpt) / Real.sqrt (M * (k + 1 : ℝ)) := by
  -- The heavy clause-(c) proof lives in the explicit-hyp core lemma, so the public theorem
  -- stays a thin source-faithful wrapper.
  exact non_euclidean_gradient_best_dual_norm_up_to_le_rate_core
    hf hadm hstepsize hfOpt k

-- Proof sketch: let `xBar` be a cluster point and extract a convergent subsequence
-- `x^(k_j) → xBar`. Clause (3) gives `‖f'(x^(k_j))‖_* → 0`, while global `L_f`-smoothness makes
-- `fderiv ℝ f` Lipschitz on `Set.univ`; hence `f'(xBar) = 0`.
/-- Theorem 10.67 (5): clause (d). Every sequential limit point of the non-Euclidean gradient
trajectory is stationary for `min_x f(x)`, in the sense that its Fréchet derivative vanishes. -/
theorem non_euclidean_gradient_cluster_point_fderiv_eq_zero
    (hf : is_l_smooth_on f Set.univ Lf)
    (hadm : non_euclidean_gradient_method_is_admissible f counterpart L x0)
    (hstepsize : uses_non_euclidean_gradient_stepsize_rule f Lf x L xDagger M)
    {xBar : E}
    (hxBar : MapClusterPt xBar Filter.atTop x) :
    fderiv ℝ f xBar = 0 := by
  obtain ⟨ψ, hψmono, hψtendsto⟩ := MapClusterPt.tendsto_subseq hxBar
  have hbelow :=
    non_euclidean_gradient_objective_bddBelow_of_cluster_point hf hadm hstepsize hxBar
  have hnorm_tendsto_zero :=
    non_euclidean_gradient_dual_norm_tendsto_zero_of_objective_bddBelow hf hadm hstepsize hbelow
  have hsubseq_norm_tendsto_zero :
      Filter.Tendsto (fun n ↦ ‖fderiv ℝ f (x (ψ n))‖_*) Filter.atTop (nhds 0) :=
    hnorm_tendsto_zero.comp hψmono.tendsto_atTop
  have hdist_tendsto_zero :
      Filter.Tendsto (fun n ↦ ‖x (ψ n) - xBar‖) Filter.atTop (nhds 0) := by
    simpa [dist_eq_norm] using (tendsto_iff_norm_sub_tendsto_zero.mp hψtendsto)
  have hcluster_rhs_tendsto_zero :
      Filter.Tendsto
        (fun n ↦ (Lf : ℝ) * ‖x (ψ n) - xBar‖ + ‖fderiv ℝ f (x (ψ n))‖_*)
        Filter.atTop (nhds 0) := by
    -- Both terms on the right-hand side of (10.84) vanish along the extracted subsequence.
    simpa using (hdist_tendsto_zero.const_mul (Lf : ℝ)).add hsubseq_norm_tendsto_zero
  have hconst_norm_tendsto_zero :
      Filter.Tendsto (fun _ : ℕ ↦ ‖fderiv ℝ f xBar‖_*) Filter.atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hcluster_rhs_tendsto_zero ?_ ?_
    · intro n
      exact norm_nonneg _
    · intro n
      exact non_euclidean_gradient_fderiv_norm_le_cluster_rhs hf
  have hnorm_zero :
      ‖fderiv ℝ f xBar‖_* = 0 := by
    exact tendsto_nhds_unique tendsto_const_nhds hconst_norm_tendsto_zero
  exact norm_eq_zero.mp hnorm_zero

end GeneratedTrajectory

end
