/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_8
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Lemma_8_27
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_4
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_5
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_6
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Lemma_9_4
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Lemma_9_25
import FirstOrderMethodsOptimization_Beck_2017.Chap09.MirrorDescentStepsize

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped BigOperators

section

variable {Lf σ : ℝ} {t : ℕ → ℝ}

/-- The canonical diminishing stepsize family from Theorem 9.18 is equivalent to the textbook
pointwise rule `t_k = √(2σ) / (L_f √(k + 1))`. -/
theorem eq_mirror_descent_predefined_diminishing_stepsize_iff :
    t = mirror_descent_predefined_diminishing_stepsize Lf σ ↔
      ∀ k, t k = Real.sqrt (2 * σ) / (Lf * Real.sqrt ((k : ℝ) + 1)) := by
  constructor
  · intro h k
    rw [h, mirror_descent_predefined_diminishing_stepsize_apply]
  · intro h
    funext k
    rw [h k, mirror_descent_predefined_diminishing_stepsize_apply]

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f g ω : E → EReal} {XStar : Set E} {FOpt Lf σ : ℝ}
variable {x : ℕ → E} {s : ℕ → StrongDual ℝ E} {t : ℕ → ℝ}

/-- Helper for Theorem 9.27: the canonical predefined diminishing Mirror-C stepsize family is
nonincreasing when `L_f > 0`. -/
lemma antitone_mirrorDescentPredefinedDiminishingStepsize
    (hLf : 0 < Lf) :
    Antitone (mirror_descent_predefined_diminishing_stepsize Lf σ) := by
  -- Increasing the index increases the square-root denominator, so the closed-form stepsizes
  -- decrease monotonically.
  intro i j hij
  rw [mirror_descent_predefined_diminishing_stepsize_apply,
    mirror_descent_predefined_diminishing_stepsize_apply]
  have hnum_nonneg : 0 ≤ Real.sqrt (2 * σ) := by positivity
  have hden_pos : 0 < Lf * Real.sqrt ((i : ℝ) + 1) := by positivity
  have hden_le :
      Lf * Real.sqrt ((i : ℝ) + 1) ≤
        Lf * Real.sqrt ((j : ℝ) + 1) := by
    have hij_real : (i : ℝ) + 1 ≤ (j : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_succ hij
    have hsqrt_le : Real.sqrt ((i : ℝ) + 1) ≤ Real.sqrt ((j : ℝ) + 1) :=
      Real.sqrt_le_sqrt hij_real
    nlinarith [hLf, hsqrt_le]
  exact div_le_div_of_nonneg_left hnum_nonneg hden_pos hden_le

omit [CompleteSpace E] in
/-- Helper for Theorem 9.27: every optimal point of the composite Mirror-C problem belongs to
`effective_domain g`. -/
lemma mirrorCOptimalPoint_mem_effectiveDomain
    (h_problem : IsCompositeMirrorDescentProblem f g XStar FOpt Lf)
    {xStar : E} (hxStar : xStar ∈ XStar) :
    xStar ∈ effective_domain g := by
  -- Compare the optimal point against any finite point in `dom(g)` to force finiteness of `g`.
  have hxStar_min : IsMinOn (fun y ↦ f y + g y) Set.univ xStar := by
    simpa [h_problem.optimal_set_eq] using hxStar
  obtain ⟨z, hz_dom⟩ := h_problem.g_proper.effective_domain_nonempty
  have hz_f : z ∈ effective_domain f := by
    exact interior_subset
      (h_problem.g_effective_domain_subset_interior_f_effective_domain hz_dom)
  have hz_sum_lt_top : f z + g z < ⊤ := by
    exact EReal.add_lt_top (mem_effective_domain.mp hz_f).ne (mem_effective_domain.mp hz_dom).ne
  have hxStar_le_z : f xStar + g xStar ≤ f z + g z := by
    exact (isMinOn_iff.mp hxStar_min) z (by simp)
  have hxStar_sum_lt_top : f xStar + g xStar < ⊤ := by
    exact lt_of_le_of_lt hxStar_le_z hz_sum_lt_top
  have hg_ne_top : g xStar ≠ ⊤ := by
    intro hg_top
    have hf_ne_bot : f xStar ≠ ⊥ := h_problem.toIsProperExtendedRealFunction.ne_bot xStar
    have hsum_top : f xStar + g xStar = ⊤ := by
      simp [hg_top, hf_ne_bot]
    exact (ne_of_lt hxStar_sum_lt_top) hsum_top
  exact mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hg_ne_top)

omit [CompleteSpace E] in
/-- Helper for Theorem 9.27: the predefined Mirror-C correction term is bounded by the harmonic
prefix sum from Lemma 8.27. -/
lemma mirrorCPredefinedCorrection_le_harmonicPrefix
    (h_problem : IsCompositeMirrorDescentProblem f g XStar FOpt Lf)
    (hω : IsBregmanPotentialOn ω (effective_domain g) σ)
    (h_traj : is_mirror_c_trajectory f g ω x s t)
    (h_stepsize : t = mirror_descent_predefined_diminishing_stepsize Lf σ)
    (k : ℕ) :
    (1 / (2 * σ)) *
        Finset.sum (Finset.range (k + 1))
          (fun n ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) ≤
      harmonicPrefixSum k := by
  -- Bound each summand using the subgradient norm cap and then normalize to the named harmonic sum.
  have hpointwise :
      ∀ n ∈ Finset.range (k + 1),
        (1 / (2 * σ)) * ((t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) ≤
          1 / ((n : ℝ) + 1) := by
    intro n hn
    have hs_norm :
        ‖s n‖ ≤ Lf :=
      h_problem.subgradient_norm_le
        (h_traj.mem_effective_domain n) (h_traj.subgradient_mem n)
    have hs_sq : ‖s n‖ ^ (2 : ℕ) ≤ Lf ^ (2 : ℕ) := by
      have hs_mul : ‖s n‖ * ‖s n‖ ≤ Lf * Lf := by
        nlinarith [hs_norm, norm_nonneg (s n), le_of_lt h_problem.Lf_pos]
      simpa [pow_two] using hs_mul
    have hLf_ne : Lf ≠ 0 := ne_of_gt h_problem.Lf_pos
    have hσ_ne : σ ≠ 0 := ne_of_gt hω.sigma_pos
    have hsqrt_ne : Real.sqrt ((n : ℝ) + 1) ≠ 0 := by positivity
    have hn1_ne : (n : ℝ) + 1 ≠ 0 := by positivity
    have h2σ_nonneg : 0 ≤ 2 * σ := by nlinarith [hω.sigma_pos]
    have hn1_nonneg : 0 ≤ (n : ℝ) + 1 := by positivity
    have hsqrt2σ_sq : Real.sqrt (2 * σ) ^ (2 : ℕ) = 2 * σ := Real.sq_sqrt h2σ_nonneg
    have hsqrtn_sq : Real.sqrt ((n : ℝ) + 1) ^ (2 : ℕ) = (n : ℝ) + 1 :=
      Real.sq_sqrt hn1_nonneg
    rw [h_stepsize, mirror_descent_predefined_diminishing_stepsize_apply]
    calc
      (1 / (2 * σ)) *
          ((Real.sqrt (2 * σ) / (Lf * Real.sqrt ((n : ℝ) + 1))) ^ (2 : ℕ) *
            ‖s n‖ ^ (2 : ℕ))
        = ‖s n‖ ^ (2 : ℕ) / (Lf ^ (2 : ℕ) * ((n : ℝ) + 1)) := by
            field_simp [pow_two, hLf_ne, hσ_ne, hsqrt_ne]
            rw [hsqrt2σ_sq, hsqrtn_sq]
      _ ≤ Lf ^ (2 : ℕ) / (Lf ^ (2 : ℕ) * ((n : ℝ) + 1)) := by
            exact div_le_div_of_nonneg_right hs_sq (by positivity)
      _ = 1 / ((n : ℝ) + 1) := by
            field_simp [pow_two, hLf_ne, hn1_ne]
  calc
    (1 / (2 * σ)) *
        Finset.sum (Finset.range (k + 1))
          (fun n ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ))
      = Finset.sum (Finset.range (k + 1))
          (fun n ↦ (1 / (2 * σ)) * ((t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ))) := by
            rw [Finset.mul_sum]
    _ ≤ Finset.sum (Finset.range (k + 1)) (fun n ↦ 1 / ((n : ℝ) + 1)) := by
          exact Finset.sum_le_sum hpointwise
    _ = harmonicPrefixSum k := by
          rw [← harmonicPrefixSum_eq_sum]

/-- Helper for Theorem 9.27: the predefined Mirror-C stepsize sum is the scaled inverse-square-root
prefix sum from Lemma 8.27. -/
lemma mirrorCPredefinedStepsizeSum_eq_scaledInverseSqrtPrefix
    (h_stepsize : t = mirror_descent_predefined_diminishing_stepsize Lf σ)
    (k : ℕ) :
    Finset.sum (Finset.range (k + 1)) (fun n ↦ t n) =
      (Real.sqrt (2 * σ) / Lf) * inverseSqrtPrefixSum k := by
  -- Pull the constant factor `√(2σ) / L_f` out of the explicit stepsize formula.
  rw [h_stepsize, inverseSqrtPrefixSum_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro n hn
  rw [mirror_descent_predefined_diminishing_stepsize_apply]
  ring_nf

/- `prompt_add/` is absent in this workspace, so the relevant API guidance comes from the local
Chapter 8 and Chapter 9 owner files. Theorem 9.27 is `source-facing`: it gives the
`O(log k / √k)` rate for the concrete Mirror-C trajectory from Definition 9.6 under the composite
problem assumptions of Definition 9.4 and the Bregman-potential assumptions of Definition 9.5,
with the specific predefined diminishing stepsize rule. The canonical owners already present are
the trajectory predicate `is_mirror_c_trajectory`, the running-best value
`best_achieved_function_value`, the composite-problem package
`IsCompositeMirrorDescentProblem`, the Bregman distance owner `B[ω]`, and the chapter-level
diminishing stepsize family `mirror_descent_predefined_diminishing_stepsize`. The same closed-form
sequence appears in Theorem 9.18, so the theorem surface here should reuse that owner rather than
restate the formula as a raw pointwise hypothesis. -/

-- Proof sketch: apply the weighted Mirror-C estimate from Lemma 9.25 to an optimal point
-- `xStar ∈ XStar`, rewrite `t n` with
-- `mirror_descent_predefined_diminishing_stepsize_apply Lf σ n`, and use the problem's
-- subgradient bound `‖f'(x^n)‖_* ≤ L_f` to convert the numerator correction term into the
-- harmonic sum `∑_{n=0}^k 1 / (n + 1)`. The resulting ratio is exactly the prefix ratio
-- controlled by Lemma 8.27 (1).
/-- Theorem 9.27: under the composite mirror-descent assumptions of Definitions 9.4,
9.5, and 9.6, if `g` is nonnegative on `dom(g)` and the Mirror-C stepsizes are given
by the canonical diminishing family
`mirror_descent_predefined_diminishing_stepsize Lf σ`, equivalently by the textbook
rule `t_k = √(2 σ) / (L_f √(k + 1))`, then for every `k ≥ 1` the running-best
composite objective gap is bounded by the `O(log k / √k)` estimate
`(L_f / √(2 σ)) * (B[ω] xStar x⁰ + (√(2 σ) / L_f) g(x⁰) + 1 + log (k + 1)) /
√(k + 1)`. -/
theorem mirror_c_best_value_gap_le_log_over_sqrt_of_predefined_diminishing_stepsizes
    (h_problem : IsCompositeMirrorDescentProblem f g XStar FOpt Lf)
    (hω : IsBregmanPotentialOn ω (effective_domain g) σ)
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (h_nonneg : ∀ z ∈ effective_domain g, 0 ≤ g z)
    (h_traj : is_mirror_c_trajectory f g ω x s t)
    {xStar : E} (hxStar : xStar ∈ XStar)
    {k : ℕ} (hk : 1 ≤ k)
    (h_stepsize : t = mirror_descent_predefined_diminishing_stepsize Lf σ) :
    best_achieved_function_value (fun y ↦ (f y + g y).toReal) x k - FOpt ≤
      (Lf / Real.sqrt (2 * σ)) *
        (B[ω] xStar (x 0) +
          (Real.sqrt (2 * σ) / Lf) * (g (x 0)).toReal +
          1 + Real.log ((k : ℝ) + 1)) /
        Real.sqrt ((k : ℝ) + 1) := by
  have _hk : 1 ≤ k := hk
  -- Route correction: prove the source ratio bound by first rewriting the weighted Lemma 9.25
  -- estimate into the Chapter 8 prefix-sum owners, and only then apply Lemma 8.27.
  let D :=
    B[ω] xStar (x 0) +
      (Real.sqrt (2 * σ) / Lf) * (g (x 0)).toReal
  have hstepsize_antitone : Antitone t := by
    rw [h_stepsize]
    exact antitone_mirrorDescentPredefinedDiminishingStepsize h_problem.Lf_pos
  have hx0_dom : x 0 ∈ effective_domain g := h_traj.mem_effective_domain 0
  have hxStar_dom : xStar ∈ effective_domain g :=
    mirrorCOptimalPoint_mem_effectiveDomain h_problem hxStar
  have hB_nonneg : 0 ≤ B[ω] xStar (x 0) := by
    -- The Bregman distance is nonnegative once both points lie in the required Chapter 9 domains.
    exact bregmanDistance_nonneg_of_mem_subdifferential_domain
      hω xStar (x 0) hxStar_dom hx0_dom (h_traj.mem_subdifferential_domain 0)
      (hω_diff _ (h_traj.mem_subdifferential_domain 0))
  have hg0_nonneg : 0 ≤ (g (x 0)).toReal := by
    -- The standing nonnegativity assumption on `g` descends from `EReal` to `ℝ`.
    exact EReal.toReal_nonneg (h_nonneg (x 0) hx0_dom)
  have hD_nonneg : 0 ≤ D := by
    have hcoeff_nonneg : 0 ≤ Real.sqrt (2 * σ) / Lf := by
      exact div_nonneg (by positivity) (le_of_lt h_problem.Lf_pos)
    dsimp [D]
    nlinarith
  have hbase :=
    mirror_c_best_value_gap_le
      (h_problem := h_problem.toIsCompositeConvexMinimizationProblem)
      hω hω_diff h_nonneg h_traj hstepsize_antitone hxStar k
  have ht0_eq : t 0 = Real.sqrt (2 * σ) / Lf := by
    rw [h_stepsize, mirror_descent_predefined_diminishing_stepsize_apply]
    simp
  have hcorr :
      (1 / (2 * σ)) *
          Finset.sum (Finset.range (k + 1))
            (fun n ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) ≤
        harmonicPrefixSum k :=
    mirrorCPredefinedCorrection_le_harmonicPrefix h_problem hω h_traj h_stepsize k
  have hsum_eq :
      Finset.sum (Finset.range (k + 1)) (fun n ↦ t n) =
        (Real.sqrt (2 * σ) / Lf) * inverseSqrtPrefixSum k :=
    mirrorCPredefinedStepsizeSum_eq_scaledInverseSqrtPrefix h_stepsize k
  have hInv_nonneg : 0 ≤ inverseSqrtPrefixSum k := by
    rw [inverseSqrtPrefixSum_eq_sum]
    exact Finset.sum_nonneg fun n hn ↦ by positivity
  have hnum_le :
      (t 0) * (g (x 0)).toReal +
          B[ω] xStar (x 0) +
          (1 / (2 * σ)) *
            Finset.sum (Finset.range (k + 1))
              (fun n ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ)) ≤
        D + harmonicPrefixSum k := by
    -- Rewrite the initial stepsize and then use the harmonic-prefix correction bound.
    have hcorr_added :=
      add_le_add_left hcorr ((t 0) * (g (x 0)).toReal + B[ω] xStar (x 0))
    simpa [D, ht0_eq, add_assoc, add_left_comm, add_comm] using hcorr_added
  have hratio :
      ((t 0) * (g (x 0)).toReal +
          B[ω] xStar (x 0) +
          (1 / (2 * σ)) *
            Finset.sum (Finset.range (k + 1))
              (fun n ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ))) /
        Finset.sum (Finset.range (k + 1)) (fun n ↦ t n) ≤
      (Lf / Real.sqrt (2 * σ)) *
        ((D + harmonicPrefixSum k) / inverseSqrtPrefixSum k) := by
    rw [hsum_eq]
    have hcoeff_nonneg : 0 ≤ Real.sqrt (2 * σ) / Lf := by
      exact div_nonneg (by positivity) (le_of_lt h_problem.Lf_pos)
    have hden_nonneg :
        0 ≤ (Real.sqrt (2 * σ) / Lf) * inverseSqrtPrefixSum k := by
      exact mul_nonneg hcoeff_nonneg hInv_nonneg
    have hdiv :=
      div_le_div_of_nonneg_right hnum_le hden_nonneg
    have hLf_ne : Lf ≠ 0 := ne_of_gt h_problem.Lf_pos
    have h2σ_pos : 0 < 2 * σ := by nlinarith [hω.sigma_pos]
    have hsqrt_pos : 0 < Real.sqrt (2 * σ) := Real.sqrt_pos.mpr h2σ_pos
    have hsqrt_ne : Real.sqrt (2 * σ) ≠ 0 := ne_of_gt hsqrt_pos
    calc
      ((t 0) * (g (x 0)).toReal +
            B[ω] xStar (x 0) +
            (1 / (2 * σ)) *
              Finset.sum (Finset.range (k + 1))
                (fun n ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ))) /
          ((Real.sqrt (2 * σ) / Lf) * inverseSqrtPrefixSum k)
        ≤ (D + harmonicPrefixSum k) /
            ((Real.sqrt (2 * σ) / Lf) * inverseSqrtPrefixSum k) := hdiv
      _ = (Lf / Real.sqrt (2 * σ)) *
            ((D + harmonicPrefixSum k) / inverseSqrtPrefixSum k) := by
          field_simp [D, hLf_ne, hsqrt_ne]
  have hprefix_ratio :=
    harmonic_prefix_ratio_le_log_bound D hD_nonneg k
  have hscaled :
      (Lf / Real.sqrt (2 * σ)) * ((D + harmonicPrefixSum k) / inverseSqrtPrefixSum k) ≤
        (Lf / Real.sqrt (2 * σ)) *
          ((D + 1 + Real.log ((k : ℝ) + 1)) / Real.sqrt ((k : ℝ) + 1)) := by
    have hcoeff_nonneg : 0 ≤ Lf / Real.sqrt (2 * σ) := by
      exact div_nonneg (le_of_lt h_problem.Lf_pos) (by positivity)
    exact mul_le_mul_of_nonneg_left hprefix_ratio hcoeff_nonneg
  calc
    best_achieved_function_value (fun y ↦ (f y + g y).toReal) x k - FOpt
      ≤ ((t 0) * (g (x 0)).toReal +
            B[ω] xStar (x 0) +
            (1 / (2 * σ)) *
              Finset.sum (Finset.range (k + 1))
                (fun n ↦ (t n) ^ (2 : ℕ) * ‖s n‖ ^ (2 : ℕ))) /
          Finset.sum (Finset.range (k + 1)) (fun n ↦ t n) := hbase
    _ ≤ (Lf / Real.sqrt (2 * σ)) *
          ((D + harmonicPrefixSum k) / inverseSqrtPrefixSum k) := hratio
    _ ≤ (Lf / Real.sqrt (2 * σ)) *
          ((D + 1 + Real.log ((k : ℝ) + 1)) / Real.sqrt ((k : ℝ) + 1)) := hscaled
    _ = (Lf / Real.sqrt (2 * σ)) *
          (B[ω] xStar (x 0) +
            (Real.sqrt (2 * σ) / Lf) * (g (x 0)).toReal +
            1 + Real.log ((k : ℝ) + 1)) /
          Real.sqrt ((k : ℝ) + 1) := by
        simp [D, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Theorem 9.27, textbook-rule companion: replacing the canonical stepsize-family equality by
the pointwise rule `t_k = √(2σ) / (L_f √(k + 1))` yields the same
`O(log k / √k)` running-best bound for the Mirror-C trajectory. -/
theorem mirror_c_best_value_gap_le_log_over_sqrt_of_textbook_diminishing_stepsizes
    (h_problem : IsCompositeMirrorDescentProblem f g XStar FOpt Lf)
    (hω : IsBregmanPotentialOn ω (effective_domain g) σ)
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (h_nonneg : ∀ z ∈ effective_domain g, 0 ≤ g z)
    (h_traj : is_mirror_c_trajectory f g ω x s t)
    {xStar : E} (hxStar : xStar ∈ XStar)
    {k : ℕ} (hk : 1 ≤ k)
    (h_stepsize :
      ∀ n, t n = Real.sqrt (2 * σ) / (Lf * Real.sqrt ((n : ℝ) + 1))) :
    best_achieved_function_value (fun y ↦ (f y + g y).toReal) x k - FOpt ≤
      (Lf / Real.sqrt (2 * σ)) *
        (B[ω] xStar (x 0) +
          (Real.sqrt (2 * σ) / Lf) * (g (x 0)).toReal +
          1 + Real.log ((k : ℝ) + 1)) /
        Real.sqrt ((k : ℝ) + 1) := by
  apply mirror_c_best_value_gap_le_log_over_sqrt_of_predefined_diminishing_stepsizes
    h_problem hω hω_diff h_nonneg h_traj hxStar hk
  exact (eq_mirror_descent_predefined_diminishing_stepsize_iff).2 h_stepsize

end
