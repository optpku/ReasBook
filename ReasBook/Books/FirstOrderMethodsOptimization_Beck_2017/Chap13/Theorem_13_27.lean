/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Algorithm_13_1
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Assumption_13_25
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Definition_13_6
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Lemma_13_7
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Lemma_13_8
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Lemma_13_12
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Lemma_13_26
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Theorem_13_14

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- `prompt_add/` is absent in this workspace, so the statement design is sampled directly from the
nearby Chapter 13 owner API.

This item is `source-facing`: it states the linear-rate estimate for the constrained
conditional-gradient method under Assumption 13.25. The relevant `core/canonical` owners already
present in the project are:

- `IsStronglyConvexConditionalGradientProblem`, specialized to the canonical optimal set
  `constrained_problem_solutions f C` and the canonical optimal value
  `generalized_conditional_gradient_optimal_value f (extendedIndicator C)`, for Assumption 13.25
  and the positive smoothness modulus needed by the textbook rate factor;
- `is_generalized_conditional_gradient_trajectory`, specialized to `g = extendedIndicator C`, for
  the constrained iterates and linear minimizers;
- `uses_generalized_conditional_gradient_adaptive_or_exact_stepsize_rule`, specialized to
  `g = extendedIndicator C`, for the admissible stepsize choice;
- `generalized_conditional_gradient_argmin` and `S[f, g](x)` for the chapter subproblem and gap.

Primitive data therefore stays upstream in those owners. This file keeps only the rate constant
from equation `(13.45)` and the two source-facing rate statements, written directly on the
canonical Chapter 13 abstractions. The scalar factor is kept only as local notation, rather than
as a separate wrapper definition, because its only mathematically correct reading here is under
the positive-smoothness owner carried by Assumption 13.25. -/

variable {f : E → EReal} {C : Set E} {σ δ : ℝ} {Lf : NNReal}
local notation "f₀" => fun y ↦ EReal.toReal (f y)
local notation "f_opt" => generalized_conditional_gradient_optimal_value f (extendedIndicator C)
local notation "F" => composite_model_objective f (extendedIndicator C)
variable
  [hproblem : IsStronglyConvexConditionalGradientProblem f C σ δ Lf]
  {x p : ℕ → E} {t : ℕ → Set.Icc (0 : ℝ) 1}
  (htraj :
    is_generalized_conditional_gradient_trajectory
      (fun y : E ↦ EReal.toReal (f y)) (extendedIndicator C) x p t)
  (hsteps :
    uses_generalized_conditional_gradient_adaptive_or_exact_stepsize_rule
      (fun y : E ↦ EReal.toReal (f y)) (extendedIndicator C) Lf x p t)

local notation "λ" => min (σ * δ / (8 * (Lf : ℝ))) (1 / 2 : ℝ)

/-- Helper for Theorem 13.27: every conditional-gradient iterate remains feasible for the
constraint set `C`. -/
lemma conditional_gradient_iterate_mem_constraint
    [hproblem : IsStronglyConvexConditionalGradientProblem f C σ δ Lf]
    (htraj :
      is_generalized_conditional_gradient_trajectory
        f₀ (extendedIndicator C) x p t)
    (k : ℕ) :
    x k ∈ C := by
  induction' k with k hk
  · -- The initial iterate is feasible by the constrained trajectory owner.
    exact is_conditional_gradient_trajectory_zero htraj
  · -- The next iterate is the convex-combination center of two feasible points.
    rcases is_conditional_gradient_trajectory_step htraj k with ⟨hpkC, _, hstep⟩
    have hradius :
        0 ≤ ((σ / 2) * (t k : ℝ) * (1 - (t k : ℝ)) * ‖p k - x k‖ ^ (2 : ℕ)) :=
      Set.strong_convex_radius_nonneg hproblem.sigma_pos.le (t k).2
    have hcenter :
        (t k : ℝ) • p k + (1 - (t k : ℝ)) • x k ∈
          Metric.closedBall
            ((t k : ℝ) • p k + (1 - (t k : ℝ)) • x k)
            (((σ / 2) * (t k : ℝ) * (1 - (t k : ℝ)) * ‖p k - x k‖ ^ (2 : ℕ)) : ℝ) := by
      simpa using
        (@Metric.mem_closedBall_self E _
          ((t k : ℝ) • p k + (1 - (t k : ℝ)) • x k)
          (((σ / 2) * (t k : ℝ) * (1 - (t k : ℝ)) * ‖p k - x k‖ ^ (2 : ℕ)) : ℝ)
          hradius)
    rw [hstep, conditional_gradient_segment_eq_convex_combo, add_comm]
    exact hproblem.strongConvex hpkC hk (t k).2 hcenter

/-- Helper for Theorem 13.27: along the constrained trajectory, the canonical Chapter 13 gap is
the finite real inner product `⟪∇f(xᵏ), xᵏ - pᵏ⟫`. -/
lemma conditional_gradient_norm_eq_coe_inner_sub
    [hproblem : IsStronglyConvexConditionalGradientProblem f C σ δ Lf]
    (htraj :
      is_generalized_conditional_gradient_trajectory
        f₀ (extendedIndicator C) x p t)
    (k : ℕ) :
    S[f₀, extendedIndicator C](x k) =
      ((inner ℝ (∇ f₀ (x k)) (x k - p k) : ℝ) : EReal) := by
  -- Realize the canonical gap at the chosen constrained argmin and cancel the indicator terms.
  have hxk : x k ∈ C :=
    @conditional_gradient_iterate_mem_constraint E _ _ _ f C σ δ Lf hproblem x p t hproblem
      htraj k
  rcases is_conditional_gradient_trajectory_step htraj k with ⟨hpkC, _, _⟩
  rw [generalized_conditional_gradient_norm_eq_of_mem_argmin (htraj.argmin_mem k),
    generalized_conditional_gradient_gap_objective_apply]
  simp [extendedIndicator, hxk, hpkC]

/-- Helper for Theorem 13.27: each constrained Frank-Wolfe gap value is nonnegative. -/
lemma conditional_gradient_gap_toReal_nonneg
    [hproblem : IsStronglyConvexConditionalGradientProblem f C σ δ Lf]
    (htraj :
      is_generalized_conditional_gradient_trajectory
        f₀ (extendedIndicator C) x p t)
    (k : ℕ) :
    0 ≤ (S[f₀, extendedIndicator C](x k)).toReal := by
  -- Compare the linear minimizer `pᵏ` against the feasible point `xᵏ`.
  have hxk : x k ∈ C :=
    @conditional_gradient_iterate_mem_constraint E _ _ _ f C σ δ Lf hproblem x p t hproblem
      htraj k
  rcases is_conditional_gradient_trajectory_step htraj k with ⟨_, hpmin, _⟩
  rw [isMinOn_iff] at hpmin
  have hle :
      inner ℝ (p k) (∇ f₀ (x k)) ≤ inner ℝ (x k) (∇ f₀ (x k)) :=
    hpmin (x k) hxk
  have hle' :
      inner ℝ (∇ f₀ (x k)) (p k) ≤ inner ℝ (∇ f₀ (x k)) (x k) := by
    simpa [real_inner_comm] using hle
  have hinner_nonneg :
      0 ≤ inner ℝ (∇ f₀ (x k)) (x k - p k) := by
    rw [inner_sub_right]
    linarith
  rw [@conditional_gradient_norm_eq_coe_inner_sub E _ _ _ f C σ δ Lf hproblem x p t hproblem
    htraj k]
  exact hinner_nonneg

/-- Helper for Theorem 13.27: the constrained objective gap is a finite real cast, so its
`toReal` is the ordinary difference of the two finite values. -/
lemma conditional_gradient_objective_gap_eq_coe_sub_optimal_value
    [hproblem : IsStronglyConvexConditionalGradientProblem f C σ δ Lf]
    (htraj :
      is_generalized_conditional_gradient_trajectory
        f₀ (extendedIndicator C) x p t)
    (k : ℕ) :
    f (x k) - f_opt =
      ((((f (x k)).toReal - (f_opt).toReal : ℝ)) : EReal) := by
  -- Rewrite both the iterate value and the optimal value through feasible finite witnesses.
  obtain ⟨xStar, hxStar⟩ := hproblem.constrained_problem_solutions_nonempty
  have hxStar_data : xStar ∈ C ∧ IsMinOn f C xStar := by
    simpa using hxStar
  have hxk : x k ∈ C :=
    @conditional_gradient_iterate_mem_constraint E _ _ _ f C σ δ Lf hproblem x p t hproblem
      htraj k
  have hxk_val :
      f (x k) = (((f (x k)).toReal : ℝ) : EReal) := by
    exact
      (EReal.coe_toReal
        (mem_effective_domain.mp (hproblem.feasible_subset_effective_domain hxk)).ne
        (hproblem.f_ne_bot (x k))).symm
  have hopt_eq : f_opt = f xStar :=
    hproblem.optimal_value_eq_of_mem_constrained_problem_solutions hxStar
  have hopt_val :
      f_opt = (((f_opt).toReal : ℝ) : EReal) := by
    rw [hopt_eq]
    exact
      (EReal.coe_toReal
        (mem_effective_domain.mp (hproblem.feasible_subset_effective_domain hxStar_data.1)).ne
        (hproblem.f_ne_bot xStar)).symm
  rw [hxk_val, hopt_val, ← EReal.coe_sub]
  simp

/-- Helper for Theorem 13.27: the constrained objective gap at every iterate is bounded above by
the canonical Frank-Wolfe gap value `S(xᵏ)`. -/
lemma conditional_gradient_objective_gap_toReal_le_gap
    [hproblem : IsStronglyConvexConditionalGradientProblem f C σ δ Lf]
    (htraj :
      is_generalized_conditional_gradient_trajectory
        f₀ (extendedIndicator C) x p t)
    (k : ℕ) :
    (f (x k) - f_opt).toReal ≤
      (S[f₀, extendedIndicator C](x k)).toReal := by
  -- Specialize Lemma 13.12 to the feasible iterate and convert the finite inequality to `ℝ`.
  have hxk : x k ∈ C :=
    @conditional_gradient_iterate_mem_constraint E _ _ _ f C σ δ Lf hproblem x p t hproblem
      htraj k
  have hxk_f : x k ∈ effective_domain f :=
    hproblem.feasible_subset_effective_domain hxk
  have hxk_g : x k ∈ effective_domain (extendedIndicator C) := by
    simpa [effective_domain_extendedIndicator] using hxk
  have hxk_diff : DifferentiableAt ℝ f₀ (x k) :=
    (hproblem.f_toReal_differentiableOn_effective_domain (x k) hxk_f).differentiableAt
      (hproblem.f_effective_domain_open.mem_nhds hxk_f)
  have hgapE :
      f (x k) - f_opt ≤ S[f₀, extendedIndicator C](x k) := by
    simpa [ge_iff_le, composite_model_objective_apply, extendedIndicator, hxk] using
      (generalized_conditional_gradient_gap_ge_objective_gap
        hproblem.f_ne_bot hproblem.f_convex hxk_f hxk_diff hxk_g)
  have hleft_bot :
      f (x k) - f_opt ≠ ⊥ := by
    rw [@conditional_gradient_objective_gap_eq_coe_sub_optimal_value
      E _ _ _ f C σ δ Lf hproblem x p t hproblem htraj k]
    exact EReal.coe_ne_bot _
  have hright_top :
      S[f₀, extendedIndicator C](x k) ≠ ⊤ := by
    rw [@conditional_gradient_norm_eq_coe_inner_sub E _ _ _ f C σ δ Lf hproblem x p t hproblem
      htraj k]
    exact EReal.coe_ne_top _
  have hreal :
      (f (x k) - f_opt).toReal ≤
        (S[f₀, extendedIndicator C](x k)).toReal :=
    EReal.toReal_le_toReal hgapE hleft_bot hright_top
  simpa using hreal

/-- Helper for Theorem 13.27: the linear-rate factor `λ` is nonnegative. -/
lemma conditional_gradient_lambda_nonneg
    [hproblem : IsStronglyConvexConditionalGradientProblem f C σ δ Lf] :
    0 ≤ λ := by
  have hnum_nonneg : 0 ≤ σ * δ := by
    nlinarith [hproblem.sigma_pos, hproblem.delta_pos]
  have hden_pos : 0 < 8 * (Lf : ℝ) := by
    nlinarith [hproblem.Lf_pos]
  have hfrac_nonneg : 0 ≤ σ * δ / (8 * (Lf : ℝ)) := by
    exact div_nonneg hnum_nonneg hden_pos.le
  exact le_min hfrac_nonneg (by positivity)

/-- Helper for Theorem 13.27: the factor `1 - λ` is nonnegative because `λ ≤ 1 / 2`. -/
lemma conditional_gradient_one_sub_lambda_nonneg
    [hproblem : IsStronglyConvexConditionalGradientProblem f C σ δ Lf] :
    0 ≤ 1 - λ := by
  have hlambda_half : λ ≤ (1 / 2 : ℝ) :=
    min_le_right _ _
  linarith

/-- Helper for Theorem 13.27: the real-valued smoothness clause from Assumption 13.25 restricts
from `dom(f)` to the smaller feasible set `C = dom(extendedIndicator C)`. -/
lemma conditional_gradient_f_toReal_smooth_on_constraint
    [hproblem : IsStronglyConvexConditionalGradientProblem f C σ δ Lf] :
    is_l_smooth_on f₀ (effective_domain (extendedIndicator C)) Lf := by
  -- Unfold both smoothness owners and restrict along the domain inclusion `C ⊆ dom(f)`.
  have hsmooth := hproblem.f_toReal_smooth_on_effective_domain
  rw [is_l_smooth_on_iff] at hsmooth ⊢
  constructor
  · intro y hy
    have hyC : y ∈ C := by
      simpa [effective_domain_extendedIndicator] using hy
    simpa [effective_domain_extendedIndicator] using
      hsmooth.1 y (hproblem.feasible_subset_effective_domain hyC)
  · intro y hy z hz
    have hyC : y ∈ C := by
      simpa [effective_domain_extendedIndicator] using hy
    have hzC : z ∈ C := by
      simpa [effective_domain_extendedIndicator] using hz
    simpa [effective_domain_extendedIndicator] using
      hsmooth.2 y (hproblem.feasible_subset_effective_domain hyC) z
        (hproblem.feasible_subset_effective_domain hzC)

/-- Helper for Theorem 13.27: on feasible points, the auxiliary exact-line-search objective
`f₀ + 𝟙_C` is just the finite objective value `f(x)`. -/
lemma conditional_gradient_auxiliary_objective_eq_coe_toReal
    [hproblem : IsStronglyConvexConditionalGradientProblem f C σ δ Lf]
    {y : E} (hy : y ∈ C) :
    composite_model_objective
        (fun z ↦ (((f z).toReal : ℝ) : EReal))
        (extendedIndicator C) y =
      (((f y).toReal : ℝ) : EReal) := by
  -- The indicator term vanishes on `C`, so only the finite `toReal` cast remains.
  rw [composite_model_objective_apply]
  simp [extendedIndicator, hy]

/-- Helper for Theorem 13.27: the constrained Frank-Wolfe gap on the trajectory is finite, so it
is the coercion of its real `toReal` value. -/
lemma conditional_gradient_gap_eq_coe_toReal
    [hproblem : IsStronglyConvexConditionalGradientProblem f C σ δ Lf]
    (htraj :
      is_generalized_conditional_gradient_trajectory
        f₀ (extendedIndicator C) x p t)
    (k : ℕ) :
    S[f₀, extendedIndicator C](x k) =
      (((S[f₀, extendedIndicator C](x k)).toReal : ℝ) : EReal) := by
  -- Rewrite the gap by the explicit finite inner-product formula along the constrained trajectory.
  rw [@conditional_gradient_norm_eq_coe_inner_sub E _ _ _ f C σ δ Lf hproblem x p t hproblem
    htraj k]
  exact (EReal.coe_toReal (EReal.coe_ne_top _) (EReal.coe_ne_bot _)).symm

/-- Helper for Theorem 13.27: under exact line search, the next iterate has no larger objective
value than any comparison point on the current segment. -/
lemma conditional_gradient_exact_step_vs_trial_point
    [hproblem : IsStronglyConvexConditionalGradientProblem f C σ δ Lf]
    (htraj :
      is_generalized_conditional_gradient_trajectory
        f₀ (extendedIndicator C) x p t)
    (hexact :
      uses_generalized_conditional_gradient_exact_line_search_rule
        f₀ (extendedIndicator C) x p t)
    (k : ℕ)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    (f (x (k + 1))).toReal ≤
      (f (x k + s • (p k - x k))).toReal := by
  -- Compare the exact-line-search value in the auxiliary objective `f₀ + 𝟙_C`, then rewrite
  -- that auxiliary objective back to the original constrained objective on feasible points.
  have hxk1 : x (k + 1) ∈ C :=
    @conditional_gradient_iterate_mem_constraint E _ _ _ f C σ δ Lf hproblem x p t hproblem
      htraj (k + 1)
  have hxk : x k ∈ C :=
    @conditional_gradient_iterate_mem_constraint E _ _ _ f C σ δ Lf hproblem x p t hproblem
      htraj k
  rcases is_conditional_gradient_trajectory_step htraj k with ⟨hpkC, _, _⟩
  have htrialC : x k + s • (p k - x k) ∈ C := by
    have hcombo :
        s • p k + (1 - s) • x k ∈ effective_domain (extendedIndicator C) :=
      combo_mem_effective_domain_of_is_convex_function
        (hproblem.toIsGeneralizedConditionalGradientProblem.g_convex)
        (by simpa [effective_domain_extendedIndicator] using hpkC)
        (by simpa [effective_domain_extendedIndicator] using hxk)
        hs
    simpa [conditional_gradient_segment_eq_convex_combo, add_comm, effective_domain_extendedIndicator]
      using hcombo
  have hcompare :
      composite_model_objective
          (fun z ↦ (((f z).toReal : ℝ) : EReal))
          (extendedIndicator C)
          (x (k + 1)) ≤
        composite_model_objective
          (fun z ↦ (((f z).toReal : ℝ) : EReal))
          (extendedIndicator C)
          (x k + s • (p k - x k)) := by
    have hexactk := hexact k
    rw [mem_conditional_gradient_exact_line_search_stepsizes_iff, isMinOn_iff] at hexactk
    rcases hexactk with ⟨_, hmin⟩
    simpa [htraj.step_eq k] using hmin s hs
  rw [@conditional_gradient_auxiliary_objective_eq_coe_toReal E _ _ _ f C σ δ Lf hproblem
      hproblem (x (k + 1)) hxk1,
    @conditional_gradient_auxiliary_objective_eq_coe_toReal E _ _ _ f C σ δ Lf hproblem
      hproblem (x k + s • (p k - x k)) htrialC] at hcompare
  exact_mod_cast hcompare

/-- Helper for Theorem 13.27: the iterate objective gap has the expected real-valued `toReal`
formula. -/
lemma conditional_gradient_gap_toReal_eq_objective_minus_optimal_value
    [hproblem : IsStronglyConvexConditionalGradientProblem f C σ δ Lf]
    (htraj :
      is_generalized_conditional_gradient_trajectory
        f₀ (extendedIndicator C) x p t)
    (k : ℕ) :
    (f (x k) - f_opt).toReal =
      (f (x k)).toReal - (f_opt).toReal := by
  -- Rewrite the `EReal` gap as a coercion of a real difference and then take `toReal`.
  rw [@conditional_gradient_objective_gap_eq_coe_sub_optimal_value
    E _ _ _ f C σ δ Lf hproblem x p t hproblem htraj k]
  simpa using EReal.toReal_coe ((f (x k)).toReal - (f_opt).toReal)

/-- Helper for Theorem 13.27: on the nondegenerate adaptive ratio branch, the quadratic gap lower
bound from Lemma 13.26 yields the factor `σ δ / (8 L_f)`. -/
lemma conditional_gradient_ratio_branch_ge_strong_convex_factor
    [hproblem : IsStronglyConvexConditionalGradientProblem f C σ δ Lf]
    (htraj :
      is_generalized_conditional_gradient_trajectory
        f₀ (extendedIndicator C) x p t)
    (k : ℕ)
    (hpx : p k ≠ x k) :
    (σ * δ / (8 * (Lf : ℝ))) *
        (S[f₀, extendedIndicator C](x k)).toReal ≤
      (S[f₀, extendedIndicator C](x k)).toReal ^ (2 : ℕ) /
        (2 * (Lf : ℝ) * ‖x k - p k‖ ^ (2 : ℕ)) := by
  -- Specialize Lemma 13.26 at the feasible iterate `xᵏ` and divide by the positive denominator
  -- `2 * L_f * ‖xᵏ - pᵏ‖²`.
  let Sx : ℝ := (S[f₀, extendedIndicator C](x k)).toReal
  have hxk : x k ∈ C :=
    @conditional_gradient_iterate_mem_constraint E _ _ _ f C σ δ Lf hproblem x p t hproblem
      htraj k
  have hxk_f : x k ∈ effective_domain f :=
    hproblem.feasible_subset_effective_domain hxk
  have hxk_diff : DifferentiableAt ℝ f₀ (x k) :=
    (hproblem.f_toReal_differentiableOn_effective_domain (x k) hxk_f).differentiableAt
      (hproblem.f_effective_domain_open.mem_nhds hxk_f)
  have hdelta :
      δ ≤ ‖∇ f₀ (x k)‖ :=
    hproblem.gradient_norm_lower_bound hxk
  have hgap_nonneg : 0 ≤ Sx := by
    dsimp [Sx]
    exact
      @conditional_gradient_gap_toReal_nonneg E _ _ _ f C σ δ Lf hproblem x p t hproblem
        htraj k
  have hxkp : x k ≠ p k := by
    simpa [eq_comm] using hpx
  have hnorm_pos : 0 < ‖x k - p k‖ := by
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hxkp)
  have hnorm_sq_pos : 0 < ‖x k - p k‖ ^ (2 : ℕ) := by
    exact pow_pos hnorm_pos _
  have hquad :
      (σ * δ / 4) * ‖x k - p k‖ ^ (2 : ℕ) ≤ Sx := by
    let xC : C := ⟨x k, hxk⟩
    simpa [Sx, xC] using
      (generalized_conditional_gradient_norm_ge_strong_convexity_quadratic_bound
        hproblem.sigma_pos hproblem.strongConvex xC hxk_diff hdelta (p k)
        (htraj.argmin_mem k))
  have hmul :
      ((σ * δ / 4) * ‖x k - p k‖ ^ (2 : ℕ)) * Sx ≤ Sx ^ (2 : ℕ) := by
    have hmul_raw := mul_le_mul_of_nonneg_right hquad hgap_nonneg
    simpa [pow_two] using hmul_raw
  have hden_pos :
      0 < 2 * (Lf : ℝ) * ‖x k - p k‖ ^ (2 : ℕ) := by
    have htwoLf_pos : 0 < 2 * (Lf : ℝ) := by
      nlinarith [hproblem.Lf_pos]
    exact mul_pos htwoLf_pos hnorm_sq_pos
  apply (le_div_iff₀ hden_pos).mpr
  calc
    (σ * δ / (8 * (Lf : ℝ))) * Sx * (2 * (Lf : ℝ) * ‖x k - p k‖ ^ (2 : ℕ)) =
        ((σ * δ / 4) * ‖x k - p k‖ ^ (2 : ℕ)) * Sx := by
          field_simp [hproblem.Lf_pos.ne']
          ring
    _ ≤ Sx ^ (2 : ℕ) := hmul

/-- Helper for Theorem 13.27: the adaptive trial point
`xᵏ + sₖ (pᵏ - xᵏ)` with the textbook adaptive stepsize already satisfies the source proof's
decrease estimate `λ S(xᵏ) ≤ f(xᵏ) - f(x̃ᵏ)`. -/
lemma conditional_gradient_adaptive_trial_drop_ge_lambda_gap
    [hproblem : IsStronglyConvexConditionalGradientProblem f C σ δ Lf]
    (htraj :
      is_generalized_conditional_gradient_trajectory
        f₀ (extendedIndicator C) x p t)
    (k : ℕ) :
    let s := conditional_gradient_adaptive_stepsize
      (S[f₀, extendedIndicator C](x k)).toReal Lf (x k) (p k)
    let xTilde := x k + s • (p k - x k)
    λ * (S[f₀, extendedIndicator C](x k)).toReal ≤
      (f (x k)).toReal - (f xTilde).toReal := by
  -- Follow the source proof literally: evaluate Lemma 13.7 at the adaptive trial point and then
  -- split the adaptive scalar into the clipped branch `s = 1` and the ratio branch.
  dsimp
  let Sx : ℝ := (S[f₀, extendedIndicator C](x k)).toReal
  let s : ℝ := conditional_gradient_adaptive_stepsize Sx Lf (x k) (p k)
  let xTilde : E := x k + s • (p k - x k)
  have hxk : x k ∈ C :=
    @conditional_gradient_iterate_mem_constraint E _ _ _ f C σ δ Lf hproblem x p t hproblem
      htraj k
  rcases is_conditional_gradient_trajectory_step htraj k with ⟨hpkC, _, _⟩
  have hS_nonneg : 0 ≤ Sx := by
    dsimp [Sx]
    exact
      @conditional_gradient_gap_toReal_nonneg E _ _ _ f C σ δ Lf hproblem x p t hproblem
        htraj k
  have hs_mem : s ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [s, Sx]
    exact conditional_gradient_adaptive_stepsize_mem_Icc hS_nonneg Lf (x k) (p k)
  have htrialC : xTilde ∈ C := by
    have hcombo :
        s • p k + (1 - s) • x k ∈ effective_domain (extendedIndicator C) :=
      combo_mem_effective_domain_of_is_convex_function
        (hproblem.toIsGeneralizedConditionalGradientProblem.g_convex)
        (by simpa [effective_domain_extendedIndicator] using hpkC)
        (by simpa [effective_domain_extendedIndicator] using hxk)
        hs_mem
    simpa [xTilde, s, conditional_gradient_segment_eq_convex_combo, add_comm,
      effective_domain_extendedIndicator] using hcombo
  have hfund :
      (f xTilde).toReal ≤
        (f (x k)).toReal - s * Sx +
          (((s ^ (2 : ℕ) * (Lf : ℝ)) / 2) * ‖p k - x k‖ ^ (2 : ℕ)) := by
    -- Rewrite the generalized composite objective back to `f` on feasible points.
    have hfund_raw :
        composite_model_objective (Function.toEReal f₀) (extendedIndicator C) xTilde ≤
          composite_model_objective (Function.toEReal f₀) (extendedIndicator C) (x k) -
            (s : EReal) * S[f₀, extendedIndicator C](x k) +
              ((((s ^ (2 : ℕ) * (Lf : ℝ)) / 2) * ‖p k - x k‖ ^ (2 : ℕ) : ℝ) : EReal) := by
      simpa [Function.toEReal, xTilde, pow_two, mul_assoc, mul_left_comm, mul_comm] using
        (generalized_conditional_gradient_fundamental_inequality
          (by
            intro y
            by_cases hy : y ∈ C <;> simp [extendedIndicator, hy])
          hproblem.toIsGeneralizedConditionalGradientProblem.g_convex
          (@conditional_gradient_f_toReal_smooth_on_constraint
            E _ _ _ f C σ δ Lf hproblem hproblem)
          (by simpa [effective_domain_extendedIndicator] using hxk)
          (htraj.argmin_mem k)
          hs_mem)
    have hxk_aux :
        composite_model_objective (Function.toEReal f₀) (extendedIndicator C) (x k) =
          (((f (x k)).toReal : ℝ) : EReal) := by
      simpa [Function.toEReal] using
        (@conditional_gradient_auxiliary_objective_eq_coe_toReal E _ _ _ f C σ δ Lf hproblem
          hproblem (x k) hxk)
    have htrial_aux :
        composite_model_objective (Function.toEReal f₀) (extendedIndicator C) xTilde =
          (((f xTilde).toReal : ℝ) : EReal) := by
      simpa [Function.toEReal] using
        (@conditional_gradient_auxiliary_objective_eq_coe_toReal E _ _ _ f C σ δ Lf hproblem
          hproblem xTilde htrialC)
    have hgap_aux :
        S[f₀, extendedIndicator C](x k) = ((Sx : ℝ) : EReal) := by
      dsimp [Sx]
      exact
        @conditional_gradient_gap_eq_coe_toReal E _ _ _ f C σ δ Lf hproblem x p t hproblem
          htraj k
    rw [htrial_aux, hxk_aux, hgap_aux, ← EReal.coe_mul, ← EReal.coe_sub, ← EReal.coe_add] at hfund_raw
    exact_mod_cast hfund_raw
  have hmodel :
      s * Sx -
          (((s ^ (2 : ℕ) * (Lf : ℝ)) / 2) * ‖p k - x k‖ ^ (2 : ℕ)) ≤
        (f (x k)).toReal - (f xTilde).toReal := by
    linarith
  have hmain : λ * Sx ≤ (f (x k)).toReal - (f xTilde).toReal := by
    by_cases hpx : p k = x k
    · -- If `pᵏ = xᵏ`, then the gap vanishes and the trial point is `xᵏ` itself.
      have hs_one : s = 1 := by
        dsimp [s]
        simpa [hpx] using
          conditional_gradient_adaptive_stepsize_eq_one_of_eq Sx Lf (x k)
      have hgap_zero : Sx = 0 := by
        dsimp [Sx]
        rw [@conditional_gradient_norm_eq_coe_inner_sub E _ _ _ f C σ δ Lf hproblem x p t
          hproblem htraj k, hpx]
        simp
      have htrial_eq : xTilde = x k := by
        dsimp [xTilde]
        rw [hs_one, hpx]
        simp
      simp [hgap_zero, htrial_eq]
    · -- On the nonstationary branch, the adaptive rule is `min {1, Sx / (L_f ‖xᵏ - pᵏ‖²)}`.
      have hLf_ne : Lf ≠ 0 := by
        intro hLf
        exact (ne_of_gt hproblem.Lf_pos) (by simpa [hLf])
      have hs_eq :
          s = min (1 : ℝ)
            (Sx / ((Lf : ℝ) * ‖p k - x k‖ ^ (2 : ℕ))) := by
        dsimp [s]
        exact conditional_gradient_adaptive_stepsize_of_ne Sx hpx hLf_ne
      have hnorm_pos : 0 < ‖p k - x k‖ := by
        exact norm_pos_iff.mpr (sub_ne_zero.mpr hpx)
      have hden_pos :
          0 < (Lf : ℝ) * ‖p k - x k‖ ^ (2 : ℕ) := by
        positivity
      by_cases hratio : Sx / ((Lf : ℝ) * ‖p k - x k‖ ^ (2 : ℕ)) ≤ 1
      · -- On the ratio branch, the quadratic expression equals the model drop and Lemma 13.26
        -- supplies the factor `σ δ / (8 L_f)`.
        have hs_ratio :
            s = Sx / ((Lf : ℝ) * ‖p k - x k‖ ^ (2 : ℕ)) := by
          rw [hs_eq, min_eq_right hratio]
        have hcore :
            Sx ^ (2 : ℕ) / (2 * (Lf : ℝ) * ‖p k - x k‖ ^ (2 : ℕ)) =
              s * Sx -
                (((s ^ (2 : ℕ) * (Lf : ℝ)) / 2) * ‖p k - x k‖ ^ (2 : ℕ)) := by
          rw [hs_ratio]
          field_simp [hden_pos.ne']
          ring
        have hratio_bound :
            (σ * δ / (8 * (Lf : ℝ))) * Sx ≤
              (f (x k)).toReal - (f xTilde).toReal := by
          have hratio_gap :
              (σ * δ / (8 * (Lf : ℝ))) * Sx ≤
                Sx ^ (2 : ℕ) / (2 * (Lf : ℝ) * ‖p k - x k‖ ^ (2 : ℕ)) := by
            simpa [Sx, norm_sub_rev] using
              @conditional_gradient_ratio_branch_ge_strong_convex_factor
                E _ _ _ f C σ δ Lf hproblem x p t hproblem htraj k hpx
          have hratio_model :
              Sx ^ (2 : ℕ) / (2 * (Lf : ℝ) * ‖p k - x k‖ ^ (2 : ℕ)) ≤
                (f (x k)).toReal - (f xTilde).toReal := by
            rw [hcore]
            exact hmodel
          exact le_trans hratio_gap hratio_model
        have hlambda_le :
            λ * Sx ≤ (σ * δ / (8 * (Lf : ℝ))) * Sx := by
          exact mul_le_mul_of_nonneg_right (min_le_left _ _) hS_nonneg
        exact le_trans hlambda_le hratio_bound
      · -- On the clipped branch `s = 1`, the decrease is at least `(1 / 2) Sx`.
        have hratio_ge :
            1 ≤ Sx / ((Lf : ℝ) * ‖p k - x k‖ ^ (2 : ℕ)) := by
          linarith
        have hs_one : s = 1 := by
          rw [hs_eq, min_eq_left hratio_ge]
        have hden_le_gap :
            (Lf : ℝ) * ‖p k - x k‖ ^ (2 : ℕ) ≤ Sx := by
          exact (one_le_div₀ hden_pos).mp hratio_ge
        have hhalf_drop :
            (1 / 2 : ℝ) * Sx ≤ (f (x k)).toReal - (f xTilde).toReal := by
          have hstep_bound :
              Sx -
                  (((1 ^ (2 : ℕ) * (Lf : ℝ)) / 2) * ‖p k - x k‖ ^ (2 : ℕ)) ≤
                (f (x k)).toReal - (f xTilde).toReal := by
            simpa [hs_one] using hmodel
          have hhalf_den :
              (((1 ^ (2 : ℕ) * (Lf : ℝ)) / 2) * ‖p k - x k‖ ^ (2 : ℕ)) ≤
                (1 / 2 : ℝ) * Sx := by
            nlinarith [hden_le_gap]
          have hhalf_le :
              (1 / 2 : ℝ) * Sx ≤
                Sx -
                  (((1 ^ (2 : ℕ) * (Lf : ℝ)) / 2) * ‖p k - x k‖ ^ (2 : ℕ)) := by
            linarith
          exact le_trans hhalf_le hstep_bound
        have hlambda_le :
            λ * Sx ≤ (1 / 2 : ℝ) * Sx := by
          exact mul_le_mul_of_nonneg_right (min_le_right _ _) hS_nonneg
        exact le_trans hlambda_le hhalf_drop
  simpa [Sx, s, xTilde] using hmain

/-- Helper for Theorem 13.27: the one-step decrease estimate from equations (13.46)--(13.49)
gives an actual drop of at least `λ S(xᵏ)` in objective value. -/
lemma conditional_gradient_step_drop_ge_lambda_gap
    [hproblem : IsStronglyConvexConditionalGradientProblem f C σ δ Lf]
    (htraj :
      is_generalized_conditional_gradient_trajectory
        f₀ (extendedIndicator C) x p t)
    (hsteps :
      uses_generalized_conditional_gradient_adaptive_or_exact_stepsize_rule
        f₀ (extendedIndicator C) Lf x p t)
    (k : ℕ) :
    λ * (S[f₀, extendedIndicator C](x k)).toReal ≤
      (f (x k)).toReal - (f (x (k + 1))).toReal := by
  -- Compare both admissible stepsize rules against the same adaptive trial point from the source
  -- proof, then keep the exact-line-search branch as a thin monotonicity adapter.
  let s : ℝ := conditional_gradient_adaptive_stepsize
    (S[f₀, extendedIndicator C](x k)).toReal Lf (x k) (p k)
  let xTilde : E := x k + s • (p k - x k)
  have hS_nonneg :
      0 ≤ (S[f₀, extendedIndicator C](x k)).toReal :=
    @conditional_gradient_gap_toReal_nonneg E _ _ _ f C σ δ Lf hproblem x p t hproblem
      htraj k
  have hs_mem : s ∈ Set.Icc (0 : ℝ) 1 := by
    dsimp [s]
    exact conditional_gradient_adaptive_stepsize_mem_Icc hS_nonneg Lf (x k) (p k)
  have htrial :
      λ * (S[f₀, extendedIndicator C](x k)).toReal ≤
        (f (x k)).toReal - (f xTilde).toReal := by
    simpa [s, xTilde] using
      @conditional_gradient_adaptive_trial_drop_ge_lambda_gap
        E _ _ _ f C σ δ Lf hproblem x p t hproblem htraj k
  rcases hsteps with hadapt | hexact
  · -- Under the adaptive rule, the next iterate is the adaptive trial point itself.
    rcases hadapt k with ⟨_, _, htk_eq⟩
    have hstep_eq : x (k + 1) = xTilde := by
      dsimp [xTilde, s]
      rw [htraj.step_eq k, htk_eq]
      rfl
    rw [hstep_eq]
    exact htrial
  · -- Under exact line search, the next iterate improves on every feasible comparison step.
    have hcompare :
        (f (x (k + 1))).toReal ≤ (f xTilde).toReal := by
      simpa [s, xTilde] using
        @conditional_gradient_exact_step_vs_trial_point
          E _ _ _ f C σ δ Lf hproblem x p t hproblem htraj hexact k s hs_mem
    linarith

include hproblem htraj hsteps

-- Proof sketch: combine the sufficient-decrease estimate for adaptive stepsize / exact line
-- search with the strong-convex-feasible-set gap lower bound from Lemma 13.26. The ratio
-- estimate yields the contraction factor `1 - λ`, where
-- `λ = min {σ δ / (8 L_f), 1 / 2}`.
/-- Theorem 13.27 (1): under Assumption 13.25, every adaptive-step or exact-line-search
conditional-gradient iteration contracts the constrained objective gap by the factor
`1 - λ`, where `λ = min {σ δ / (8 L_f), 1 / 2}`. -/
theorem conditional_gradient_objective_gap_step_le_linear_rate_factor
    (k : ℕ) :
    (f (x (k + 1)) - f_opt).toReal ≤
      (1 - λ) *
        (f (x k) - f_opt).toReal := by
  -- Route correction: include the section owners so this theorem genuinely quantifies the
  -- trajectory and stepsize data required by the source proof.
  have hstep_drop :
      λ * (f (x k) - f_opt).toReal ≤
        (f (x k)).toReal - (f (x (k + 1))).toReal := by
    have hgap_le :
        (f (x k) - f_opt).toReal ≤
          (S[f₀, extendedIndicator C](x k)).toReal :=
      @conditional_gradient_objective_gap_toReal_le_gap
        E _ _ _ f C σ δ Lf hproblem x p t hproblem htraj k
    have hstep_gap :
        λ * (S[f₀, extendedIndicator C](x k)).toReal ≤
          (f (x k)).toReal - (f (x (k + 1))).toReal :=
      @conditional_gradient_step_drop_ge_lambda_gap
        E _ _ _ f C σ δ Lf hproblem x p t hproblem htraj hsteps k
    exact le_trans
      (mul_le_mul_of_nonneg_left hgap_le
        (@conditional_gradient_lambda_nonneg E _ _ _ f C σ δ Lf hproblem hproblem))
      hstep_gap
  let gapk : ℝ := (f (x k) - f_opt).toReal
  have hgapk :
      gapk = (f (x k)).toReal - (f_opt).toReal := by
    dsimp [gapk]
    exact
      @conditional_gradient_gap_toReal_eq_objective_minus_optimal_value
        E _ _ _ f C σ δ Lf hproblem x p t hproblem htraj k
  have hgapk1 :
      (f (x (k + 1)) - f_opt).toReal =
        (f (x (k + 1))).toReal - (f_opt).toReal := by
    exact
      @conditional_gradient_gap_toReal_eq_objective_minus_optimal_value
        E _ _ _ f C σ δ Lf hproblem x p t hproblem htraj (k + 1)
  have hstep_drop' :
      λ * gapk ≤ (f (x k)).toReal - (f (x (k + 1))).toReal := by
    simpa [gapk] using hstep_drop
  have hstep_drop'' :
      λ * ((f (x k)).toReal - (f_opt).toReal) ≤
        (f (x k)).toReal - (f (x (k + 1))).toReal := by
    simpa [hgapk] using hstep_drop'
  rw [hgapk1, show (f (x k) - f_opt).toReal = gapk by rfl]
  rw [hgapk]
  nlinarith [hstep_drop'']

-- Proof sketch: iterate the one-step contraction from clause `(1)` over the indices
-- `0, 1, ..., k - 1`. The product of the identical contraction factors is `(1 - λ)^k`, yielding
-- the geometric bound relative to the initial objective gap.
/-- Theorem 13.27 (2): under Assumption 13.25, the constrained objective gap along the adaptive
or exact-line-search conditional-gradient trajectory decays geometrically:
`f(xᵏ) - f_opt ≤ (1 - λ)^k (f(x⁰) - f_opt)`. -/
theorem conditional_gradient_objective_gap_le_geometric_rate
    (k : ℕ) :
    (f (x k) - f_opt).toReal ≤
      (1 - λ) ^ k *
        (f (x 0) - f_opt).toReal := by
  -- Iterate the one-step contraction and keep the scalar factor nonnegative at each step.
  induction' k with k hk
  · simp
  · have hstep :=
      @conditional_gradient_objective_gap_step_le_linear_rate_factor
        E _ _ _ f C σ δ Lf hproblem x p t htraj hsteps k
    have hone :
        0 ≤ 1 - λ :=
      @conditional_gradient_one_sub_lambda_nonneg E _ _ _ f C σ δ Lf hproblem hproblem
    calc
      (f (x (k + 1)) - f_opt).toReal ≤
          (1 - λ) * (f (x k) - f_opt).toReal := hstep
      _ ≤ (1 - λ) * ((1 - λ) ^ k * (f (x 0) - f_opt).toReal) := by
          exact mul_le_mul_of_nonneg_left hk hone
      _ = (1 - λ) ^ (k + 1) * (f (x 0) - f_opt).toReal := by
          rw [pow_succ]
          ring

end
