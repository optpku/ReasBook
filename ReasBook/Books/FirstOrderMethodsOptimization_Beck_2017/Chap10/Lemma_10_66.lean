/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_5
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_62
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_11
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Lemma_10_14
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Lemma_10_65

local notation "Λ[" a "]" => primalCounterparts a

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped DualNorm

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The exact line search stepsizes along the non-Euclidean descent ray
`α ↦ x - α ‖f'(x)‖_* xDagger`. -/
def non_euclidean_exact_line_search_stepsizes
    (f : E → ℝ) (x xDagger : E) : Set ℝ :=
  constrained_problem_solutions
    (fun t ↦ f (x - (t * ‖fderiv ℝ f x‖_*) • xDagger))
    (Set.Ici (0 : ℝ))

-- Proof sketch: unfold `non_euclidean_exact_line_search_stepsizes`; membership is definitionally
-- the conjunction of nonnegativity and minimality of the one-dimensional line-search objective.
/-- A scalar belongs to the non-Euclidean exact line search set exactly when it is nonnegative and
minimizes the descent objective along the chosen non-Euclidean ray. -/
@[simp] theorem mem_non_euclidean_exact_line_search_stepsizes_iff
    {f : E → ℝ} {x xDagger : E} {α : ℝ} :
    α ∈ non_euclidean_exact_line_search_stepsizes f x xDagger ↔
      0 ≤ α ∧
        IsMinOn
          (fun t ↦ f (x - (t * ‖fderiv ℝ f x‖_*) • xDagger))
          (Set.Ici (0 : ℝ)) α := by
  simp [non_euclidean_exact_line_search_stepsizes]

/-- The exact-line-search branch in Lemma 10.66: at every iteration `k`, the reciprocal
curvature estimate `1 / L_k` belongs to the exact line-search set along the chosen
non-Euclidean descent ray at `x^k`. -/
def uses_non_euclidean_exact_line_search_stepsize_rule
    (f : E → ℝ) (x : ℕ → E) (L : ℕ → PosReal) (xDagger : ℕ → E) : Prop :=
  ∀ k : ℕ, (1 / (L k : ℝ)) ∈ non_euclidean_exact_line_search_stepsizes f (x k) (xDagger k)

/-- The admissible non-Euclidean stepsize regime in Lemma 10.66, together with its sufficient
decrease constant `M`: either a constant curvature rule, backtracking procedure B4, or exact
line search. -/
def uses_non_euclidean_gradient_stepsize_rule
    (f : E → ℝ) (Lf : NNReal) (x : ℕ → E) (L : ℕ → PosReal) (xDagger : ℕ → E)
    (M : ℝ) : Prop :=
  (∃ barL : ProximalGradientConstantStepsizeParameter Lf,
      L = Function.const ℕ (barL : PosReal) ∧
        M = ((barL : ℝ) - (Lf : ℝ) / 2) / ((barL : ℝ) ^ (2 : ℕ))) ∨
    (∃ s : PosReal, ∃ γ : ProximalGradientBacktrackingDecreaseFraction,
      ∃ η : ProximalGradientBacktrackingGrowthFactor,
        uses_non_euclidean_backtracking_B4_rule f x L xDagger s γ η ∧
          M = (γ : ℝ) / max (s : ℝ) (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ))))) ∨
    (0 < (Lf : ℝ) ∧
      uses_non_euclidean_exact_line_search_stepsize_rule f x L xDagger ∧
        M = 1 / (2 * (Lf : ℝ)))

namespace uses_non_euclidean_exact_line_search_stepsize_rule

/-- Bridge/view layer: the exact-line-search owner canonically supplies the exact-line-search
branch of `uses_non_euclidean_gradient_stepsize_rule` with sufficient-decrease coefficient
`1 / (2 L_f)`. -/
theorem to_gradient_stepsize_rule
    {f : E → ℝ} {Lf : NNReal} {x : ℕ → E} {L : ℕ → PosReal} {xDagger : ℕ → E}
    (hsearch : uses_non_euclidean_exact_line_search_stepsize_rule f x L xDagger)
    (hLf : 0 < (Lf : ℝ)) :
    uses_non_euclidean_gradient_stepsize_rule f Lf x L xDagger (1 / (2 * (Lf : ℝ))) := by
  exact Or.inr <| Or.inr ⟨hLf, hsearch, rfl⟩

end uses_non_euclidean_exact_line_search_stepsize_rule

/-- Helper for Lemma 10.66: any trial curvature above the non-Euclidean smoothness threshold
`L_f / (2 * (1 - γ))` satisfies the B4 acceptance test. -/
theorem non_euclidean_backtracking_B4_accepts_of_stepsize_ge_smoothness_threshold
    {f : E → ℝ} {Lf : NNReal} (hf : is_l_smooth_on f Set.univ Lf)
    (γ : ProximalGradientBacktrackingDecreaseFraction)
    (L : PosReal) {x xDagger : E}
    (hDagger : xDagger ∈ Λ[fderiv ℝ f x])
    (hthreshold : (Lf : ℝ) / (2 * (1 - (γ : ℝ))) ≤ (L : ℝ)) :
    non_euclidean_gradient_backtracking_B4_accepts f γ L x xDagger := by
  let residual : ℝ := ‖fderiv ℝ f x‖_* ^ (2 : ℕ)
  -- Lemma 10.65 supplies the one-step decrease with the trial curvature `L`.
  have hdecrease :
      f (x - (‖fderiv ℝ f x‖_* / (L : ℝ)) • xDagger) ≤
        f x - (((L : ℝ) - (Lf : ℝ) / 2) / (L : ℝ) ^ (2 : ℕ)) * residual := by
    simpa [residual] using
      non_euclidean_gradient_method_sufficient_decrease hf x L xDagger hDagger
  have hresidual_nonneg : 0 ≤ residual := by
    -- The squared dual norm is nonnegative.
    dsimp [residual]
    positivity
  have hL_pos : 0 < (L : ℝ) := L.2
  have hL_sq_nonneg : 0 ≤ (L : ℝ) ^ (2 : ℕ) := by
    positivity
  have hdenom_pos : 0 < 2 * (1 - (γ : ℝ)) := by
    nlinarith [γ.2]
  have hlinear :
      (γ : ℝ) * (L : ℝ) ≤ (L : ℝ) - (Lf : ℝ) / 2 := by
    have hthreshold_mul : (Lf : ℝ) ≤ (L : ℝ) * (2 * (1 - (γ : ℝ))) := by
      exact (div_le_iff₀ hdenom_pos).1 hthreshold
    -- This is the textbook threshold inequality rewritten into linear form.
    nlinarith
  have hdiv :
      ((γ : ℝ) * (L : ℝ)) / (L : ℝ) ^ (2 : ℕ) ≤
        ((L : ℝ) - (Lf : ℝ) / 2) / (L : ℝ) ^ (2 : ℕ) := by
    exact div_le_div_of_nonneg_right hlinear hL_sq_nonneg
  have hL_ne : (L : ℝ) ≠ 0 := ne_of_gt hL_pos
  have hleft :
      ((γ : ℝ) * (L : ℝ)) / (L : ℝ) ^ (2 : ℕ) = (γ : ℝ) / (L : ℝ) := by
    field_simp [pow_two, hL_ne]
  have hcoeff :
      (γ : ℝ) / (L : ℝ) ≤
        ((L : ℝ) - (Lf : ℝ) / 2) / (L : ℝ) ^ (2 : ℕ) := by
    -- Rewriting the left side through the common denominator `L^2` exposes monotonicity.
    rw [← hleft]
    exact hdiv
  have hscaled :
      ((γ : ℝ) / (L : ℝ)) * residual ≤
        (((L : ℝ) - (Lf : ℝ) / 2) / (L : ℝ) ^ (2 : ℕ)) * residual := by
    exact mul_le_mul_of_nonneg_right hcoeff hresidual_nonneg
  have hdrop :
      (((L : ℝ) - (Lf : ℝ) / 2) / (L : ℝ) ^ (2 : ℕ)) * residual ≤
        f x - f (x - (‖fderiv ℝ f x‖_* / (L : ℝ)) • xDagger) := by
    linarith
  -- Combining the coefficient comparison with Lemma 10.65 yields the B4 acceptance inequality.
  simpa [non_euclidean_gradient_backtracking_B4_accepts, residual] using
    le_trans hscaled hdrop

/-- Helper for Lemma 10.66: consecutive non-Euclidean B4 trial curvatures differ by the
multiplicative factor `η`. -/
theorem non_euclidean_backtracking_trial_stepsize_succ_coe
    (s : PosReal) (η : ProximalGradientBacktrackingGrowthFactor)
    (n : ℕ) :
    (proximal_gradient_backtracking_trial_stepsize s η (n + 1) : ℝ) =
      (η : ℝ) * (proximal_gradient_backtracking_trial_stepsize s η n : ℝ) := by
  -- Unfold the geometric trial family and rewrite `η^(n+1)` as `η * η^n`.
  simp [proximal_gradient_backtracking_trial_stepsize_coe, pow_succ, mul_left_comm, mul_comm]

-- Proof sketch: if the accepted index is `i = 0`, then the accepted curvature equals `s`.
-- Otherwise the preceding trial is rejected by minimality. Applying the one-step estimate from
-- Lemma 10.65 shows that every trial curvature at least `η L_f / (2 (1 - γ))` is accepted, so
-- the final accepted trial is bounded by `max {s, η L_f / (2 (1 - γ))}`.
/-- Under global `L_f`-smoothness, the trial curvature accepted by backtracking procedure B4 is
bounded by `max {s, η L_f / (2 (1 - γ))}`. -/
theorem non_euclidean_backtracking_B4_stepsize_le_max_initial_or_smoothness_threshold
    {f : E → ℝ} {Lf : NNReal} (hf : is_l_smooth_on f Set.univ Lf)
    (s : PosReal) (γ : ProximalGradientBacktrackingDecreaseFraction)
    (η : ProximalGradientBacktrackingGrowthFactor)
    {x xDagger : E} {i : ℕ}
    (hi : is_backtracking_procedure_B4_index f s γ η x xDagger i) :
    (proximal_gradient_backtracking_trial_stepsize s η i : ℝ) ≤
      max (s : ℝ)
        (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ)))) := by
  cases i with
  | zero =>
      -- The initial accepted trial is exactly the starting curvature `s`.
      simpa [proximal_gradient_backtracking_trial_stepsize_coe] using
        (le_max_left (s : ℝ)
          (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ)))))
  | succ n =>
      -- Minimality forces the previous geometric trial to be rejected.
      have hreject :
          ¬ non_euclidean_gradient_backtracking_B4_accepts
            f γ (proximal_gradient_backtracking_trial_stepsize s η n) x xDagger :=
        is_backtracking_procedure_B4_index_minimal hi (Nat.lt_succ_self n)
      have htrial_lt_threshold :
          (proximal_gradient_backtracking_trial_stepsize s η n : ℝ) <
            (Lf : ℝ) / (2 * (1 - (γ : ℝ))) := by
        refine lt_of_not_ge fun hge ↦ ?_
        exact hreject <|
          non_euclidean_backtracking_B4_accepts_of_stepsize_ge_smoothness_threshold
            hf γ (proximal_gradient_backtracking_trial_stepsize s η n)
            (is_backtracking_procedure_B4_index_counterpart_mem hi) hge
      have hη_pos : 0 < (η : ℝ) := lt_trans zero_lt_one η.2
      have hmul_lt :
          (η : ℝ) * (proximal_gradient_backtracking_trial_stepsize s η n : ℝ) <
            (η : ℝ) * ((Lf : ℝ) / (2 * (1 - (γ : ℝ)))) := by
        exact mul_lt_mul_of_pos_left htrial_lt_threshold hη_pos
      have hbound :
          (proximal_gradient_backtracking_trial_stepsize s η (n + 1) : ℝ) <
            (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ)))) := by
        -- Consecutive trial curvatures differ by the geometric growth factor `η`.
        rw [non_euclidean_backtracking_trial_stepsize_succ_coe]
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul_lt
      exact le_trans (le_of_lt hbound) (le_max_right (s : ℝ)
        (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ)))))

section SufficientDecreaseRule

variable {f : E → ℝ} {Lf : NNReal}
variable (hf : is_l_smooth_on f Set.univ Lf)
variable {x : ℕ → E} {L : ℕ → PosReal} {xDagger : ℕ → E}
variable (hstep :
  ∀ k : ℕ,
    x (k + 1) =
      x k -
        (‖fderiv ℝ f (x k)‖_* / (L k : ℝ)) • xDagger k)
variable (hDagger :
  ∀ k : ℕ,
    xDagger k ∈ Λ[fderiv ℝ f (x k)])

private abbrev backtracking_B4_sufficient_decrease_coeff
    (Lf : NNReal) (s : PosReal)
    (γ : ProximalGradientBacktrackingDecreaseFraction)
    (η : ProximalGradientBacktrackingGrowthFactor) : ℝ :=
  (γ : ℝ) / max (s : ℝ) (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ))))

-- Proof sketch: rewrite `L k` as the constant parameter `barL`, apply Lemma 10.65 at the current
-- iterate with the chosen counterpart `xDagger k`, and then unfold the constant-case coefficient.
/-- Lemma 10.66 (1), constant-stepsize branch: if every `L_k = barL` for some
`barL ∈ (L_f / 2, ∞)`, then each non-Euclidean gradient step satisfies the sufficient-decrease
estimate with coefficient `((barL : ℝ) - L_f / 2) / barL^2`. -/
theorem non_euclidean_gradient_constant_stepsize_sufficient_decrease
    (hf : is_l_smooth_on f Set.univ Lf)
    (hstep :
      ∀ k : ℕ,
        x (k + 1) =
          x k -
            (‖fderiv ℝ f (x k)‖_* / (L k : ℝ)) • xDagger k)
    (hDagger :
      ∀ k : ℕ,
        xDagger k ∈ Λ[fderiv ℝ f (x k)])
    (barL : ProximalGradientConstantStepsizeParameter Lf)
    (hL : L = Function.const ℕ (barL : PosReal))
    (k : ℕ) :
    f (x k) - f (x (k + 1)) ≥
      (((barL : ℝ) - (Lf : ℝ) / 2) / ((barL : ℝ) ^ (2 : ℕ))) *
        ‖fderiv ℝ f (x k)‖_* ^ (2 : ℕ) := by
  have hstepk :
      x (k + 1) =
        x k - (‖fderiv ℝ f (x k)‖_* / ((barL : PosReal) : ℝ)) • xDagger k := by
    -- The constant-rule hypothesis identifies the current curvature with `barL`.
    simpa [hL] using hstep k
  have hdecrease :
      f (x (k + 1)) ≤
        f (x k) -
          (((barL : ℝ) - (Lf : ℝ) / 2) / ((barL : ℝ) ^ (2 : ℕ))) *
            ‖fderiv ℝ f (x k)‖_* ^ (2 : ℕ) := by
    -- Lemma 10.65 applies directly at the current iterate with the chosen counterpart.
    simpa [hstepk] using
      non_euclidean_gradient_method_sufficient_decrease
        hf (x k) (barL : PosReal) (xDagger k) (hDagger k)
  -- Rearranging the one-step upper bound gives the desired decrease estimate.
  linarith

-- Proof sketch: use the accepted-trial inequality from
-- `uses_non_euclidean_backtracking_B4_rule_accepts` and bound the accepted trial curvature from
-- above by
-- `non_euclidean_backtracking_B4_stepsize_le_max_initial_or_smoothness_threshold`; this yields
-- the displayed uniform B4 coefficient.
/-- Lemma 10.66 (2), B4-backtracking branch: if the curvature estimates are chosen by backtracking
procedure B4 with parameters `(s, γ, η)`, then each step satisfies the sufficient-decrease
estimate with coefficient `γ / max {s, η L_f / (2 (1 - γ))}`. -/
theorem non_euclidean_gradient_backtracking_B4_sufficient_decrease
    (hf : is_l_smooth_on f Set.univ Lf)
    (hstep :
      ∀ k : ℕ,
        x (k + 1) =
          x k -
            (‖fderiv ℝ f (x k)‖_* / (L k : ℝ)) • xDagger k)
    (s : PosReal) (γ : ProximalGradientBacktrackingDecreaseFraction)
    (η : ProximalGradientBacktrackingGrowthFactor)
    (hB4 : uses_non_euclidean_backtracking_B4_rule f x L xDagger s γ η)
    (k : ℕ) :
    f (x k) - f (x (k + 1)) ≥
      backtracking_B4_sufficient_decrease_coeff Lf s γ η *
        ‖fderiv ℝ f (x k)‖_* ^ (2 : ℕ) := by
  rcases hB4 k with ⟨i, hi, hLk⟩
  let residual : ℝ := ‖fderiv ℝ f (x k)‖_* ^ (2 : ℕ)
  have hstepk :
      x (k + 1) =
        x k -
          (‖fderiv ℝ f (x k)‖_* /
            (proximal_gradient_backtracking_trial_stepsize s η i : ℝ)) • xDagger k := by
    -- Rewriting the update with the accepted trial identifies the concrete B4 step.
    simpa [hLk] using hstep k
  have haccept :
      (γ : ℝ) / (L k : ℝ) * residual ≤ f (x k) - f (x (k + 1)) := by
    -- The accepted B4 trial gives the raw sufficient-decrease inequality at iteration `k`.
    simpa [non_euclidean_gradient_backtracking_B4_accepts, hLk, hstepk, residual] using
      is_backtracking_procedure_B4_index_accepts hi
  have hL_upper :
      (L k : ℝ) ≤
        max (s : ℝ) (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ)))) := by
    -- The accepted trial curvature is uniformly bounded by the source backtracking threshold.
    simpa [hLk] using
      non_euclidean_backtracking_B4_stepsize_le_max_initial_or_smoothness_threshold
        hf s γ η hi
  have hγ_nonneg : 0 ≤ (γ : ℝ) := le_of_lt γ.1.2
  have hmax_pos :
      0 < max (s : ℝ) (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ)))) := by
    exact lt_of_lt_of_le s.2 (le_max_left (s : ℝ)
      (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ)))))
  have hcoeff :
      backtracking_B4_sufficient_decrease_coeff Lf s γ η ≤ (γ : ℝ) / (L k : ℝ) := by
    -- Replacing `L_k` by its uniform upper bound yields the branch coefficient.
    dsimp [backtracking_B4_sufficient_decrease_coeff]
    have hinv :
        (max (s : ℝ) (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ)))))⁻¹ ≤
          ((L k : ℝ))⁻¹ := by
      exact (inv_le_inv₀ hmax_pos (L k).2).2 hL_upper
    have hmul :
        (γ : ℝ) * (max (s : ℝ) (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ)))))⁻¹ ≤
          (γ : ℝ) * ((L k : ℝ))⁻¹ := by
      exact mul_le_mul_of_nonneg_left hinv hγ_nonneg
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul
  have hresidual_nonneg : 0 ≤ residual := by
    -- The squared dual norm is nonnegative.
    dsimp [residual]
    positivity
  have hscaled :
      backtracking_B4_sufficient_decrease_coeff Lf s γ η * residual ≤
        (γ : ℝ) / (L k : ℝ) * residual := by
    exact mul_le_mul_of_nonneg_right hcoeff hresidual_nonneg
  -- Chain the coefficient comparison with the accepted-trial decrease estimate.
  exact le_trans hscaled haccept

-- Proof sketch: compare the exact minimizing stepsize with the candidate `1 / L_f`, use the
-- global `L_f`-smoothness estimate from Lemma 10.65 at that comparison step, and conclude by
-- minimality of the chosen exact-line-search parameter.
/-- Lemma 10.66 (3), exact-line-search branch: if `L_f > 0` and every reciprocal stepsize
`1 / L_k` minimizes the descent objective along the non-Euclidean ray at iteration `k`, then
each step satisfies the sufficient-decrease estimate with coefficient `1 / (2 L_f)`. -/
theorem non_euclidean_gradient_exact_line_search_sufficient_decrease
    (hf : is_l_smooth_on f Set.univ Lf)
    (hstep :
      ∀ k : ℕ,
        x (k + 1) =
          x k -
            (‖fderiv ℝ f (x k)‖_* / (L k : ℝ)) • xDagger k)
    (hDagger :
      ∀ k : ℕ,
        xDagger k ∈ Λ[fderiv ℝ f (x k)])
    (hLf : 0 < (Lf : ℝ))
    (hsearch : uses_non_euclidean_exact_line_search_stepsize_rule f x L xDagger)
    (k : ℕ) :
    f (x k) - f (x (k + 1)) ≥
      (1 / (2 * (Lf : ℝ))) * ‖fderiv ℝ f (x k)‖_* ^ (2 : ℕ) := by
  let residual : ℝ := ‖fderiv ℝ f (x k)‖_* ^ (2 : ℕ)
  have hsearchk :
      (1 / (L k : ℝ)) ∈
        non_euclidean_exact_line_search_stepsizes f (x k) (xDagger k) :=
    hsearch k
  have hmin :
      IsMinOn
        (fun t ↦ f (x k - (t * ‖fderiv ℝ f (x k)‖_*) • xDagger k))
        (Set.Ici (0 : ℝ))
        (1 / (L k : ℝ)) := by
    -- The exact-line-search rule records minimality over the nonnegative ray.
    exact (mem_non_euclidean_exact_line_search_stepsizes_iff.mp hsearchk).2
  rw [isMinOn_iff] at hmin
  have hcandidate_nonneg : 0 ≤ 1 / (Lf : ℝ) := by
    exact one_div_nonneg.mpr hLf.le
  have hcompare :
      f (x k - ((1 / (L k : ℝ)) * ‖fderiv ℝ f (x k)‖_*) • xDagger k) ≤
        f (x k - ((1 / (Lf : ℝ)) * ‖fderiv ℝ f (x k)‖_*) • xDagger k) := by
    -- Minimality lets us compare the chosen step with the feasible candidate `1 / L_f`.
    exact hmin (1 / (Lf : ℝ)) (by simpa using hcandidate_nonneg)
  have hstepk :
      x (k + 1) =
        x k - ((1 / (L k : ℝ)) * ‖fderiv ℝ f (x k)‖_*) • xDagger k := by
    -- Rewriting the update factor `‖f'(x^k)‖_* / L_k` as `(1 / L_k) ‖f'(x^k)‖_*` matches the
    -- exact-line-search ray parameterization.
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hstep k
  have hcompare_step :
      f (x (k + 1)) ≤
        f (x k - ((1 / (Lf : ℝ)) * ‖fderiv ℝ f (x k)‖_*) • xDagger k) := by
    -- Rewriting the minimizing parameter `1 / L_k` recovers the actual iterate `x^(k+1)`.
    simpa [hstepk] using hcompare
  let LfPos : PosReal := ⟨(Lf : ℝ), hLf⟩
  have hcandidate_decrease :
      f (x k - ((1 / (Lf : ℝ)) * ‖fderiv ℝ f (x k)‖_*) • xDagger k) ≤
        f (x k) - ((((Lf : ℝ) - (Lf : ℝ) / 2) / (Lf : ℝ) ^ (2 : ℕ)) * residual) := by
    -- Lemma 10.65 at the comparison curvature `L = L_f` bounds the candidate objective value.
    simpa [LfPos, residual, div_eq_mul_inv,
      mul_assoc, mul_left_comm, mul_comm] using
      non_euclidean_gradient_method_sufficient_decrease
        hf (x k) LfPos (xDagger k) (hDagger k)
  have hcoeff :
      (((Lf : ℝ) - (Lf : ℝ) / 2) / (Lf : ℝ) ^ (2 : ℕ)) =
        1 / (2 * (Lf : ℝ)) := by
    have hLf_ne : (Lf : ℝ) ≠ 0 := ne_of_gt hLf
    field_simp [pow_two, hLf_ne]
    ring
  have hdecrease :
      f (x (k + 1)) ≤ f (x k) - (1 / (2 * (Lf : ℝ))) * residual := by
    -- Combine the line-search comparison with the candidate decrease bound.
    rw [← hcoeff]
    exact le_trans hcompare_step hcandidate_decrease
  -- Rearranging finishes the exact-line-search branch.
  linarith

-- Proof sketch: use Lemma 10.65 in the constant-stepsize branch, applied to the trial point
-- `x k - (‖f'(x^k)‖_* / L_k) • xDagger^k`. In the B4 branch, combine the accepted-trial
-- inequality from the `accepts` field of the B4
-- backtracking-index owner with the preceding uniform upper bound on `L_k`. In the
-- exact-line-search branch, compare the minimizing step size with `1 / L_f` and use
-- `L_f`-smoothness to bound the objective value of that comparison step; this branch keeps
-- `0 < L_f` as the branch hypothesis and states the textbook coefficient directly as
-- `M = 1 / (2 L_f)`.
/-- Lemma 10.66 (4): if `f` is globally `L_f`-smooth and the iterates satisfy
`x^(k+1) = x^k - (‖f'(x^k)‖_* / L_k) • xDagger^k`,
with `xDagger^k ∈ Λ_{f'(x^k)}`, and if the stepsizes are chosen either by a constant rule
`barL ∈ (L_f / 2, ∞)`, by backtracking procedure B4 with parameters `(s, γ, η)`, or by exact
line search with `0 < L_f`, then for every `k ≥ 0`,
`f(x^k) - f(x^(k+1)) ≥ M ‖f'(x^k)‖_*^2`, where
`M = ((barL : ℝ) - L_f / 2) / barL^2` in the constant case,
`M = γ / max {s, η L_f / (2 (1 - γ))}` in the B4 case, and
`M = 1 / (2 L_f)` in the exact-line-search case. -/
theorem non_euclidean_gradient_sufficient_decrease_by_stepsize_rule
    {f : E → ℝ} {Lf : NNReal} (hf : is_l_smooth_on f Set.univ Lf)
    (x : ℕ → E) (L : ℕ → PosReal) (xDagger : ℕ → E)
    (hstep :
      ∀ k : ℕ,
        x (k + 1) =
          x k -
            (‖fderiv ℝ f (x k)‖_* / (L k : ℝ)) • xDagger k)
    (hDagger :
      ∀ k : ℕ,
        xDagger k ∈ Λ[fderiv ℝ f (x k)])
    {M : ℝ}
    (hstepsize : uses_non_euclidean_gradient_stepsize_rule f Lf x L xDagger M)
    (k : ℕ) :
    f (x k) - f (x (k + 1)) ≥
      M * ‖fderiv ℝ f (x k)‖_* ^ (2 : ℕ) := by
  rcases hstepsize with hconst | hrest
  · rcases hconst with ⟨barL, hL, rfl⟩
    -- The constant-stepsize branch is exactly the specialized one-step estimate.
    simpa using
      non_euclidean_gradient_constant_stepsize_sufficient_decrease
        hf hstep hDagger barL hL k
  · rcases hrest with hB4 | hexact
    · rcases hB4 with ⟨s, γ, η, hrule, rfl⟩
      -- The B4 branch uses acceptance plus the uniform upper bound on the chosen trial.
      simpa [backtracking_B4_sufficient_decrease_coeff] using
        non_euclidean_gradient_backtracking_B4_sufficient_decrease
          hf hstep s γ η hrule k
    · rcases hexact with ⟨hLf, hsearch, rfl⟩
      -- The exact-line-search branch compares the minimizing step with the candidate `1 / L_f`.
      simpa using
        non_euclidean_gradient_exact_line_search_sufficient_decrease
          hf hstep hDagger hLf hsearch k

end SufficientDecreaseRule

end
