/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_11
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Lemma_10_4
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Remark_10_13
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

/- Lemma 10.14 is `source-facing` in the Chapter 10 proximal-gradient API.

Domain sampling:
- `prox_grad_sufficient_decrease` from Lemma 10.4 is the upstream one-step descent theorem, and
  it already exposes the primitive regularity hypotheses actually used here;
- `backtracking_procedure_B1_stepsize_le_max_initial_or_smoothness_threshold` from Remark 10.13
  is the upstream B1 stepsize bound under that same primitive hypothesis block;
- `is_proximal_gradient_trajectory` from Algorithm 10.1 is the owner for the iterate sequence
  `x^k`;
- `gradient_mapping` is the Chapter 10 owner for the residual `G_L`;
- `uses_proximal_gradient_backtracking_B1_rule` is the source-facing owner of the B1 strategy.

Triage:
- `source-facing`: the two sufficient-decrease statements, split by the textbook's constant and B1
  stepsize cases;
- `core/canonical`: the trajectory owner, `gradient_mapping`, and the primitive regularity
  hypotheses already isolated by Lemma 10.4 and Remark 10.13;
- `bridge/view`: no extra wrapper is introduced, because the admissible strategy remains the
  theorem-specific constant-step or B1 input.

The prox-grad residual therefore stays on the canonical owner `gradient_mapping`, while the public
regularity interface is reduced to the primitive smoothness/closedness/convexity/domain data that
the theorem actually uses. The sufficient-decrease coefficients are theorem-local arithmetic data,
so the source-facing API keeps them inline instead of exporting separate wrapper names. -/

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

variable {f g : E → EReal} {Lf : NNReal}
variable [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
variable [Fact (is_convex_function g)]
variable
    (hf_ne_bot : ∀ y, f y ≠ ⊥)
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f))
    (hf_toReal_smooth_on_interior_effective_domain :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)

local notation "F" => composite_model_objective f g

set_option quotPrecheck false in
local notation:max "G[" L "]" =>
  G[L, f, g]

-- Proof sketch: rewrite the set-valued trajectory update at step `k` using the singleton
-- description of the prox-gradient operator, so the realized successor `x^(k+1)` becomes the
-- point-valued operator `T[L_k]` applied to the current iterate.
/-- Helper for Lemma 10.14: the successor of a proximal-gradient trajectory is the prox-gradient
operator applied to the current iterate. -/
lemma proximal_gradient_trajectory_succ_eq_prox_grad_operator
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L) (k : ℕ) :
    x (k + 1) = T[L k, f, g] (proximal_gradient_trajectory_iterate htraj k) := by
  -- The trajectory step lies in a singleton prox-gradient step, so it equals the chosen point.
  have hstep :
      x (k + 1) ∈
        proximal_gradient_step f g (proximal_gradient_trajectory_iterate htraj k : E) (L k) := by
    simpa [proximal_gradient_trajectory_iterate] using
      (is_proximal_gradient_trajectory_step htraj k).2
  rw [prox_grad_operator_eq_singleton f g (L k)
    (proximal_gradient_trajectory_iterate htraj k)] at hstep
  simpa using hstep

-- Proof sketch: unpack the B1 rule at iteration `k`, unfold the acceptance predicate at the
-- accepted trial stepsize, identify the induced interior-domain point with the canonical
-- trajectory iterate `x^k`, and rewrite the realized update as `x^(k+1)`.
/-- Helper for Lemma 10.14: the B1 acceptance test at iteration `k` gives the accepted
sufficient-decrease inequality for the realized iterate and chosen stepsize. -/
lemma backtracking_B1_acceptance_ineq_at_iterate
    (s : PosReal) (γ : ProximalGradientBacktrackingDecreaseFraction)
    (η : ProximalGradientBacktrackingGrowthFactor)
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hbacktrack :
      uses_proximal_gradient_backtracking_B1_rule
        f g
        hg_effective_domain_subset_interior_f_effective_domain
        x L htraj s γ η)
    (k : ℕ) :
    ((((γ : ℝ) / (L k : ℝ)) *
        ‖G[L k] (proximal_gradient_trajectory_iterate htraj k)‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
      F (x k) - F (x (k + 1)) := by
  rcases hbacktrack k with ⟨hxk, i, hi, hLk⟩
  have haccepts := is_backtracking_procedure_B1_index_accepts hi
  let xkEff : effective_domain g :=
    ⟨(proximal_gradient_trajectory_iterate htraj k : E), hxk⟩
  have hxInterior :
      (⟨(xkEff : E),
        hg_effective_domain_subset_interior_f_effective_domain xkEff.property⟩ :
        interior (effective_domain f)) =
        proximal_gradient_trajectory_iterate htraj k := by
    apply Subtype.ext
    rfl
  -- Unfold the accepted B1 decrease test and identify its point data with the trajectory iterate.
  simpa [xkEff, proximal_gradient_backtracking_accepts, hLk, hxInterior,
    proximal_gradient_trajectory_succ_eq_prox_grad_operator htraj k] using haccepts

-- Proof sketch: compare the coefficients using `L_k ≤ max {s, η L_f / (2 (1 - γ))}` and compare
-- the residuals using the monotonicity `‖G_s(x^k)‖ ≤ ‖G_Lk(x^k)‖` from Theorem 10.9. Multiplying
-- the two monotone factors yields the displayed real inequality.
/-- Helper for Lemma 10.14: stepsize bounds convert the accepted B1 decrease coefficient at
`L_k` into the displayed coefficient at the canonical residual `G[s]`. -/
lemma backtracking_residual_bound_from_stepsize_bounds
    (s : PosReal) (γ : ProximalGradientBacktrackingDecreaseFraction)
    (η : ProximalGradientBacktrackingGrowthFactor)
    (xk : interior (effective_domain f)) (Lk : PosReal)
    (hs_le_Lk : (s : ℝ) ≤ (Lk : ℝ))
    (hLk_le_max :
      (Lk : ℝ) ≤ max (s : ℝ) (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ))))) :
    (((γ : ℝ) / max (s : ℝ) (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ)))) *
        ‖G[s] xk‖ ^ (2 : ℕ) : ℝ)) ≤
      (((γ : ℝ) / (Lk : ℝ)) * ‖G[Lk] xk‖ ^ (2 : ℕ) : ℝ) := by
  let M : ℝ := max (s : ℝ) (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ))))
  have hnorm :
      ‖G[s] xk‖ ≤ ‖G[Lk] xk‖ :=
    gradient_mapping_norm_monotone f g xk hs_le_Lk
  have hsq :
      ‖G[s] xk‖ ^ (2 : ℕ) ≤ ‖G[Lk] xk‖ ^ (2 : ℕ) := by
    nlinarith [hnorm, norm_nonneg (G[s] xk), norm_nonneg (G[Lk] xk)]
  have hγ_nonneg : 0 ≤ (γ : ℝ) := le_of_lt γ.1.2
  have hLk_pos : 0 < (Lk : ℝ) := Lk.2
  have hM_pos : 0 < M := by
    dsimp [M]
    exact lt_of_lt_of_le s.2 (le_max_left _ _)
  have hcoeff :
      (γ : ℝ) / M ≤ (γ : ℝ) / (Lk : ℝ) := by
    -- The coefficient grows when the positive denominator decreases from `M` to `L_k`.
    field_simp [M, hM_pos.ne', hLk_pos.ne']
    nlinarith
  have hsq_nonneg : 0 ≤ ‖G[s] xk‖ ^ (2 : ℕ) := by
    nlinarith [norm_nonneg (G[s] xk)]
  have hcoeff_nonneg : 0 ≤ (γ : ℝ) / (Lk : ℝ) := by
    exact div_nonneg hγ_nonneg (le_of_lt hLk_pos)
  have hstep1 :
      ((γ : ℝ) / M) * ‖G[s] xk‖ ^ (2 : ℕ) ≤
        ((γ : ℝ) / (Lk : ℝ)) * ‖G[s] xk‖ ^ (2 : ℕ) := by
    exact mul_le_mul_of_nonneg_right hcoeff hsq_nonneg
  have hstep2 :
      ((γ : ℝ) / (Lk : ℝ)) * ‖G[s] xk‖ ^ (2 : ℕ) ≤
        ((γ : ℝ) / (Lk : ℝ)) * ‖G[Lk] xk‖ ^ (2 : ℕ) := by
    exact mul_le_mul_of_nonneg_left hsq hcoeff_nonneg
  exact le_trans (by simpa [M] using hstep1) hstep2

include hf_ne_bot hf_effective_domain_convex
  hg_effective_domain_subset_interior_f_effective_domain
  hf_toReal_smooth_on_interior_effective_domain

-- Proof sketch: specialize Lemma 10.4 at the canonical iterate `x^k` of the trajectory. This
-- packages the primitive Assumption 10.1 hypotheses into a theorem-local API that the two source
-- facing sufficient-decrease statements can reuse directly.
/-- Helper for Lemma 10.14: Lemma 10.4 applied at the `k`-th proximal-gradient trajectory
iterate. -/
lemma prox_grad_sufficient_decrease_at_trajectory_iterate
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L) (k : ℕ) :
    F ((proximal_gradient_trajectory_iterate htraj k : E)) -
        F (T[L k, f, g] (proximal_gradient_trajectory_iterate htraj k)) ≥
      (((((L k : ℝ) - (Lf : ℝ) / 2) / ((L k : ℝ) ^ (2 : ℕ))) *
          ‖G[L k] (proximal_gradient_trajectory_iterate htraj k)‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  -- Specialize Lemma 10.4 at the realized interior-domain iterate `x^k`.
  simpa using
    prox_grad_sufficient_decrease
      f g Lf hf_ne_bot hf_effective_domain_convex
      hg_effective_domain_subset_interior_f_effective_domain
      hf_toReal_smooth_on_interior_effective_domain
      (L k) (proximal_gradient_trajectory_iterate htraj k)

-- Proof sketch: unpack the B1 owner at iteration `k` and then apply Remark 10.13's uniform
-- stepsize bound to the accepted trial `s η^i = L_k`.
/-- Helper for Lemma 10.14: the B1 stepsize chosen at iteration `k` is bounded by
`max {s, η L_f / (2 (1 - γ))}`. -/
lemma backtracking_B1_stepsize_le_max_at_iterate
    (s : PosReal) (γ : ProximalGradientBacktrackingDecreaseFraction)
    (η : ProximalGradientBacktrackingGrowthFactor)
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hbacktrack :
      uses_proximal_gradient_backtracking_B1_rule
        f g
        hg_effective_domain_subset_interior_f_effective_domain
        x L htraj s γ η)
    (k : ℕ) :
    (L k : ℝ) ≤ max (s : ℝ) (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ)))) := by
  rcases hbacktrack k with ⟨hxk, i, hi, hLk⟩
  let xkEff : effective_domain g :=
    ⟨(proximal_gradient_trajectory_iterate htraj k : E), hxk⟩
  -- Apply Remark 10.13 to the accepted backtracking index produced at iteration `k`.
  have hbound :
      (proximal_gradient_backtracking_trial_stepsize s η i : ℝ) ≤
        max (s : ℝ) (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ)))) :=
    backtracking_procedure_B1_stepsize_le_max_initial_or_smoothness_threshold
      f g Lf
      hg_effective_domain_subset_interior_f_effective_domain
      s γ η xkEff
      hf_ne_bot hf_effective_domain_convex
      hf_toReal_smooth_on_interior_effective_domain
      hi
  -- Rewrite the accepted trial stepsize back to the trajectory stepsize `L_k`.
  simpa [xkEff, hLk] using hbound

-- Proof sketch: apply `prox_grad_sufficient_decrease` to the iterate `x^k` with
-- `L = barL` under the primitive descent hypotheses from Lemma 10.4. Then rewrite the
-- prox-grad step `T_barL(x^k)` as `x^(k+1)` by combining
-- `is_proximal_gradient_trajectory_step` with `prox_grad_operator_eq_singleton`, and keep the
-- residual term in the canonical Chapter 10 form `‖G[barL] x^k‖²`.
/-- Lemma 10.14 (1): under the one-step descent hypotheses of Lemma 10.4, if the iterates `x^k`
are generated by the proximal gradient method with the constant stepsize
`barL ∈ (L_f / 2, ∞)`, then
`F(x^k) - F(x^(k+1)) ≥ M ‖G_barL(x^k)‖^2` with
`M = ((barL : ℝ) - L_f / 2) / barL^2`. -/
theorem proximal_gradient_constant_stepsize_sufficient_decrease
    (barL : ProximalGradientConstantStepsizeParameter Lf) (x : ℕ → E)
    (htraj : is_proximal_gradient_trajectory f g x
      (Function.const ℕ barL))
    (k : ℕ) :
    F (x k) - F (x (k + 1)) ≥
      (((((barL : ℝ) - (Lf : ℝ) / 2) / ((barL : ℝ) ^ (2 : ℕ))) *
          ‖G[barL] (proximal_gradient_trajectory_iterate htraj k)‖ ^ (2 : ℕ) : ℝ) : EReal) :=
by
  let xk := proximal_gradient_trajectory_iterate htraj k
  -- Specialize the packaged one-step descent theorem at the realized iterate `x^k`.
  have hdescent :
      F (xk : E) - F (T[barL, f, g] xk) ≥
        (((((barL : ℝ) - (Lf : ℝ) / 2) / ((barL : ℝ) ^ (2 : ℕ))) *
            ‖G[barL] xk‖ ^ (2 : ℕ) : ℝ) : EReal) :=
    by
      simpa [xk] using
        prox_grad_sufficient_decrease
          f g Lf hf_ne_bot hf_effective_domain_convex
          hg_effective_domain_subset_interior_f_effective_domain
          hf_toReal_smooth_on_interior_effective_domain
          barL (proximal_gradient_trajectory_iterate htraj k)
  -- Rewrite the prox-gradient update as the realized successor `x^(k+1)`.
  simpa [xk, proximal_gradient_trajectory_succ_eq_prox_grad_operator
    htraj k] using hdescent

-- Proof sketch: for the accepted B1 stepsize `L_k`, use the `accepts` field of the
-- backtracking-index owner to get the sufficient-decrease estimate
-- `F(x^k) - F(x^(k+1)) ≥ (γ / L_k) ‖G_{L_k}(x^k)‖^2`. Use
-- `backtracking_procedure_B1_stepsize_le_max_initial_or_smoothness_threshold` to bound `L_k`
-- from above, and apply `gradient_mapping_norm_monotone` with `s ≤ L_k` to rewrite the final
-- bound in terms of the canonical residual `‖G[s] x^k‖²`.
/-- Lemma 10.14 (2): under the primitive hypotheses used by Lemma 10.4 and Remark 10.13, if the
iterates `x^k` are generated by the proximal gradient method with a stepsize selected by
backtracking procedure B1 with parameters `(s, γ, η)`, then
`F(x^k) - F(x^(k+1)) ≥ M ‖G_s(x^k)‖^2` with
`M = γ / max {s, η L_f / (2 (1 - γ))}`. -/
theorem proximal_gradient_backtracking_B1_sufficient_decrease
    (s : PosReal) (γ : ProximalGradientBacktrackingDecreaseFraction)
    (η : ProximalGradientBacktrackingGrowthFactor)
    (x : ℕ → E) (L : ℕ → PosReal)
    (htraj : is_proximal_gradient_trajectory f g x L)
    (hbacktrack :
      uses_proximal_gradient_backtracking_B1_rule
        f g
        hg_effective_domain_subset_interior_f_effective_domain
        x L htraj s γ η)
    (k : ℕ) :
    F (x k) - F (x (k + 1)) ≥
      ((((γ : ℝ) / max (s : ℝ) (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ))))) *
          ‖G[s] (proximal_gradient_trajectory_iterate htraj k)‖ ^ (2 : ℕ) : ℝ) : EReal) :=
by
  let xk := proximal_gradient_trajectory_iterate htraj k
  rcases hbacktrack k with ⟨hxk, i, hi, hLk⟩
  let xkEff : effective_domain g := ⟨(xk : E), hxk⟩
  -- The accepted B1 index gives the sufficient-decrease inequality at the realized iterate.
  have haccept :
      ((((γ : ℝ) / (L k : ℝ)) * ‖G[L k] xk‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        F (x k) - F (x (k + 1)) :=
    backtracking_B1_acceptance_ineq_at_iterate
      hg_effective_domain_subset_interior_f_effective_domain
      s γ η htraj hbacktrack k
  have hLk_le_max :
      (L k : ℝ) ≤ max (s : ℝ) (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ)))) := by
    -- Remark 10.13 bounds every accepted B1 stepsize by the stated uniform maximum.
    exact backtracking_B1_stepsize_le_max_at_iterate
      hf_ne_bot hf_effective_domain_convex
      hg_effective_domain_subset_interior_f_effective_domain
      hf_toReal_smooth_on_interior_effective_domain
      s γ η htraj hbacktrack k
  have hs_le_Lk : (s : ℝ) ≤ (L k : ℝ) := by
    -- Every accepted trial has the form `s * η^i`, so it is at least the initial trial `s`.
    rw [hLk, proximal_gradient_backtracking_trial_stepsize_coe]
    have hηge1 : (1 : ℝ) ≤ (η : ℝ) := le_of_lt η.2
    have hs_nonneg : 0 ≤ (s : ℝ) := le_of_lt s.2
    exact le_mul_of_one_le_right hs_nonneg (one_le_pow₀ hηge1)
  have hresidual_real :
      (((γ : ℝ) / max (s : ℝ) (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ)))) *
          ‖G[s] xk‖ ^ (2 : ℕ) : ℝ)) ≤
        (((γ : ℝ) / (L k : ℝ)) * ‖G[L k] xk‖ ^ (2 : ℕ) : ℝ) :=
    backtracking_residual_bound_from_stepsize_bounds
      s γ η xk (L k) hs_le_Lk hLk_le_max
  have hresidual :
      ((((γ : ℝ) / max (s : ℝ) (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ)))) *
          ‖G[s] xk‖ ^ (2 : ℕ) : ℝ) : EReal)) ≤
        ((((γ : ℝ) / (L k : ℝ)) * ‖G[L k] xk‖ ^ (2 : ℕ) : ℝ) : EReal) := by
    exact_mod_cast hresidual_real
  -- Chain the coefficient/residual comparison with the accepted sufficient-decrease estimate.
  exact le_trans hresidual haccept

end

end
