/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_8
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_17
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_1
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_5
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Corollary_10_8
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Lemma_10_10
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Lemma_10_14
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

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
local notation:max "G[" L "]" => G[L, f, g]

/- Theorem 10.15 is `source-facing` in the Chapter 10 proximal-gradient API.

Domain sampling identifies the relevant owner abstractions already present in the chapter:
- `Lemma_10_14`, which already isolates the primitive regularity and domain-compatibility data
  actually used by the sufficient-decrease arguments here;
- `is_proximal_gradient_trajectory` from Algorithm 10.1 for the iterate sequence `x^k`;
- `gradient_mapping` from Definition 10.5 and `best_achieved_function_value` from
  Definition 8.8 for the canonical residual observable `x ↦ ‖G_d(x)‖` and its prefix minimum;
- `Function.const` applied to an admissible
  `ProximalGradientConstantStepsizeParameter` from Definition 10.11 for the constant rule;
- `uses_proximal_gradient_backtracking_B1_rule` from Algorithm 10.2 for the B1 rule;
- `IsGLB` for the lower-bound data needed only in clauses (3)-(5).

Triage:
- `source-facing`: Theorem 10.15 itself, whose public statements keep the textbook constant-step
  and B1 cases.
- `core/canonical`: the primitive regularity hypotheses already exposed by Lemma 10.14, together
  with the trajectory, gradient-mapping, running-minimum, constant-map, B1-rule, and `IsGLB`
  owners.
- `bridge/view`: no extra wrapper is introduced; the admissible-rule disjunction and the
  case-dependent coefficients remain theorem-local data. -/

section SufficientDecreaseRule

variable {x : ℕ → E} {L : ℕ → PosReal}
variable (htraj : is_proximal_gradient_trajectory f g x L)
variable (hrule :
  (∃ barL : ProximalGradientConstantStepsizeParameter Lf,
      L = Function.const ℕ (barL : PosReal)) ∨
    ∃ s : PosReal, ∃ γ : ProximalGradientBacktrackingDecreaseFraction,
      ∃ η : ProximalGradientBacktrackingGrowthFactor,
        uses_proximal_gradient_backtracking_B1_rule
          f g hg_effective_domain_subset_interior_f_effective_domain x L htraj s γ η)

include hf_ne_bot hf_effective_domain_convex
  hg_effective_domain_subset_interior_f_effective_domain
  hf_toReal_smooth_on_interior_effective_domain htraj hrule

omit hrule in
/-- Helper for Theorem 10.15: every positive-index proximal-gradient iterate lies in
`effective_domain g` because it is realized by the prox-gradient operator. -/
lemma proximal_gradient_positive_iterate_mem_effective_domain_g
    (k : ℕ) :
    x (k + 1) ∈ effective_domain g := by
  -- Rewrite the realized successor to the prox-gradient operator output and reuse the Chapter 10
  -- domain-membership lemma for that operator.
  rw [proximal_gradient_trajectory_succ_eq_prox_grad_operator (f := f) (g := g) htraj k]
  exact
    prox_grad_operator_mem_effective_domain_g
      (f := f) (g := g) (L := L k) (x := proximal_gradient_trajectory_iterate htraj k)

omit hf_effective_domain_convex hf_toReal_smooth_on_interior_effective_domain htraj hrule in
/-- Helper for Theorem 10.15: on `effective_domain g`, the composite objective is a finite real
sum of the finite `f`- and `g`-values. -/
lemma proximal_gradient_objective_eq_real_of_mem_effective_domain_g
    {xPoint : E} (hxPoint : xPoint ∈ effective_domain g) :
    F xPoint = ((((f xPoint).toReal + (g xPoint).toReal : ℝ)) : EReal) := by
  have hfxPoint : xPoint ∈ effective_domain f := by
    exact interior_subset (hg_effective_domain_subset_interior_f_effective_domain hxPoint)
  have hfx_val :
      f xPoint = ((((f xPoint).toReal : ℝ)) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hfxPoint).ne (hf_ne_bot xPoint)).symm
  have hgx_val :
      g xPoint = ((((g xPoint).toReal : ℝ)) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hxPoint).ne
        (‹IsProperExtendedRealFunction g›.ne_bot xPoint)).symm
  -- Once both summands are finite, the composite objective is just the real-valued sum cast to
  -- `EReal`.
  rw [composite_model_objective_apply, hfx_val, hgx_val]
  simp [EReal.coe_add]

omit hrule in
/-- Helper for Theorem 10.15: if the current iterate lies in `effective_domain g`, then the
one-step objective gap is an ordinary real difference cast to `EReal`. -/
lemma proximal_gradient_objective_gap_eq_coe_sub_toReal_of_mem_effective_domain_g
    (k : ℕ) (hxkg : x k ∈ effective_domain g) :
    F (x k) - F (x (k + 1)) =
      (((((F (x k)).toReal - (F (x (k + 1))).toReal : ℝ))) : EReal) := by
  have hxk1g :
      x (k + 1) ∈ effective_domain g :=
    proximal_gradient_positive_iterate_mem_effective_domain_g
      (f := f) (g := g)
      (hf_ne_bot := hf_ne_bot)
      (hf_effective_domain_convex := hf_effective_domain_convex)
      (hg_effective_domain_subset_interior_f_effective_domain :=
        hg_effective_domain_subset_interior_f_effective_domain)
      (hf_toReal_smooth_on_interior_effective_domain :=
        hf_toReal_smooth_on_interior_effective_domain)
      (htraj := htraj) k
  have hxk_val :
      F (x k) = ((((f (x k)).toReal + (g (x k)).toReal : ℝ)) : EReal) :=
    proximal_gradient_objective_eq_real_of_mem_effective_domain_g
      (f := f) (g := g)
      (hf_ne_bot := hf_ne_bot)
      (hg_effective_domain_subset_interior_f_effective_domain :=
        hg_effective_domain_subset_interior_f_effective_domain)
      hxkg
  have hxk1_val :
      F (x (k + 1)) = ((((f (x (k + 1))).toReal + (g (x (k + 1))).toReal : ℝ)) : EReal) :=
    proximal_gradient_objective_eq_real_of_mem_effective_domain_g
      (f := f) (g := g)
      (hf_ne_bot := hf_ne_bot)
      (hg_effective_domain_subset_interior_f_effective_domain :=
        hg_effective_domain_subset_interior_f_effective_domain)
      hxk1g
  have hxk_toReal :
      (F (x k)).toReal = (f (x k)).toReal + (g (x k)).toReal := by
    rw [hxk_val]
    simpa using EReal.toReal_coe ((f (x k)).toReal + (g (x k)).toReal)
  have hxk1_toReal :
      (F (x (k + 1))).toReal = (f (x (k + 1))).toReal + (g (x (k + 1))).toReal := by
    rw [hxk1_val]
    simpa using EReal.toReal_coe ((f (x (k + 1))).toReal + (g (x (k + 1))).toReal)
  -- Rewrite both objective values to finite real casts and then use the canonical `EReal` cast of
  -- a real difference.
  rw [hxk_toReal, hxk1_toReal, hxk_val, hxk1_val]
  simp [EReal.coe_sub]

omit hrule in
/-- Helper for Theorem 10.15: on a step whose current iterate lies in `effective_domain g`, any
nonnegative real lower bound on the one-step objective gap yields monotonicity. -/
lemma proximal_gradient_objective_step_le_of_mem_effective_domain_g
    {k : ℕ} (hxkg : x k ∈ effective_domain g) {gap : ℝ}
    (hgap :
      F (x k) - F (x (k + 1)) ≥ ((gap : ℝ) : EReal))
    (hgap_nonneg : 0 ≤ gap) :
    F (x (k + 1)) ≤ F (x k) := by
  have hxk_val :
      F (x k) = ((((f (x k)).toReal + (g (x k)).toReal : ℝ)) : EReal) :=
    proximal_gradient_objective_eq_real_of_mem_effective_domain_g
      (f := f) (g := g)
      (hf_ne_bot := hf_ne_bot)
      (hg_effective_domain_subset_interior_f_effective_domain :=
        hg_effective_domain_subset_interior_f_effective_domain)
      hxkg
  have hxk1g :
      x (k + 1) ∈ effective_domain g :=
    proximal_gradient_positive_iterate_mem_effective_domain_g
      (f := f) (g := g)
      (hf_ne_bot := hf_ne_bot)
      (hf_effective_domain_convex := hf_effective_domain_convex)
      (hg_effective_domain_subset_interior_f_effective_domain :=
        hg_effective_domain_subset_interior_f_effective_domain)
      (hf_toReal_smooth_on_interior_effective_domain :=
        hf_toReal_smooth_on_interior_effective_domain)
      (htraj := htraj) k
  have hxk1_val :
      F (x (k + 1)) = ((((f (x (k + 1))).toReal + (g (x (k + 1))).toReal : ℝ)) : EReal) :=
    proximal_gradient_objective_eq_real_of_mem_effective_domain_g
      (f := f) (g := g)
      (hf_ne_bot := hf_ne_bot)
      (hg_effective_domain_subset_interior_f_effective_domain :=
        hg_effective_domain_subset_interior_f_effective_domain)
      hxk1g
  have hgap_real :
      gap ≤
        ((f (x k)).toReal + (g (x k)).toReal) -
          ((f (x (k + 1))).toReal + (g (x (k + 1))).toReal) := by
    rw [hxk_val, hxk1_val] at hgap
    exact EReal.coe_le_coe_iff.mp (by simpa [EReal.coe_sub] using hgap)
  have hmono_real :
      (f (x (k + 1))).toReal + (g (x (k + 1))).toReal ≤
        (f (x k)).toReal + (g (x k)).toReal := by
    nlinarith
  -- Convert the real monotonicity back to the original `EReal` objective values.
  rw [hxk1_val, hxk_val]
  exact EReal.coe_le_coe_iff.mpr hmono_real

omit hrule in
/-- Helper for Theorem 10.15: on a step whose current iterate lies in `effective_domain g`, any
strictly positive real lower bound on the one-step objective gap yields strict decrease. -/
lemma proximal_gradient_objective_step_lt_of_mem_effective_domain_g
    {k : ℕ} (hxkg : x k ∈ effective_domain g) {gap : ℝ}
    (hgap :
      F (x k) - F (x (k + 1)) ≥ ((gap : ℝ) : EReal))
    (hgap_pos : 0 < gap) :
    F (x (k + 1)) < F (x k) := by
  have hxk_val :
      F (x k) = ((((f (x k)).toReal + (g (x k)).toReal : ℝ)) : EReal) :=
    proximal_gradient_objective_eq_real_of_mem_effective_domain_g
      (f := f) (g := g)
      (hf_ne_bot := hf_ne_bot)
      (hg_effective_domain_subset_interior_f_effective_domain :=
        hg_effective_domain_subset_interior_f_effective_domain)
      hxkg
  have hxk1g :
      x (k + 1) ∈ effective_domain g :=
    proximal_gradient_positive_iterate_mem_effective_domain_g
      (f := f) (g := g)
      (hf_ne_bot := hf_ne_bot)
      (hf_effective_domain_convex := hf_effective_domain_convex)
      (hg_effective_domain_subset_interior_f_effective_domain :=
        hg_effective_domain_subset_interior_f_effective_domain)
      (hf_toReal_smooth_on_interior_effective_domain :=
        hf_toReal_smooth_on_interior_effective_domain)
      (htraj := htraj) k
  have hxk1_val :
      F (x (k + 1)) = ((((f (x (k + 1))).toReal + (g (x (k + 1))).toReal : ℝ)) : EReal) :=
    proximal_gradient_objective_eq_real_of_mem_effective_domain_g
      (f := f) (g := g)
      (hf_ne_bot := hf_ne_bot)
      (hg_effective_domain_subset_interior_f_effective_domain :=
        hg_effective_domain_subset_interior_f_effective_domain)
      hxk1g
  have hgap_real :
      gap ≤
        ((f (x k)).toReal + (g (x k)).toReal) -
          ((f (x (k + 1))).toReal + (g (x (k + 1))).toReal) := by
    rw [hxk_val, hxk1_val] at hgap
    exact EReal.coe_le_coe_iff.mp (by simpa [EReal.coe_sub] using hgap)
  have hmono_real :
      (f (x (k + 1))).toReal + (g (x (k + 1))).toReal <
        (f (x k)).toReal + (g (x k)).toReal := by
    nlinarith
  -- Convert the strict real inequality back to the original `EReal` objective values.
  rw [hxk1_val, hxk_val]
  exact EReal.coe_lt_coe_iff.mpr hmono_real

-- Proof sketch: apply the constant-stepsize or B1 sufficient-decrease inequality from
-- Lemma 10.14 at each iteration `k`, and deduce `F(x^(k+1)) ≤ F(x^k)` from the nonnegativity of
-- the squared residual term.
/-- Theorem 10.15 (1): clause (a). Under the primitive regularity hypotheses isolated in
Lemma 10.14, if the proximal-gradient trajectory uses either a constant stepsize
`barL ∈ (L_f / 2, ∞)` or backtracking procedure B1, then the objective sequence `F(x^k)` is
nonincreasing. -/
theorem proximal_gradient_objective_values_antitone :
    Antitone (fun k ↦ F (x k)) := by
  -- Route correction: the earlier generic `EReal` telescope route is unnecessary for clause (a).
  -- The real-gap bridge is only needed on finite steps; the constant-step initial exception
  -- `x^0 ∉ effective_domain g` is handled separately by `F(x^0) = ⊤`.
  refine antitone_nat_of_succ_le ?_
  intro k
  rcases hrule with ⟨barL, hconst⟩ | ⟨s, γ, η, hB1⟩
  · by_cases hk0 : k = 0
    · subst hk0
      by_cases hx0g : x 0 ∈ effective_domain g
      · -- On the finite initial step, the sufficient-decrease inequality gives a nonnegative real
        -- objective gap.
        have hdecrease :=
          proximal_gradient_constant_stepsize_sufficient_decrease
            (f := f)
            (g := g)
            (Lf := Lf)
            (hf_ne_bot := hf_ne_bot)
            (hf_effective_domain_convex := hf_effective_domain_convex)
            (hg_effective_domain_subset_interior_f_effective_domain :=
              hg_effective_domain_subset_interior_f_effective_domain)
            (hf_toReal_smooth_on_interior_effective_domain :=
              hf_toReal_smooth_on_interior_effective_domain)
            barL x (by simpa [hconst] using htraj) 0
        have hcoeff_nonneg :
            0 ≤
              (((barL : ℝ) - (Lf : ℝ) / 2) / ((barL : ℝ) ^ (2 : ℕ))) *
                ‖G[barL] (proximal_gradient_trajectory_iterate
                  (by simpa [hconst] using htraj) 0)‖ ^ (2 : ℕ) := by
          have hnum_nonneg : 0 ≤ (barL : ℝ) - (Lf : ℝ) / 2 := by
            exact sub_nonneg.mpr barL.lower_bound.le
          have hden_nonneg : 0 ≤ (barL : ℝ) ^ (2 : ℕ) := by positivity
          exact mul_nonneg (div_nonneg hnum_nonneg hden_nonneg) (sq_nonneg _)
        exact
          proximal_gradient_objective_step_le_of_mem_effective_domain_g
            (f := f)
            (g := g)
            (Lf := Lf)
            (hf_ne_bot := hf_ne_bot)
            (hf_effective_domain_convex := hf_effective_domain_convex)
            (hg_effective_domain_subset_interior_f_effective_domain :=
              hg_effective_domain_subset_interior_f_effective_domain)
            (hf_toReal_smooth_on_interior_effective_domain :=
              hf_toReal_smooth_on_interior_effective_domain)
            (htraj := by simpa [hconst] using htraj)
            hx0g hdecrease hcoeff_nonneg
      · -- Outside `effective_domain g`, the initial composite objective is `⊤`, so the first
        -- monotonicity step is immediate because the successor is always feasible.
        have hgx0_top : g (x 0) = ⊤ := by
          exact le_antisymm le_top (not_lt.mp (by simpa using hx0g))
        have hFx0_top : F (x 0) = ⊤ := by
          simp [composite_model_objective_apply, hgx0_top, hf_ne_bot (x 0)]
        rw [hFx0_top]
        exact le_top
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
      have hxjg :
          x (j + 1) ∈ effective_domain g :=
        proximal_gradient_positive_iterate_mem_effective_domain_g
          (f := f)
          (g := g)
          (hf_ne_bot := hf_ne_bot)
          (hf_effective_domain_convex := hf_effective_domain_convex)
          (hg_effective_domain_subset_interior_f_effective_domain :=
            hg_effective_domain_subset_interior_f_effective_domain)
          (hf_toReal_smooth_on_interior_effective_domain :=
            hf_toReal_smooth_on_interior_effective_domain)
          (htraj := htraj) j
      have hdecrease :=
        proximal_gradient_constant_stepsize_sufficient_decrease
          (f := f)
          (g := g)
          (Lf := Lf)
          (hf_ne_bot := hf_ne_bot)
          (hf_effective_domain_convex := hf_effective_domain_convex)
          (hg_effective_domain_subset_interior_f_effective_domain :=
            hg_effective_domain_subset_interior_f_effective_domain)
          (hf_toReal_smooth_on_interior_effective_domain :=
            hf_toReal_smooth_on_interior_effective_domain)
          barL x (by simpa [hconst] using htraj) (j + 1)
      have hcoeff_nonneg :
          0 ≤
            (((barL : ℝ) - (Lf : ℝ) / 2) / ((barL : ℝ) ^ (2 : ℕ))) *
              ‖G[barL] (proximal_gradient_trajectory_iterate
                (by simpa [hconst] using htraj) (j + 1))‖ ^ (2 : ℕ) := by
        have hnum_nonneg : 0 ≤ (barL : ℝ) - (Lf : ℝ) / 2 := by
          exact sub_nonneg.mpr barL.lower_bound.le
        have hden_nonneg : 0 ≤ (barL : ℝ) ^ (2 : ℕ) := by positivity
        exact mul_nonneg (div_nonneg hnum_nonneg hden_nonneg) (sq_nonneg _)
      simpa [Nat.add_assoc] using
        proximal_gradient_objective_step_le_of_mem_effective_domain_g
          (f := f)
          (g := g)
          (Lf := Lf)
          (hf_ne_bot := hf_ne_bot)
          (hf_effective_domain_convex := hf_effective_domain_convex)
          (hg_effective_domain_subset_interior_f_effective_domain :=
            hg_effective_domain_subset_interior_f_effective_domain)
          (hf_toReal_smooth_on_interior_effective_domain :=
            hf_toReal_smooth_on_interior_effective_domain)
          (htraj := by simpa [hconst] using htraj)
          hxjg hdecrease hcoeff_nonneg
  · -- In the B1 branch, every iterate already comes with the required feasibility certificate.
    have hkB1 :
        ∃ hxk : (proximal_gradient_trajectory_iterate htraj k : E) ∈ effective_domain g,
          ∃ i : ℕ,
            is_backtracking_procedure_B1_index
              f g s γ η
              hg_effective_domain_subset_interior_f_effective_domain
              ⟨(proximal_gradient_trajectory_iterate htraj k : E), hxk⟩ i ∧
            L k = proximal_gradient_backtracking_trial_stepsize s η i := hB1 k
    rcases hkB1 with ⟨hxk, i, hi, hLk⟩
    have hdecrease :=
      proximal_gradient_backtracking_B1_sufficient_decrease
        (f := f)
        (g := g)
        (Lf := Lf)
        (hf_ne_bot := hf_ne_bot)
        (hf_effective_domain_convex := hf_effective_domain_convex)
        (hg_effective_domain_subset_interior_f_effective_domain :=
          hg_effective_domain_subset_interior_f_effective_domain)
        (hf_toReal_smooth_on_interior_effective_domain :=
          hf_toReal_smooth_on_interior_effective_domain)
        s γ η x L htraj hB1 k
    have hcoeff_nonneg :
        0 ≤
          ((γ : ℝ) / max (s : ℝ) (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ))))) *
            ‖G[s] (proximal_gradient_trajectory_iterate htraj k)‖ ^ (2 : ℕ) := by
      have hden_pos :
          0 < max (s : ℝ) (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ)))) := by
        exact lt_of_lt_of_le s.2 (le_max_left _ _)
      exact mul_nonneg (div_nonneg (le_of_lt γ.1.2) (le_of_lt hden_pos)) (sq_nonneg _)
    exact
      proximal_gradient_objective_step_le_of_mem_effective_domain_g
        (f := f)
        (g := g)
        (Lf := Lf)
        (hf_ne_bot := hf_ne_bot)
        (hf_effective_domain_convex := hf_effective_domain_convex)
        (hg_effective_domain_subset_interior_f_effective_domain :=
          hg_effective_domain_subset_interior_f_effective_domain)
        (hf_toReal_smooth_on_interior_effective_domain :=
          hf_toReal_smooth_on_interior_effective_domain)
        (htraj := htraj)
        (by simpa [proximal_gradient_trajectory_iterate] using hxk)
        hdecrease hcoeff_nonneg

section

variable [FiniteDimensional ℝ E]

omit hrule in
/-- Helper for Theorem 10.15: if the gradient mapping vanishes at the `k`-th iterate, then the
proximal-gradient update fixes that iterate. -/
lemma proximal_gradient_iterate_succ_eq_self_of_gradient_mapping_eq_zero
    (k : ℕ)
    (hzero : G[L k] (proximal_gradient_trajectory_iterate htraj k) = 0) :
    x (k + 1) = x k := by
  have hfixed :
      T[L k, f, g] (proximal_gradient_trajectory_iterate htraj k) =
        (proximal_gradient_trajectory_iterate htraj k : E) := by
    -- Zero residual means the prox-gradient operator leaves the current iterate unchanged.
    rw [gradient_mapping_apply] at hzero
    rcases smul_eq_zero.mp hzero with hLzero | hsub
    · exact False.elim ((L k).2.ne' hLzero)
    · exact (sub_eq_zero.mp hsub).symm
  -- Rewrite the realized successor as the prox-gradient operator output and then use the fixed
  -- point identity.
  calc
    x (k + 1) = T[L k, f, g] (proximal_gradient_trajectory_iterate htraj k) := by
      exact proximal_gradient_trajectory_succ_eq_prox_grad_operator (f := f) (g := g) htraj k
    _ = (proximal_gradient_trajectory_iterate htraj k : E) := hfixed
    _ = x k := rfl

omit hrule in
/-- Helper for Theorem 10.15: vanishing of the gradient mapping at the `k`-th iterate is
equivalent to stationarity of that iterate for the composite objective. -/
lemma proximal_gradient_iterate_stationary_iff_gradient_mapping_eq_zero
    (L0 : PosReal) (k : ℕ) :
    G[L0] (proximal_gradient_trajectory_iterate htraj k) = 0 ↔
      is_stationary_point f g (x k) := by
  let xk := proximal_gradient_trajectory_iterate htraj k
  have hdiff : is_differentiable_at f (xk : E) :=
    is_differentiable_at_of_mem_interior_effective_domain
      hf_ne_bot
      hf_toReal_smooth_on_interior_effective_domain
      xk.property
  -- The Chapter 10 stationarity bridge applies directly to the realized iterate `x^k`.
  simpa [xk, proximal_gradient_trajectory_iterate] using
    (gradient_mapping_eq_zero_iff_is_stationary_point
      (f := f) (g := g) L0 xk hdiff)

-- Proof sketch: in each admissible stepsize regime, Lemma 10.14 identifies strict decrease with
-- nonvanishing of the appropriate gradient mapping. Then use Theorem 10.7 to rewrite vanishing of
-- that gradient mapping at `x^k` as the Chapter 3 stationary-point condition.
/-- Theorem 10.15 (2): clause (a). Under the same regularity hypotheses, the one-step decrease is
strict exactly when the current iterate `x^k` is not stationary for the composite problem
`min_x {f(x) + g(x)}`. -/
theorem proximal_gradient_step_strict_decrease_iff_not_stationary
    (k : ℕ) :
    F (x (k + 1)) < F (x k) ↔
      ¬ is_stationary_point f g (x k) := by
  -- Route correction: strict decrease is read from the same finite-gap bridge as clause (1), with
  -- the exceptional constant-step initial case again discharged by `F(x^0) = ⊤`.
  rcases hrule with ⟨barL, hconst⟩ | ⟨s, γ, η, hB1⟩
  · constructor
    · intro hlt hstat
      have hzero :
          G[barL] (proximal_gradient_trajectory_iterate
            (by simpa [hconst] using htraj) k) = 0 := by
        exact
          (proximal_gradient_iterate_stationary_iff_gradient_mapping_eq_zero
            (f := f)
            (g := g)
            (Lf := Lf)
            (hf_ne_bot := hf_ne_bot)
            (hf_effective_domain_convex := hf_effective_domain_convex)
            (hg_effective_domain_subset_interior_f_effective_domain :=
              hg_effective_domain_subset_interior_f_effective_domain)
            (hf_toReal_smooth_on_interior_effective_domain :=
              hf_toReal_smooth_on_interior_effective_domain)
            (htraj := by simpa [hconst] using htraj)
            (L0 := barL) (k := k)).mpr hstat
      have hfixed :
          x (k + 1) = x k :=
        proximal_gradient_iterate_succ_eq_self_of_gradient_mapping_eq_zero
          (f := f)
          (g := g)
          (Lf := Lf)
          (hf_ne_bot := hf_ne_bot)
          (hf_effective_domain_convex := hf_effective_domain_convex)
          (hg_effective_domain_subset_interior_f_effective_domain :=
            hg_effective_domain_subset_interior_f_effective_domain)
          (hf_toReal_smooth_on_interior_effective_domain :=
            hf_toReal_smooth_on_interior_effective_domain)
          (htraj := by simpa [hconst] using htraj)
          k hzero
      rw [hfixed] at hlt
      exact (lt_irrefl _ hlt).elim
    · intro hnotstat
      by_cases hk0 : k = 0
      · subst hk0
        by_cases hx0g : x 0 ∈ effective_domain g
        · have hdecrease :=
            proximal_gradient_constant_stepsize_sufficient_decrease
              (f := f)
              (g := g)
              (Lf := Lf)
              (hf_ne_bot := hf_ne_bot)
              (hf_effective_domain_convex := hf_effective_domain_convex)
              (hg_effective_domain_subset_interior_f_effective_domain :=
                hg_effective_domain_subset_interior_f_effective_domain)
              (hf_toReal_smooth_on_interior_effective_domain :=
                hf_toReal_smooth_on_interior_effective_domain)
              barL x (by simpa [hconst] using htraj) 0
          have hnonzero :
              G[barL] (proximal_gradient_trajectory_iterate
                (by simpa [hconst] using htraj) 0) ≠ 0 := by
            intro hzero
            exact hnotstat <|
              (proximal_gradient_iterate_stationary_iff_gradient_mapping_eq_zero
                (f := f)
                (g := g)
                (Lf := Lf)
                (hf_ne_bot := hf_ne_bot)
                (hf_effective_domain_convex := hf_effective_domain_convex)
                (hg_effective_domain_subset_interior_f_effective_domain :=
                  hg_effective_domain_subset_interior_f_effective_domain)
                (hf_toReal_smooth_on_interior_effective_domain :=
                  hf_toReal_smooth_on_interior_effective_domain)
                (htraj := by simpa [hconst] using htraj)
                (L0 := barL) (k := 0)).mp hzero
          have hcoeff_pos :
              0 <
                (((barL : ℝ) - (Lf : ℝ) / 2) / ((barL : ℝ) ^ (2 : ℕ))) *
                  ‖G[barL] (proximal_gradient_trajectory_iterate
                    (by simpa [hconst] using htraj) 0)‖ ^ (2 : ℕ) := by
            have hnum_pos : 0 < (barL : ℝ) - (Lf : ℝ) / 2 := by
              exact sub_pos.mpr barL.lower_bound
            have hden_pos : 0 < (barL : ℝ) ^ (2 : ℕ) := by
              nlinarith [show 0 < ((barL : PosReal) : ℝ) from (barL : PosReal).2]
            have hnorm_sq_pos :
                0 <
                  ‖G[barL] (proximal_gradient_trajectory_iterate
                    (by simpa [hconst] using htraj) 0)‖ ^ (2 : ℕ) := by
              exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hnonzero)
            exact mul_pos (div_pos hnum_pos hden_pos) hnorm_sq_pos
          exact
            proximal_gradient_objective_step_lt_of_mem_effective_domain_g
              (f := f)
              (g := g)
              (Lf := Lf)
              (hf_ne_bot := hf_ne_bot)
              (hf_effective_domain_convex := hf_effective_domain_convex)
              (hg_effective_domain_subset_interior_f_effective_domain :=
                hg_effective_domain_subset_interior_f_effective_domain)
              (hf_toReal_smooth_on_interior_effective_domain :=
                hf_toReal_smooth_on_interior_effective_domain)
              (htraj := by simpa [hconst] using htraj)
              hx0g hdecrease hcoeff_pos
        · have hgx0_top : g (x 0) = ⊤ := by
            exact le_antisymm le_top (not_lt.mp (by simpa using hx0g))
          have hFx0_top : F (x 0) = ⊤ := by
            simp [composite_model_objective_apply, hgx0_top, hf_ne_bot (x 0)]
          have hx1g :
              x 1 ∈ effective_domain g :=
            proximal_gradient_positive_iterate_mem_effective_domain_g
              (f := f)
              (g := g)
              (hf_ne_bot := hf_ne_bot)
              (hf_effective_domain_convex := hf_effective_domain_convex)
              (hg_effective_domain_subset_interior_f_effective_domain :=
                hg_effective_domain_subset_interior_f_effective_domain)
              (hf_toReal_smooth_on_interior_effective_domain :=
                hf_toReal_smooth_on_interior_effective_domain)
              (htraj := htraj) 0
          have hFx1_val :
              F (x 1) = ((((f (x 1)).toReal + (g (x 1)).toReal : ℝ)) : EReal) :=
            proximal_gradient_objective_eq_real_of_mem_effective_domain_g
              (f := f)
              (g := g)
              (hf_ne_bot := hf_ne_bot)
              (hg_effective_domain_subset_interior_f_effective_domain :=
                hg_effective_domain_subset_interior_f_effective_domain)
              hx1g
          rw [hFx1_val, hFx0_top]
          simpa using EReal.coe_lt_top ((f (x 1)).toReal + (g (x 1)).toReal)
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0
        have hxjg :
            x (j + 1) ∈ effective_domain g :=
          proximal_gradient_positive_iterate_mem_effective_domain_g
            (f := f)
            (g := g)
            (hf_ne_bot := hf_ne_bot)
            (hf_effective_domain_convex := hf_effective_domain_convex)
            (hg_effective_domain_subset_interior_f_effective_domain :=
              hg_effective_domain_subset_interior_f_effective_domain)
            (hf_toReal_smooth_on_interior_effective_domain :=
              hf_toReal_smooth_on_interior_effective_domain)
            (htraj := htraj) j
        have hdecrease :=
          proximal_gradient_constant_stepsize_sufficient_decrease
            (f := f)
            (g := g)
            (Lf := Lf)
            (hf_ne_bot := hf_ne_bot)
            (hf_effective_domain_convex := hf_effective_domain_convex)
            (hg_effective_domain_subset_interior_f_effective_domain :=
              hg_effective_domain_subset_interior_f_effective_domain)
            (hf_toReal_smooth_on_interior_effective_domain :=
              hf_toReal_smooth_on_interior_effective_domain)
            barL x (by simpa [hconst] using htraj) (j + 1)
        have hnonzero :
            G[barL] (proximal_gradient_trajectory_iterate
              (by simpa [hconst] using htraj) (j + 1)) ≠ 0 := by
          intro hzero
          exact hnotstat <|
            (proximal_gradient_iterate_stationary_iff_gradient_mapping_eq_zero
              (f := f)
              (g := g)
              (Lf := Lf)
              (hf_ne_bot := hf_ne_bot)
              (hf_effective_domain_convex := hf_effective_domain_convex)
              (hg_effective_domain_subset_interior_f_effective_domain :=
                hg_effective_domain_subset_interior_f_effective_domain)
              (hf_toReal_smooth_on_interior_effective_domain :=
                hf_toReal_smooth_on_interior_effective_domain)
              (htraj := by simpa [hconst] using htraj)
              (L0 := barL) (k := j + 1)).mp hzero
        have hcoeff_pos :
            0 <
              (((barL : ℝ) - (Lf : ℝ) / 2) / ((barL : ℝ) ^ (2 : ℕ))) *
                ‖G[barL] (proximal_gradient_trajectory_iterate
                  (by simpa [hconst] using htraj) (j + 1))‖ ^ (2 : ℕ) := by
          have hnum_pos : 0 < (barL : ℝ) - (Lf : ℝ) / 2 := by
            exact sub_pos.mpr barL.lower_bound
          have hden_pos : 0 < (barL : ℝ) ^ (2 : ℕ) := by
            nlinarith [show 0 < ((barL : PosReal) : ℝ) from (barL : PosReal).2]
          have hnorm_sq_pos :
              0 <
                ‖G[barL] (proximal_gradient_trajectory_iterate
                  (by simpa [hconst] using htraj) (j + 1))‖ ^ (2 : ℕ) := by
            exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hnonzero)
          exact mul_pos (div_pos hnum_pos hden_pos) hnorm_sq_pos
        simpa [Nat.add_assoc] using
          proximal_gradient_objective_step_lt_of_mem_effective_domain_g
            (f := f)
            (g := g)
            (Lf := Lf)
            (hf_ne_bot := hf_ne_bot)
            (hf_effective_domain_convex := hf_effective_domain_convex)
            (hg_effective_domain_subset_interior_f_effective_domain :=
              hg_effective_domain_subset_interior_f_effective_domain)
            (hf_toReal_smooth_on_interior_effective_domain :=
              hf_toReal_smooth_on_interior_effective_domain)
            (htraj := by simpa [hconst] using htraj)
            hxjg hdecrease hcoeff_pos
  · constructor
    · intro hlt hstat
      have hzero :
          G[L k] (proximal_gradient_trajectory_iterate htraj k) = 0 := by
        exact
          (proximal_gradient_iterate_stationary_iff_gradient_mapping_eq_zero
            (f := f)
            (g := g)
            (Lf := Lf)
            (hf_ne_bot := hf_ne_bot)
            (hf_effective_domain_convex := hf_effective_domain_convex)
            (hg_effective_domain_subset_interior_f_effective_domain :=
              hg_effective_domain_subset_interior_f_effective_domain)
            (hf_toReal_smooth_on_interior_effective_domain :=
              hf_toReal_smooth_on_interior_effective_domain)
            (htraj := htraj)
            (L0 := L k) (k := k)).mpr hstat
      have hfixed :
          x (k + 1) = x k :=
        proximal_gradient_iterate_succ_eq_self_of_gradient_mapping_eq_zero
          (f := f)
          (g := g)
          (Lf := Lf)
          (hf_ne_bot := hf_ne_bot)
          (hf_effective_domain_convex := hf_effective_domain_convex)
          (hg_effective_domain_subset_interior_f_effective_domain :=
            hg_effective_domain_subset_interior_f_effective_domain)
          (hf_toReal_smooth_on_interior_effective_domain :=
            hf_toReal_smooth_on_interior_effective_domain)
          (htraj := htraj)
          k hzero
      rw [hfixed] at hlt
      exact (lt_irrefl _ hlt).elim
    · intro hnotstat
      have hkB1 :
          ∃ hxk : (proximal_gradient_trajectory_iterate htraj k : E) ∈ effective_domain g,
            ∃ i : ℕ,
              is_backtracking_procedure_B1_index
                f g s γ η
                hg_effective_domain_subset_interior_f_effective_domain
                ⟨(proximal_gradient_trajectory_iterate htraj k : E), hxk⟩ i ∧
              L k = proximal_gradient_backtracking_trial_stepsize s η i := hB1 k
      rcases hkB1 with ⟨hxk, i, hi, hLk⟩
      have hdecrease :=
        proximal_gradient_backtracking_B1_sufficient_decrease
          (f := f)
          (g := g)
          (Lf := Lf)
          (hf_ne_bot := hf_ne_bot)
          (hf_effective_domain_convex := hf_effective_domain_convex)
          (hg_effective_domain_subset_interior_f_effective_domain :=
            hg_effective_domain_subset_interior_f_effective_domain)
          (hf_toReal_smooth_on_interior_effective_domain :=
            hf_toReal_smooth_on_interior_effective_domain)
          s γ η x L htraj hB1 k
      have hnonzero :
          G[s] (proximal_gradient_trajectory_iterate htraj k) ≠ 0 := by
        intro hzero
        exact hnotstat <|
          (proximal_gradient_iterate_stationary_iff_gradient_mapping_eq_zero
            (f := f)
            (g := g)
            (Lf := Lf)
            (hf_ne_bot := hf_ne_bot)
            (hf_effective_domain_convex := hf_effective_domain_convex)
            (hg_effective_domain_subset_interior_f_effective_domain :=
              hg_effective_domain_subset_interior_f_effective_domain)
            (hf_toReal_smooth_on_interior_effective_domain :=
              hf_toReal_smooth_on_interior_effective_domain)
            (htraj := htraj)
            (L0 := s) (k := k)).mp hzero
      have hden_pos :
          0 < max (s : ℝ) (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ)))) := by
        exact lt_of_lt_of_le s.2 (le_max_left _ _)
      have hcoeff_pos :
          0 <
            ((γ : ℝ) / max (s : ℝ) (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ))))) *
              ‖G[s] (proximal_gradient_trajectory_iterate htraj k)‖ ^ (2 : ℕ) := by
        have hnorm_sq_pos :
            0 < ‖G[s] (proximal_gradient_trajectory_iterate htraj k)‖ ^ (2 : ℕ) := by
          exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hnonzero)
        exact mul_pos (div_pos γ.1.2 hden_pos) hnorm_sq_pos
      exact
        proximal_gradient_objective_step_lt_of_mem_effective_domain_g
          (f := f)
          (g := g)
          (Lf := Lf)
          (hf_ne_bot := hf_ne_bot)
          (hf_effective_domain_convex := hf_effective_domain_convex)
          (hg_effective_domain_subset_interior_f_effective_domain :=
            hg_effective_domain_subset_interior_f_effective_domain)
          (hf_toReal_smooth_on_interior_effective_domain :=
            hf_toReal_smooth_on_interior_effective_domain)
          (htraj := htraj)
          (by simpa [proximal_gradient_trajectory_iterate] using hxk)
          hdecrease hcoeff_pos

end

end SufficientDecreaseRule

section LowerBound

variable {FOpt : ℝ}
variable
    (hf_ne_bot : ∀ y, f y ≠ ⊥)
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f))
    (hf_toReal_smooth_on_interior_effective_domain :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)

set_option quotPrecheck false in
local notation "R[" htraj "; " d ", " k "]" =>
  best_achieved_function_value
    (fun y ↦ ‖G[d] y‖) (proximal_gradient_trajectory_iterate htraj) k

/-- Helper for Theorem 10.15: the squared running-best residual on a prefix is bounded above by
the average of the squared residuals on that prefix. -/
lemma best_residual_sq_mul_prefix_length_le_sum
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L)
    (d : PosReal) (k : ℕ) :
    (k + 1 : ℝ) * R[htraj; d, k] ^ (2 : ℕ) ≤
      Finset.sum (Finset.range (k + 1))
        (fun n ↦ ‖G[d] (proximal_gradient_trajectory_iterate htraj n)‖ ^ (2 : ℕ)) := by
  have hbest_nonneg : 0 ≤ R[htraj; d, k] := by
    -- The running minimum is attained by one prefix residual norm, hence is nonnegative.
    unfold best_achieved_function_value
    have hmem :=
      Finset.min'_mem
        ((Finset.range (k + 1)).image
          fun n ↦ ‖G[d] (proximal_gradient_trajectory_iterate htraj n)‖)
        (objective_value_prefix_nonempty
          (fun y ↦ ‖G[d] y‖) (proximal_gradient_trajectory_iterate htraj) k)
    rcases Finset.mem_image.mp hmem with ⟨n, _, hn⟩
    rw [← hn]
    exact norm_nonneg _
  have hpointwise :
      ∀ n ∈ Finset.range (k + 1),
        R[htraj; d, k] ^ (2 : ℕ) ≤
          ‖G[d] (proximal_gradient_trajectory_iterate htraj n)‖ ^ (2 : ℕ) := by
    intro n hn
    have hbest_le :=
      best_achieved_function_value_le_objective_value
        (f := fun y ↦ ‖G[d] y‖) (proximal_gradient_trajectory_iterate htraj) k n hn
    nlinarith [hbest_nonneg, norm_nonneg (G[d] (proximal_gradient_trajectory_iterate htraj n)),
      hbest_le]
  -- Summing the pointwise lower bound across the whole prefix yields the structural estimate.
  calc
    (k + 1 : ℝ) * R[htraj; d, k] ^ (2 : ℕ) =
        Finset.sum (Finset.range (k + 1)) (fun _ ↦ R[htraj; d, k] ^ (2 : ℕ)) := by
      simp
    _ ≤ Finset.sum (Finset.range (k + 1))
          (fun n ↦ ‖G[d] (proximal_gradient_trajectory_iterate htraj n)‖ ^ (2 : ℕ)) := by
      exact Finset.sum_le_sum hpointwise

/-- Helper for Theorem 10.15: a real-valued antitone sequence that is bounded below has
successive differences converging to `0`. -/
private lemma objective_gap_tendsto_zero_of_antitone_bddBelow
    {φ : ℕ → ℝ}
    (hanti : Antitone φ)
    (hbelow : BddBelow (Set.range φ)) :
    Filter.Tendsto (fun k ↦ φ k - φ (k + 1)) Filter.atTop (nhds 0) := by
  let ℓ : ℝ := ⨅ k, φ k
  have hobj :
      Filter.Tendsto (fun k ↦ φ k) Filter.atTop (nhds ℓ) :=
    tendsto_atTop_ciInf hanti hbelow
  have hobj_shift :
      Filter.Tendsto (fun k ↦ φ (k + 1)) Filter.atTop (nhds ℓ) := by
    have hshift :
        Filter.Tendsto (fun k : ℕ ↦ k + 1) Filter.atTop Filter.atTop :=
      (show StrictMono (fun k : ℕ ↦ k + 1) from
        fun a b hab ↦ Nat.add_lt_add_right hab 1).tendsto_atTop
    simpa [ℓ] using hobj.comp hshift
  -- Subtracting the shifted copy leaves a sequence converging to `ℓ - ℓ = 0`.
  simpa [ℓ] using hobj.sub hobj_shift

/-- Helper for Theorem 10.15: a finite composite-objective gap to the lower bound `FOpt` is the
cast of the corresponding real difference. -/
lemma proximal_gradient_objective_minus_FOpt_eq_coe_sub_toReal_of_mem_effective_domain_g
    (hf_ne_bot_local : ∀ y, f y ≠ ⊥)
    (hg_subset_local : effective_domain g ⊆ interior (effective_domain f))
    {xPoint : E} (hxPoint : xPoint ∈ effective_domain g) :
    ((((F xPoint).toReal - FOpt : ℝ) : EReal)) =
      F xPoint - (FOpt : EReal) := by
  have hxPoint_val :
      F xPoint = ((((f xPoint).toReal + (g xPoint).toReal : ℝ)) : EReal) :=
    proximal_gradient_objective_eq_real_of_mem_effective_domain_g
      (f := f)
      (g := g)
      (hf_ne_bot := hf_ne_bot_local)
      (hg_effective_domain_subset_interior_f_effective_domain := hg_subset_local)
      hxPoint
  have hxPoint_toReal :
      (F xPoint).toReal = (f xPoint).toReal + (g xPoint).toReal := by
    rw [hxPoint_val]
    simpa using EReal.toReal_coe ((f xPoint).toReal + (g xPoint).toReal)
  -- Rewrite the finite objective value through its real representative before subtracting `FOpt`.
  rw [hxPoint_toReal, hxPoint_val]
  simp [EReal.coe_sub]

/-- Helper for Theorem 10.15: any feasible iterate has composite objective value at least the
optimal lower bound `FOpt`. -/
lemma proximal_gradient_toReal_ge_FOpt_of_isGLB
    (hFOpt : IsGLB (Set.range F) (FOpt : EReal))
    (hf_ne_bot_local : ∀ y, f y ≠ ⊥)
    (hg_subset_local : effective_domain g ⊆ interior (effective_domain f))
    {xPoint : E} (hxPoint : xPoint ∈ effective_domain g) :
    FOpt ≤ (F xPoint).toReal := by
  have hxPoint_val :
      F xPoint = ((((f xPoint).toReal + (g xPoint).toReal : ℝ)) : EReal) :=
    proximal_gradient_objective_eq_real_of_mem_effective_domain_g
      (f := f)
      (g := g)
      (hf_ne_bot := hf_ne_bot_local)
      (hg_effective_domain_subset_interior_f_effective_domain := hg_subset_local)
      hxPoint
  have hxPoint_toReal :
      (F xPoint).toReal = (f xPoint).toReal + (g xPoint).toReal := by
    rw [hxPoint_val]
    simpa using EReal.toReal_coe ((f xPoint).toReal + (g xPoint).toReal)
  have hxPoint_finite :
      (((F xPoint).toReal : ℝ) : EReal) = F xPoint := by
    rw [hxPoint_toReal, hxPoint_val]
  have hlower : (FOpt : EReal) ≤ F xPoint := hFOpt.1 ⟨xPoint, rfl⟩
  -- Once the feasible objective value is known to be finite, the `EReal` lower bound reads as a
  -- plain real inequality.
  rw [← hxPoint_finite] at hlower
  exact EReal.coe_le_coe_iff.mp hlower

/-- Helper for Theorem 10.15: converting a one-step `EReal` sufficient-decrease estimate to the
finite real layer only requires feasibility of the current iterate. -/
lemma proximal_gradient_real_step_gap_lower_bound_of_mem_effective_domain_g
    (hf_ne_bot_local : ∀ y, f y ≠ ⊥)
    (hf_effective_domain_convex_local : Convex ℝ (effective_domain f))
    (hg_subset_local : effective_domain g ⊆ interior (effective_domain f))
    (hf_smooth_local :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L)
    (k : ℕ) (hxkg : x k ∈ effective_domain g) {gap : ℝ}
    (hgap :
      F (x k) - F (x (k + 1)) ≥ ((gap : ℝ) : EReal)) :
    gap ≤ (F (x k)).toReal - (F (x (k + 1))).toReal := by
  have hgap' : ((gap : ℝ) : EReal) ≤ F (x k) - F (x (k + 1)) := by
    simpa using hgap
  -- The objective-gap bridge isolates the whole `EReal` transport in one rewrite.
  have hgap'' :
      ((gap : ℝ) : EReal) ≤
        ((((F (x k)).toReal - (F (x (k + 1))).toReal : ℝ)) : EReal) := by
    have htmp : ((gap : ℝ) : EReal) ≤ F (x k) - F (x (k + 1)) := hgap'
    rw [proximal_gradient_objective_gap_eq_coe_sub_toReal_of_mem_effective_domain_g
      (f := f)
      (g := g)
      (Lf := Lf)
      (hf_ne_bot := hf_ne_bot_local)
      (hf_effective_domain_convex := hf_effective_domain_convex_local)
      (hg_effective_domain_subset_interior_f_effective_domain := hg_subset_local)
      (hf_toReal_smooth_on_interior_effective_domain := hf_smooth_local)
      (htraj := htraj)
      k hxkg] at htmp
    exact htmp
  exact EReal.coe_le_coe_iff.mp hgap''

/-- Helper for Theorem 10.15: every iterate produced by backtracking rule `B1` is feasible for
the nonsmooth term `g`. -/
lemma proximal_gradient_backtracking_iterate_mem_effective_domain_g
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L)
    (s : PosReal) (γ : ProximalGradientBacktrackingDecreaseFraction)
    (η : ProximalGradientBacktrackingGrowthFactor)
    (hB1 : uses_proximal_gradient_backtracking_B1_rule
      f g hg_effective_domain_subset_interior_f_effective_domain x L htraj s γ η)
    (k : ℕ) :
    x k ∈ effective_domain g := by
  rcases hB1 k with ⟨hxk, _, _, _⟩
  simpa [proximal_gradient_trajectory_iterate] using hxk

/-- Helper for Theorem 10.15: if the current iterate is feasible in the constant-stepsize regime,
then the one-step sufficient-decrease inequality can be rewritten on the finite real layer. -/
lemma proximal_gradient_constant_stepsize_real_sufficient_decrease_of_mem_effective_domain_g
    (hf_ne_bot_local : ∀ y, f y ≠ ⊥)
    (hf_effective_domain_convex_local : Convex ℝ (effective_domain f))
    (hg_subset_local : effective_domain g ⊆ interior (effective_domain f))
    (hf_smooth_local :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)
    {x : ℕ → E} (barL : ProximalGradientConstantStepsizeParameter Lf)
    (htraj : is_proximal_gradient_trajectory f g x (Function.const ℕ barL))
    (k : ℕ) (hxkg : x k ∈ effective_domain g) :
    (((barL : ℝ) - (Lf : ℝ) / 2) / ((barL : ℝ) ^ (2 : ℕ))) *
        ‖G[barL] (proximal_gradient_trajectory_iterate htraj k)‖ ^ (2 : ℕ) ≤
      (F (x k)).toReal - (F (x (k + 1))).toReal := by
  -- Convert the Chapter 10 sufficient-decrease estimate at step `k` through the real-gap bridge.
  exact
    proximal_gradient_real_step_gap_lower_bound_of_mem_effective_domain_g
      (f := f)
      (g := g)
      (Lf := Lf)
      (hf_ne_bot_local := hf_ne_bot_local)
      (hf_effective_domain_convex_local := hf_effective_domain_convex_local)
      (hg_subset_local := hg_subset_local)
      (hf_smooth_local := hf_smooth_local)
      (htraj := htraj)
      (k := k)
      hxkg
      (proximal_gradient_constant_stepsize_sufficient_decrease
        (f := f)
        (g := g)
        (Lf := Lf)
        (hf_ne_bot := hf_ne_bot_local)
        (hf_effective_domain_convex := hf_effective_domain_convex_local)
        (hg_effective_domain_subset_interior_f_effective_domain := hg_subset_local)
        (hf_toReal_smooth_on_interior_effective_domain := hf_smooth_local)
        barL x htraj k)

/-- Helper for Theorem 10.15: in the constant-stepsize regime, each positive iterate satisfies
the real sufficient-decrease inequality used in clauses `(b)` and `(c)`. -/
lemma proximal_gradient_constant_stepsize_real_sufficient_decrease
    (hf_ne_bot_local : ∀ y, f y ≠ ⊥)
    (hf_effective_domain_convex_local : Convex ℝ (effective_domain f))
    (hg_subset_local : effective_domain g ⊆ interior (effective_domain f))
    (hf_smooth_local :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)
    {x : ℕ → E} (barL : ProximalGradientConstantStepsizeParameter Lf)
    (htraj : is_proximal_gradient_trajectory f g x (Function.const ℕ barL))
    (k : ℕ) :
    (((barL : ℝ) - (Lf : ℝ) / 2) / ((barL : ℝ) ^ (2 : ℕ))) *
        ‖G[barL] (proximal_gradient_trajectory_iterate htraj (k + 1))‖ ^ (2 : ℕ) ≤
      (F (x (k + 1))).toReal - (F (x (k + 2))).toReal := by
  have hxk1g :
      x (k + 1) ∈ effective_domain g :=
    proximal_gradient_positive_iterate_mem_effective_domain_g
      (f := f)
      (g := g)
      (hf_ne_bot := hf_ne_bot_local)
      (hf_effective_domain_convex := hf_effective_domain_convex_local)
      (hg_effective_domain_subset_interior_f_effective_domain := hg_subset_local)
      (hf_toReal_smooth_on_interior_effective_domain := hf_smooth_local)
      (htraj := htraj)
      k
  -- Specialize the unshifted real-gap bridge at the positive iterate `x^(k+1)`.
  simpa [Nat.add_assoc] using
    proximal_gradient_constant_stepsize_real_sufficient_decrease_of_mem_effective_domain_g
      hf_ne_bot_local
      hf_effective_domain_convex_local
      hg_subset_local
      hf_smooth_local
      barL htraj (k + 1) hxk1g

/-- Helper for Theorem 10.15: in the backtracking-B1 regime, each iterate satisfies the real
sufficient-decrease inequality used in clauses `(b)` and `(c)`. -/
lemma proximal_gradient_backtracking_B1_real_sufficient_decrease
    (hf_ne_bot_local : ∀ y, f y ≠ ⊥)
    (hf_effective_domain_convex_local : Convex ℝ (effective_domain f))
    (hg_subset_local : effective_domain g ⊆ interior (effective_domain f))
    (hf_smooth_local :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L)
    (s : PosReal) (γ : ProximalGradientBacktrackingDecreaseFraction)
    (η : ProximalGradientBacktrackingGrowthFactor)
    (hB1 : uses_proximal_gradient_backtracking_B1_rule
      f g hg_effective_domain_subset_interior_f_effective_domain x L htraj s γ η)
    (k : ℕ) :
    (γ : ℝ) / max (s : ℝ) (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ)))) *
        ‖G[s] (proximal_gradient_trajectory_iterate htraj k)‖ ^ (2 : ℕ) ≤
      (F (x k)).toReal - (F (x (k + 1))).toReal := by
  have hxkg :
      x k ∈ effective_domain g :=
    proximal_gradient_backtracking_iterate_mem_effective_domain_g
      (f := f)
      (g := g)
      (hg_effective_domain_subset_interior_f_effective_domain := hg_subset_local)
      (htraj := htraj)
      s γ η hB1 k
  -- Rewrite the Chapter 10 B1 sufficient-decrease estimate through the real-gap bridge.
  exact
    proximal_gradient_real_step_gap_lower_bound_of_mem_effective_domain_g
      (f := f)
      (g := g)
      (Lf := Lf)
      (hf_ne_bot_local := hf_ne_bot_local)
      (hf_effective_domain_convex_local := hf_effective_domain_convex_local)
      (hg_subset_local := hg_subset_local)
      (hf_smooth_local := hf_smooth_local)
      (htraj := htraj)
      (k := k)
      hxkg
      (proximal_gradient_backtracking_B1_sufficient_decrease
        (f := f)
        (g := g)
        (Lf := Lf)
        (hf_ne_bot := hf_ne_bot_local)
        (hf_effective_domain_convex := hf_effective_domain_convex_local)
        (hg_effective_domain_subset_interior_f_effective_domain := hg_subset_local)
        (hf_toReal_smooth_on_interior_effective_domain := hf_smooth_local)
        s γ η x L htraj hB1 k)

/-- Helper for Theorem 10.15: summing one-step real objective drops over the prefix `0, …, k`
telescopes to the gap between the initial and terminal real objective values. -/
private lemma proximal_gradient_real_objective_telescope
    (φ : ℕ → ℝ) (k : ℕ) :
    Finset.sum (Finset.range (k + 1)) (fun n ↦ φ n - φ (n + 1)) =
      φ 0 - φ (k + 1) := by
  -- This is the exact telescoping identity used in the source proof for clause `(c)`.
  have htel := Finset.sum_range_sub φ (k + 1)
  calc
    Finset.sum (Finset.range (k + 1)) (fun n ↦ φ n - φ (n + 1)) =
        Finset.sum (Finset.range (k + 1)) (fun n ↦ -(φ (n + 1) - φ n)) := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      ring
    _ = -Finset.sum (Finset.range (k + 1)) (fun n ↦ φ (n + 1) - φ n) := by
      rw [Finset.sum_neg_distrib]
    _ = -(φ (k + 1) - φ 0) := by
      rw [htel]
    _ = φ 0 - φ (k + 1) := by
      ring

/-- Helper for Theorem 10.15: if a positive scalar multiple of squared residual norms tends to
`0`, then the residuals themselves tend to `0`. -/
private lemma tendsto_zero_of_scaled_sq_norm_tendsto_zero
    {u : ℕ → E} {c : ℝ}
    (hc : 0 < c)
    (hscaled :
      Filter.Tendsto (fun k ↦ c * ‖u k‖ ^ (2 : ℕ)) Filter.atTop (nhds 0)) :
    Filter.Tendsto u Filter.atTop (nhds 0) := by
  have hsq_eq :
      (fun k ↦ ‖u k‖ ^ (2 : ℕ)) =
        fun k ↦ (1 / c) * (c * ‖u k‖ ^ (2 : ℕ)) := by
    funext k
    field_simp [hc.ne']
  have hsq_tendsto_zero :
      Filter.Tendsto (fun k ↦ ‖u k‖ ^ (2 : ℕ)) Filter.atTop (nhds 0) := by
    rw [hsq_eq]
    simpa using hscaled.const_mul (1 / c)
  have hsqrt_tendsto_zero :
      Filter.Tendsto (fun k ↦ Real.sqrt (‖u k‖ ^ (2 : ℕ))) Filter.atTop (nhds 0) := by
    let hsqrt_cont : ContinuousAt Real.sqrt 0 := Real.continuous_sqrt.continuousAt
    simpa only [Function.comp, Real.sqrt_zero] using hsqrt_cont.tendsto.comp hsq_tendsto_zero
  have hnorm_eq_sqrt :
      ∀ k, ‖u k‖ = Real.sqrt (‖u k‖ ^ (2 : ℕ)) := by
    intro k
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
    exact norm_nonneg _
  have hnorm_tendsto_zero :
      Filter.Tendsto (fun k ↦ ‖u k‖) Filter.atTop (nhds 0) := by
    have hEq :
        (fun k ↦ ‖u k‖) = fun k ↦ Real.sqrt (‖u k‖ ^ (2 : ℕ)) := by
      funext k
      exact hnorm_eq_sqrt k
    rw [hEq]
    exact hsqrt_tendsto_zero
  -- Convergence in norm to zero is equivalent to convergence of the vector sequence to `0`.
  refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
  simpa using hnorm_tendsto_zero

include hf_ne_bot hf_effective_domain_convex
  hg_effective_domain_subset_interior_f_effective_domain
  hf_toReal_smooth_on_interior_effective_domain

omit hf_ne_bot hf_effective_domain_convex
  hg_effective_domain_subset_interior_f_effective_domain
  hf_toReal_smooth_on_interior_effective_domain in
-- Proof sketch: the sufficient-decrease estimate from Lemma 10.14 gives
-- `F(x^k) - F(x^(k+1)) ≥ M ‖G_d(x^k)‖²`. If `FOpt` is the greatest lower bound of the composite
-- objective, then `F(x^k)` is bounded below, so its successive differences tend to `0`, forcing
-- `G_d(x^k) → 0`.
/-- Theorem 10.15 (3): clause (b), constant-step case. If the proximal-gradient trajectory uses
the constant stepsize `barL ∈ (L_f / 2, ∞)` and `FOpt` is the greatest lower bound of
`Set.range (f + g)`, then the corresponding residual sequence `G_barL(x^k)` converges to `0`. -/
theorem proximal_gradient_constant_stepsize_residual_tendsto_zero
    (hf_ne_bot : ∀ y, f y ≠ ⊥)
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f))
    (hf_toReal_smooth_on_interior_effective_domain :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)
    {x : ℕ → E} (barL : ProximalGradientConstantStepsizeParameter Lf)
    (htraj : is_proximal_gradient_trajectory f g x
      (Function.const ℕ barL))
    (hFOpt : IsGLB (Set.range F) (FOpt : EReal)) :
    Filter.Tendsto
      (fun k ↦ G[barL] (proximal_gradient_trajectory_iterate htraj k))
      Filter.atTop (nhds 0) := by
  let c : ℝ := ((barL : ℝ) - (Lf : ℝ) / 2) / ((barL : ℝ) ^ (2 : ℕ))
  have hc_pos : 0 < c := by
    -- The constant-stepsize coefficient is positive because `barL > L_f / 2`.
    dsimp [c]
    have hnum_pos : 0 < (barL : ℝ) - (Lf : ℝ) / 2 := by
      exact sub_pos.mpr barL.lower_bound
    have hden_pos : 0 < (barL : ℝ) ^ (2 : ℕ) := by
      exact pow_pos barL.1.2 2
    exact div_pos hnum_pos hden_pos
  let φ : ℕ → ℝ := fun k ↦ (F (x (k + 1))).toReal
  have hanti : Antitone φ := by
    -- On the feasible tail, the real sufficient-decrease inequality directly yields monotonicity.
    refine antitone_nat_of_succ_le ?_
    intro k
    have hdecrease :
        c * ‖G[barL] (proximal_gradient_trajectory_iterate htraj (k + 1))‖ ^ (2 : ℕ) ≤
          φ k - φ (k + 1) := by
      simpa [c, φ] using
        proximal_gradient_constant_stepsize_real_sufficient_decrease
          (f := f)
          (g := g)
          (Lf := Lf)
          hf_ne_bot
          hf_effective_domain_convex
          hg_effective_domain_subset_interior_f_effective_domain
          hf_toReal_smooth_on_interior_effective_domain
          barL htraj k
    have hterm_nonneg :
        0 ≤ c * ‖G[barL] (proximal_gradient_trajectory_iterate htraj (k + 1))‖ ^ (2 : ℕ) := by
      exact mul_nonneg (le_of_lt hc_pos) (sq_nonneg _)
    exact sub_nonneg.mp (le_trans hterm_nonneg hdecrease)
  have hbelow : BddBelow (Set.range φ) := by
    -- Every positive iterate is feasible, so its finite objective value is bounded below by `FOpt`.
    refine ⟨FOpt, ?_⟩
    intro y hy
    rcases hy with ⟨k, rfl⟩
    exact
      proximal_gradient_toReal_ge_FOpt_of_isGLB
        (f := f)
        (g := g)
        (FOpt := FOpt)
        hFOpt
        hf_ne_bot
        hg_effective_domain_subset_interior_f_effective_domain
        (proximal_gradient_positive_iterate_mem_effective_domain_g
          (f := f)
          (g := g)
          (Lf := Lf)
          (hf_ne_bot := hf_ne_bot)
          (hf_effective_domain_convex := hf_effective_domain_convex)
          (hg_effective_domain_subset_interior_f_effective_domain :=
            hg_effective_domain_subset_interior_f_effective_domain)
          (hf_toReal_smooth_on_interior_effective_domain :=
            hf_toReal_smooth_on_interior_effective_domain)
          (htraj := htraj)
          k)
  have hgap_tendsto_zero :
      Filter.Tendsto (fun k ↦ φ k - φ (k + 1)) Filter.atTop (nhds 0) :=
    objective_gap_tendsto_zero_of_antitone_bddBelow hanti hbelow
  have hscaled_tendsto_zero :
      Filter.Tendsto
        (fun k ↦ c * ‖G[barL] (proximal_gradient_trajectory_iterate htraj (k + 1))‖ ^ (2 : ℕ))
        Filter.atTop
        (nhds 0) := by
    -- The scaled squared residuals are squeezed between `0` and the vanishing objective gaps.
    refine squeeze_zero ?_ ?_ hgap_tendsto_zero
    · intro k
      exact mul_nonneg (le_of_lt hc_pos) (sq_nonneg _)
    · intro k
      simpa [c, φ] using
        proximal_gradient_constant_stepsize_real_sufficient_decrease
          (f := f)
          (g := g)
          (Lf := Lf)
          hf_ne_bot
          hf_effective_domain_convex
          hg_effective_domain_subset_interior_f_effective_domain
          hf_toReal_smooth_on_interior_effective_domain
          barL htraj k
  have htail_res :
      Filter.Tendsto
        (fun k ↦ G[barL] (proximal_gradient_trajectory_iterate htraj (k + 1)))
        Filter.atTop
        (nhds 0) :=
    tendsto_zero_of_scaled_sq_norm_tendsto_zero hc_pos hscaled_tendsto_zero
  -- A shift by one index does not affect convergence at `atTop`.
  rw [← Filter.tendsto_add_atTop_iff_nat
    (f := fun k ↦ G[barL] (proximal_gradient_trajectory_iterate htraj k)) 1]
  exact htail_res

-- Proof sketch: the B1 sufficient-decrease estimate from Lemma 10.14 gives
-- `F(x^k) - F(x^(k+1)) ≥ M ‖G_s(x^k)‖²` with
-- `M = γ / max {s, η L_f / (2 (1 - γ))}`. If `FOpt` is the greatest lower bound of the
-- composite objective, then `F(x^k)` is bounded below, so its successive differences tend to
-- `0`, forcing `G_s(x^k) → 0`.
/-- Theorem 10.15 (3): clause (b), backtracking-B1 case. If the trajectory uses backtracking
procedure B1 with parameters `(s, γ, η)` and `FOpt` is the greatest lower bound of
`Set.range (f + g)`, then the corresponding residual sequence `G_s(x^k)` converges to `0`. -/
theorem proximal_gradient_backtracking_B1_residual_tendsto_zero
    (hf_ne_bot : ∀ y, f y ≠ ⊥)
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f))
    (hf_toReal_smooth_on_interior_effective_domain :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L)
    (s : PosReal) (γ : ProximalGradientBacktrackingDecreaseFraction)
    (η : ProximalGradientBacktrackingGrowthFactor)
    (hB1 : uses_proximal_gradient_backtracking_B1_rule
      f g hg_effective_domain_subset_interior_f_effective_domain x L htraj s γ η)
    (hFOpt : IsGLB (Set.range F) (FOpt : EReal)) :
    Filter.Tendsto
      (fun k ↦ G[s] (proximal_gradient_trajectory_iterate htraj k))
      Filter.atTop (nhds 0) := by
  let c : ℝ := (γ : ℝ) / max (s : ℝ) (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ))))
  have hc_pos : 0 < c := by
    -- The B1 coefficient is positive because both the numerator `γ` and the denominator are.
    dsimp [c]
    have hden_pos :
        0 < max (s : ℝ) (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ)))) := by
      exact lt_of_lt_of_le s.2 (le_max_left _ _)
    exact div_pos γ.1.2 hden_pos
  let φ : ℕ → ℝ := fun k ↦ (F (x k)).toReal
  have hanti : Antitone φ := by
    -- In the B1 regime every iterate is feasible, so the real sufficient-decrease inequality is
    -- available without shifting.
    refine antitone_nat_of_succ_le ?_
    intro k
    have hdecrease :
        c * ‖G[s] (proximal_gradient_trajectory_iterate htraj k)‖ ^ (2 : ℕ) ≤
          φ k - φ (k + 1) := by
      simpa [c, φ] using
        proximal_gradient_backtracking_B1_real_sufficient_decrease
          (f := f)
          (g := g)
          (Lf := Lf)
          (hf_ne_bot_local := hf_ne_bot)
          (hf_effective_domain_convex_local := hf_effective_domain_convex)
          (hg_subset_local := hg_effective_domain_subset_interior_f_effective_domain)
          (hf_smooth_local := hf_toReal_smooth_on_interior_effective_domain)
          (htraj := htraj)
          (s := s)
          (γ := γ)
          (η := η)
          (hB1 := hB1)
          (k := k)
    have hterm_nonneg :
        0 ≤ c * ‖G[s] (proximal_gradient_trajectory_iterate htraj k)‖ ^ (2 : ℕ) := by
      exact mul_nonneg (le_of_lt hc_pos) (sq_nonneg _)
    exact sub_nonneg.mp (le_trans hterm_nonneg hdecrease)
  have hbelow : BddBelow (Set.range φ) := by
    -- Feasibility of all B1 iterates turns the objective lower bound into a real lower bound.
    refine ⟨FOpt, ?_⟩
    intro y hy
    rcases hy with ⟨k, rfl⟩
    exact
      proximal_gradient_toReal_ge_FOpt_of_isGLB
        (f := f)
        (g := g)
        (FOpt := FOpt)
        hFOpt
        hf_ne_bot
        hg_effective_domain_subset_interior_f_effective_domain
        (proximal_gradient_backtracking_iterate_mem_effective_domain_g
          (f := f)
          (g := g)
          (htraj := htraj)
          (hg_effective_domain_subset_interior_f_effective_domain :=
            hg_effective_domain_subset_interior_f_effective_domain)
          s γ η hB1 k)
  have hgap_tendsto_zero :
      Filter.Tendsto (fun k ↦ φ k - φ (k + 1)) Filter.atTop (nhds 0) :=
    objective_gap_tendsto_zero_of_antitone_bddBelow hanti hbelow
  have hscaled_tendsto_zero :
      Filter.Tendsto
        (fun k ↦ c * ‖G[s] (proximal_gradient_trajectory_iterate htraj k)‖ ^ (2 : ℕ))
        Filter.atTop
        (nhds 0) := by
    -- The scaled squared residuals are controlled by the vanishing one-step objective gaps.
    refine squeeze_zero ?_ ?_ hgap_tendsto_zero
    · intro k
      exact mul_nonneg (le_of_lt hc_pos) (sq_nonneg _)
    · intro k
      simpa [c, φ] using
        proximal_gradient_backtracking_B1_real_sufficient_decrease
          (f := f)
          (g := g)
          (Lf := Lf)
          (hf_ne_bot_local := hf_ne_bot)
          (hf_effective_domain_convex_local := hf_effective_domain_convex)
          (hg_subset_local := hg_effective_domain_subset_interior_f_effective_domain)
          (hf_smooth_local := hf_toReal_smooth_on_interior_effective_domain)
          (htraj := htraj)
          (s := s)
          (γ := γ)
          (η := η)
          (hB1 := hB1)
          (k := k)
  -- Convert the vanishing scaled squared residuals back to vanishing residual vectors.
  exact tendsto_zero_of_scaled_sq_norm_tendsto_zero hc_pos hscaled_tendsto_zero

section

-- Proof sketch: sum the sufficient-decrease inequality from Lemma 10.14 over `n = 0, ..., k`,
-- telescope the objective values, and bound the sum below by `(k + 1)` times the squared running
-- minimum residual norm.
/-- Theorem 10.15 (4): clause (c), constant-step case. If `FOpt` is the greatest lower bound of
`Set.range (f + g)`, then the squared complexity bound holds:
`M (k + 1) (min_{0 ≤ n ≤ k} ‖G_barL(x^n)‖)^2 ≤ F(x^0) - F_opt`, where
`M = ((barL : ℝ) - L_f / 2) / barL^2`. -/
theorem proximal_gradient_constant_stepsize_best_residual_norm_sq_le_objective_gap
    (hf_ne_bot : ∀ y, f y ≠ ⊥)
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f))
    (hf_toReal_smooth_on_interior_effective_domain :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)
    {x : ℕ → E} (barL : ProximalGradientConstantStepsizeParameter Lf)
    (htraj : is_proximal_gradient_trajectory f g x
      (Function.const ℕ barL))
    (hFOpt : IsGLB (Set.range F) (FOpt : EReal))
    (k : ℕ) :
    (((((barL : ℝ) - (Lf : ℝ) / 2) / ((barL : ℝ) ^ (2 : ℕ))) * (k + 1 : ℝ) *
        R[htraj; barL, k] ^ (2 : ℕ) :
        ℝ) : EReal) ≤
      F (x 0) - (FOpt : EReal) := by
  let c : ℝ := ((barL : ℝ) - (Lf : ℝ) / 2) / ((barL : ℝ) ^ (2 : ℕ))
  have hc_nonneg : 0 ≤ c := le_of_lt <| by
    dsimp [c]
    have hnum_pos : 0 < (barL : ℝ) - (Lf : ℝ) / 2 := by
      exact sub_pos.mpr barL.lower_bound
    have hden_pos : 0 < (barL : ℝ) ^ (2 : ℕ) := by
      exact pow_pos barL.1.2 2
    exact div_pos hnum_pos hden_pos
  by_cases hx0g : x 0 ∈ effective_domain g
  · have hprefix_mem :
        ∀ n, n ≤ k → x n ∈ effective_domain g := by
      intro n hn
      cases n with
      | zero =>
          simpa using hx0g
      | succ j =>
          exact
            proximal_gradient_positive_iterate_mem_effective_domain_g
              (f := f)
              (g := g)
              (Lf := Lf)
              (hf_ne_bot := hf_ne_bot)
              (hf_effective_domain_convex := hf_effective_domain_convex)
              (hg_effective_domain_subset_interior_f_effective_domain :=
                hg_effective_domain_subset_interior_f_effective_domain)
              (hf_toReal_smooth_on_interior_effective_domain :=
                hf_toReal_smooth_on_interior_effective_domain)
              (htraj := htraj)
              j
    have hsum_decrease :
        Finset.sum (Finset.range (k + 1))
            (fun n ↦ c * ‖G[barL] (proximal_gradient_trajectory_iterate htraj n)‖ ^ (2 : ℕ)) ≤
          Finset.sum (Finset.range (k + 1))
            (fun n ↦ (F (x n)).toReal - (F (x (n + 1))).toReal) := by
      -- Sum the real sufficient-decrease estimate over the whole prefix.
      refine Finset.sum_le_sum ?_
      intro n hn
      exact
        proximal_gradient_constant_stepsize_real_sufficient_decrease_of_mem_effective_domain_g
          (f := f)
          (g := g)
          (Lf := Lf)
          hf_ne_bot
          hf_effective_domain_convex
          hg_effective_domain_subset_interior_f_effective_domain
          hf_toReal_smooth_on_interior_effective_domain
          barL htraj n
          (hprefix_mem n (Nat.le_of_lt_succ (Finset.mem_range.mp hn)))
    have hprefix_best :
        c * (k + 1 : ℝ) * R[htraj; barL, k] ^ (2 : ℕ) ≤
          (F (x 0)).toReal - (F (x (k + 1))).toReal := by
      -- The source proof combines the prefix minimum estimate with the telescoping sum.
      calc
        c * (k + 1 : ℝ) * R[htraj; barL, k] ^ (2 : ℕ) ≤
            c * Finset.sum (Finset.range (k + 1))
              (fun n ↦ ‖G[barL] (proximal_gradient_trajectory_iterate htraj n)‖ ^ (2 : ℕ)) := by
          simpa [mul_assoc] using
            (mul_le_mul_of_nonneg_left
              (best_residual_sq_mul_prefix_length_le_sum
                (htraj := htraj)
                (d := barL)
                (k := k))
              hc_nonneg)
        _ = Finset.sum (Finset.range (k + 1))
              (fun n ↦ c * ‖G[barL] (proximal_gradient_trajectory_iterate htraj n)‖ ^ (2 : ℕ)) := by
          rw [Finset.mul_sum]
        _ ≤ Finset.sum (Finset.range (k + 1))
              (fun n ↦ (F (x n)).toReal - (F (x (n + 1))).toReal) := hsum_decrease
        _ = (F (x 0)).toReal - (F (x (k + 1))).toReal := by
          simpa using proximal_gradient_real_objective_telescope
            (fun n ↦ (F (x n)).toReal) k
    have htail_ge :
        FOpt ≤ (F (x (k + 1))).toReal := by
      exact
        proximal_gradient_toReal_ge_FOpt_of_isGLB
          (f := f)
          (g := g)
          (FOpt := FOpt)
          hFOpt
          hf_ne_bot
          hg_effective_domain_subset_interior_f_effective_domain
          (proximal_gradient_positive_iterate_mem_effective_domain_g
            (f := f)
            (g := g)
            (Lf := Lf)
            (hf_ne_bot := hf_ne_bot)
            (hf_effective_domain_convex := hf_effective_domain_convex)
            (hg_effective_domain_subset_interior_f_effective_domain :=
              hg_effective_domain_subset_interior_f_effective_domain)
            (hf_toReal_smooth_on_interior_effective_domain :=
              hf_toReal_smooth_on_interior_effective_domain)
            (htraj := htraj)
            k)
    have hreal :
        c * (k + 1 : ℝ) * R[htraj; barL, k] ^ (2 : ℕ) ≤
          (F (x 0)).toReal - FOpt := by
      nlinarith
    have hgap0 :
        ((((F (x 0)).toReal - FOpt : ℝ) : EReal)) =
          F (x 0) - (FOpt : EReal) := by
      exact
        proximal_gradient_objective_minus_FOpt_eq_coe_sub_toReal_of_mem_effective_domain_g
          (f := f)
          (g := g)
          (FOpt := FOpt)
          hf_ne_bot
          hg_effective_domain_subset_interior_f_effective_domain
          hx0g
    -- Convert the real prefix estimate back to the original `EReal` objective gap.
    rw [← hgap0]
    exact EReal.coe_le_coe_iff.mpr hreal
  · have hgx0_top : g (x 0) = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa using hx0g))
    have hFx0_top : F (x 0) = ⊤ := by
      rw [composite_model_objective_apply, hgx0_top]
      simpa [hf_ne_bot (x 0)]
    -- If the initial iterate is infeasible for `g`, then `F(x^0) = ⊤` and the estimate is trivial.
    rw [hFx0_top]
    exact le_top

-- Proof sketch: sum the B1 sufficient-decrease inequality from Lemma 10.14 over
-- `n = 0, ..., k`, telescope the objective values, and bound the sum below by `(k + 1)` times
-- the squared running minimum residual norm for the canonical B1 residual `G_s`.
/-- Theorem 10.15 (4): clause (c), backtracking-B1 case. If `FOpt` is the greatest lower bound of
`Set.range (f + g)`, then the squared complexity bound holds:
`M (k + 1) (min_{0 ≤ n ≤ k} ‖G_s(x^n)‖)^2 ≤ F(x^0) - F_opt`, where
`M = γ / max {s, η L_f / (2 (1 - γ))}`. -/
theorem proximal_gradient_backtracking_B1_best_residual_norm_sq_le_objective_gap
    (hf_ne_bot : ∀ y, f y ≠ ⊥)
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f))
    (hf_toReal_smooth_on_interior_effective_domain :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L)
    (s : PosReal) (γ : ProximalGradientBacktrackingDecreaseFraction)
    (η : ProximalGradientBacktrackingGrowthFactor)
    (hB1 : uses_proximal_gradient_backtracking_B1_rule
      f g hg_effective_domain_subset_interior_f_effective_domain x L htraj s γ η)
    (hFOpt : IsGLB (Set.range F) (FOpt : EReal))
    (k : ℕ) :
    (((γ : ℝ) / max (s : ℝ) (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ)))) *
        (k + 1 : ℝ) *
          R[htraj; s, k] ^ (2 : ℕ) :
        ℝ) : EReal) ≤
      F (x 0) - (FOpt : EReal) := by
  let c : ℝ := (γ : ℝ) / max (s : ℝ) (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ))))
  have hc_nonneg : 0 ≤ c := le_of_lt <| by
    dsimp [c]
    have hden_pos :
        0 < max (s : ℝ) (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ)))) := by
      exact lt_of_lt_of_le s.2 (le_max_left _ _)
    exact div_pos γ.1.2 hden_pos
  have hsum_decrease :
      Finset.sum (Finset.range (k + 1))
          (fun n ↦ c * ‖G[s] (proximal_gradient_trajectory_iterate htraj n)‖ ^ (2 : ℕ)) ≤
        Finset.sum (Finset.range (k + 1))
          (fun n ↦ (F (x n)).toReal - (F (x (n + 1))).toReal) := by
    -- Sum the B1 real sufficient-decrease estimate along the whole prefix.
    refine Finset.sum_le_sum ?_
    intro n hn
    simpa [c] using
      proximal_gradient_backtracking_B1_real_sufficient_decrease
        (f := f)
        (g := g)
        (Lf := Lf)
        (hf_ne_bot_local := hf_ne_bot)
        (hf_effective_domain_convex_local := hf_effective_domain_convex)
        (hg_subset_local := hg_effective_domain_subset_interior_f_effective_domain)
        (hf_smooth_local := hf_toReal_smooth_on_interior_effective_domain)
        (htraj := htraj)
        (s := s)
        (γ := γ)
        (η := η)
        (hB1 := hB1)
        (k := n)
  have hprefix_best :
      c * (k + 1 : ℝ) * R[htraj; s, k] ^ (2 : ℕ) ≤
        (F (x 0)).toReal - (F (x (k + 1))).toReal := by
    -- Combine the running-best estimate with the telescoping real sufficient-decrease sum.
    calc
      c * (k + 1 : ℝ) * R[htraj; s, k] ^ (2 : ℕ) ≤
          c * Finset.sum (Finset.range (k + 1))
            (fun n ↦ ‖G[s] (proximal_gradient_trajectory_iterate htraj n)‖ ^ (2 : ℕ)) := by
        simpa [mul_assoc] using
          (mul_le_mul_of_nonneg_left
            (best_residual_sq_mul_prefix_length_le_sum
              (htraj := htraj)
              (d := s)
              (k := k))
            hc_nonneg)
      _ = Finset.sum (Finset.range (k + 1))
            (fun n ↦ c * ‖G[s] (proximal_gradient_trajectory_iterate htraj n)‖ ^ (2 : ℕ)) := by
        rw [Finset.mul_sum]
      _ ≤ Finset.sum (Finset.range (k + 1))
            (fun n ↦ (F (x n)).toReal - (F (x (n + 1))).toReal) := hsum_decrease
      _ = (F (x 0)).toReal - (F (x (k + 1))).toReal := by
        simpa using proximal_gradient_real_objective_telescope
          (fun n ↦ (F (x n)).toReal) k
  have hx0g :
      x 0 ∈ effective_domain g :=
    proximal_gradient_backtracking_iterate_mem_effective_domain_g
      (f := f)
      (g := g)
      (htraj := htraj)
      (hg_effective_domain_subset_interior_f_effective_domain :=
        hg_effective_domain_subset_interior_f_effective_domain)
      s γ η hB1 0
  have htail_ge :
      FOpt ≤ (F (x (k + 1))).toReal := by
    exact
      proximal_gradient_toReal_ge_FOpt_of_isGLB
        (f := f)
        (g := g)
        (FOpt := FOpt)
        hFOpt
        hf_ne_bot
        hg_effective_domain_subset_interior_f_effective_domain
        (proximal_gradient_backtracking_iterate_mem_effective_domain_g
          (f := f)
          (g := g)
          (htraj := htraj)
          (hg_effective_domain_subset_interior_f_effective_domain :=
            hg_effective_domain_subset_interior_f_effective_domain)
          s γ η hB1 (k + 1))
  have hreal :
      c * (k + 1 : ℝ) * R[htraj; s, k] ^ (2 : ℕ) ≤
        (F (x 0)).toReal - FOpt := by
    nlinarith
  have hgap0 :
      ((((F (x 0)).toReal - FOpt : ℝ) : EReal)) =
        F (x 0) - (FOpt : EReal) := by
    exact
      proximal_gradient_objective_minus_FOpt_eq_coe_sub_toReal_of_mem_effective_domain_g
        (f := f)
        (g := g)
        (FOpt := FOpt)
        hf_ne_bot
        hg_effective_domain_subset_interior_f_effective_domain
        hx0g
  -- Convert the real prefix estimate back to the public `EReal`-valued objective gap.
  rw [← hgap0]
  exact EReal.coe_le_coe_iff.mpr hreal

end

section

variable [FiniteDimensional ℝ E]

omit hf_ne_bot hf_effective_domain_convex
  hg_effective_domain_subset_interior_f_effective_domain
  hf_toReal_smooth_on_interior_effective_domain in
/-- Helper for Theorem 10.15: the norm of one proximal-gradient displacement is exactly the norm
of the corresponding gradient mapping divided by the current stepsize. -/
lemma proximal_gradient_step_norm_eq_gradient_mapping_norm_div_stepsize
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L)
    (k : ℕ) :
    ‖x (k + 1) - x k‖ =
      ‖G[L k] (proximal_gradient_trajectory_iterate htraj k)‖ / (L k : ℝ) := by
  have hstep_eq :
      x (k + 1) =
        T[L k, f, g] (proximal_gradient_trajectory_iterate htraj k) := by
    -- Rewrite the realized successor to the canonical prox-gradient operator output.
    exact proximal_gradient_trajectory_succ_eq_prox_grad_operator (f := f) (g := g) htraj k
  have hprox_eq :
      T[L k, f, g] (proximal_gradient_trajectory_iterate htraj k) =
        x k -
          (1 / (L k : ℝ)) •
            G[L k] (proximal_gradient_trajectory_iterate htraj k) := by
    -- The Chapter 10 operator identity expresses the update as a scaled residual correction.
    simpa using
      prox_grad_operator_eq_sub_gradient_mapping
        (f := f)
        (g := g)
        (L := L k)
        (x := proximal_gradient_trajectory_iterate htraj k)
  calc
    ‖x (k + 1) - x k‖ =
        ‖T[L k, f, g] (proximal_gradient_trajectory_iterate htraj k) - x k‖ := by
      rw [hstep_eq]
    _ = ‖-((1 / (L k : ℝ)) • G[L k] (proximal_gradient_trajectory_iterate htraj k))‖ := by
      rw [hprox_eq]
      abel
    _ = ‖(1 / (L k : ℝ)) • G[L k] (proximal_gradient_trajectory_iterate htraj k)‖ := by
      simp
    _ = |1 / (L k : ℝ)| * ‖G[L k] (proximal_gradient_trajectory_iterate htraj k)‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ = ‖G[L k] (proximal_gradient_trajectory_iterate htraj k)‖ / (L k : ℝ) := by
      rw [abs_of_pos (one_div_pos.mpr (L k).2)]
      simp [div_eq_mul_inv, mul_comm]

omit hf_ne_bot hf_effective_domain_convex
  hg_effective_domain_subset_interior_f_effective_domain
  hf_toReal_smooth_on_interior_effective_domain in
/-- Helper for Theorem 10.15: every B1-accepted stepsize is at least the initial trial
stepsize `s`. -/
lemma proximal_gradient_backtracking_B1_stepsize_ge_initial_at_iterate
    {x : ℕ → E} {L : ℕ → PosReal}
    (hg_subset : effective_domain g ⊆ interior (effective_domain f))
    (htraj : is_proximal_gradient_trajectory f g x L)
    (s : PosReal) (γ : ProximalGradientBacktrackingDecreaseFraction)
    (η : ProximalGradientBacktrackingGrowthFactor)
    (hB1 : uses_proximal_gradient_backtracking_B1_rule
      f g hg_subset x L htraj s γ η)
    (k : ℕ) :
    (s : ℝ) ≤ (L k : ℝ) := by
  rcases hB1 k with ⟨_, i, _, hLk⟩
  -- Unfold the accepted B1 trial stepsize and use `η > 1` to bound `η^i` below by `1`.
  rw [hLk, proximal_gradient_backtracking_trial_stepsize_coe]
  have hpow_ge_one : (1 : ℝ) ≤ (η : ℝ) ^ i :=
    one_le_pow₀ (le_of_lt η.2)
  have hs_nonneg : 0 ≤ (s : ℝ) := le_of_lt s.2
  calc
    (s : ℝ) = (s : ℝ) * 1 := by ring
    _ ≤ (s : ℝ) * (η : ℝ) ^ i := by
      exact mul_le_mul_of_nonneg_left hpow_ge_one hs_nonneg

omit hf_ne_bot hf_effective_domain_convex
  hg_effective_domain_subset_interior_f_effective_domain
  hf_toReal_smooth_on_interior_effective_domain in
/-- Helper for Theorem 10.15: residual decay for the constant-step method forces the actual
displacements `x^(k+1) - x^k` to vanish. -/
lemma proximal_gradient_constant_stepsize_step_tendsto_zero
    {x : ℕ → E} (barL : ProximalGradientConstantStepsizeParameter Lf)
    (htraj : is_proximal_gradient_trajectory f g x
      (Function.const ℕ barL))
    (hres :
      Filter.Tendsto
        (fun k ↦ G[barL] (proximal_gradient_trajectory_iterate htraj k))
        Filter.atTop
        (nhds 0)) :
    Filter.Tendsto (fun k ↦ x (k + 1) - x k) Filter.atTop (nhds 0) := by
  have hstep_eq :
      (fun k ↦ x (k + 1) - x k) =
        fun k ↦
          (-(1 / (barL : ℝ))) •
            G[barL] (proximal_gradient_trajectory_iterate htraj k) := by
    ext k
    -- Route correction: work with the explicit update `x^(k+1) - x^k = -(1 / barL) G_barL(x^k)`
    -- instead of trying to infer vanishing steps indirectly from objective descent.
    rw [proximal_gradient_trajectory_succ_eq_prox_grad_operator (f := f) (g := g) htraj k]
    simp only [Function.const_apply]
    rw [prox_grad_operator_eq_sub_gradient_mapping
      (f := f)
      (g := g)
      (L := barL)
      (x := proximal_gradient_trajectory_iterate htraj k)]
    change
      x k -
          (1 / (barL : ℝ)) •
            G[barL] (proximal_gradient_trajectory_iterate htraj k) -
          x k =
        -(1 / (barL : ℝ)) •
          G[barL] (proximal_gradient_trajectory_iterate htraj k)
    abel_nf
    simp [smul_smul]
  -- Scalar multiplication preserves convergence of the residual sequence to `0`.
  rw [hstep_eq]
  simpa using hres.const_smul (-(1 / (barL : ℝ)))

omit hf_ne_bot hf_effective_domain_convex
  hg_effective_domain_subset_interior_f_effective_domain
  hf_toReal_smooth_on_interior_effective_domain in
/-- Helper for Theorem 10.15: residual decay for a B1 trajectory forces the actual displacements
`x^(k+1) - x^k` to vanish. -/
lemma proximal_gradient_backtracking_B1_step_tendsto_zero
    {x : ℕ → E} {L : ℕ → PosReal}
    (hg_subset : effective_domain g ⊆ interior (effective_domain f))
    (htraj : is_proximal_gradient_trajectory f g x L)
    (s : PosReal) (γ : ProximalGradientBacktrackingDecreaseFraction)
    (η : ProximalGradientBacktrackingGrowthFactor)
    (hB1 : uses_proximal_gradient_backtracking_B1_rule
      f g hg_subset x L htraj s γ η)
    (hres :
      Filter.Tendsto
        (fun k ↦ G[s] (proximal_gradient_trajectory_iterate htraj k))
        Filter.atTop
        (nhds 0)) :
    Filter.Tendsto (fun k ↦ x (k + 1) - x k) Filter.atTop (nhds 0) := by
  have hratio_tendsto_zero :
      Filter.Tendsto
        (fun k ↦ ‖G[s] (proximal_gradient_trajectory_iterate htraj k)‖ / (s : ℝ))
        Filter.atTop
        (nhds 0) := by
    have hres_norm :
        Filter.Tendsto
          (fun k ↦ ‖G[s] (proximal_gradient_trajectory_iterate htraj k)‖)
          Filter.atTop
          (nhds 0) := by
      simpa using hres.norm
    -- Divide the vanishing residual norm by the fixed positive stepsize `s`.
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hres_norm.const_mul (1 / (s : ℝ))
  have hstep_norm_tendsto_zero :
      Filter.Tendsto (fun k ↦ ‖x (k + 1) - x k‖) Filter.atTop (nhds 0) := by
    -- Compare each accepted-step displacement with the baseline residual `G_s(x^k) / s`.
    refine squeeze_zero ?_ ?_ hratio_tendsto_zero
    · intro k
      exact norm_nonneg _
    · intro k
      have hstep_eq :=
        proximal_gradient_step_norm_eq_gradient_mapping_norm_div_stepsize
          htraj
          k
      have hs_le_Lk :
          (s : ℝ) ≤ (L k : ℝ) :=
        proximal_gradient_backtracking_B1_stepsize_ge_initial_at_iterate
          hg_subset
          htraj
          s
          γ
          η
          hB1
          k
      have hratio_le :
          ‖G[L k] (proximal_gradient_trajectory_iterate htraj k)‖ / (L k : ℝ) ≤
            ‖G[s] (proximal_gradient_trajectory_iterate htraj k)‖ / (s : ℝ) :=
        (gradient_mapping_norm_div_stepsize_antitone
          (f := f)
          (g := g)
          (proximal_gradient_trajectory_iterate htraj k))
          hs_le_Lk
      simpa [hstep_eq] using hratio_le
  -- Convert norm convergence back to vector convergence.
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa using hstep_norm_tendsto_zero

omit hf_ne_bot hf_effective_domain_convex
  hg_effective_domain_subset_interior_f_effective_domain
  hf_toReal_smooth_on_interior_effective_domain in
/-- Helper for Theorem 10.15: if a subsequence converges to `xBar` and the full trajectory has
vanishing successive displacements, then the shifted subsequence converges to the same limit. -/
lemma subseq_succ_tendsto_of_step_tendsto_zero
    {x : ℕ → E} {ψ : ℕ → ℕ} {xBar : E}
    (hψmono : StrictMono ψ)
    (hψtendsto : Filter.Tendsto (fun n ↦ x (ψ n)) Filter.atTop (nhds xBar))
    (hstep :
      Filter.Tendsto (fun k ↦ x (k + 1) - x k) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n ↦ x (ψ n + 1)) Filter.atTop (nhds xBar) := by
  have hstep_subseq :
      Filter.Tendsto (fun n ↦ x (ψ n + 1) - x (ψ n)) Filter.atTop (nhds 0) := by
    simpa using hstep.comp hψmono.tendsto_atTop
  have hsum :
      Filter.Tendsto
        (fun n ↦ x (ψ n) + (x (ψ n + 1) - x (ψ n)))
        Filter.atTop
        (nhds (xBar + 0)) :=
    hψtendsto.add hstep_subseq
  -- Rewrite the source sequence as the shifted subsequence and collapse the limit `xBar + 0`.
  convert hsum using 1
  · ext n
    abel
  · simp

omit hf_ne_bot hf_effective_domain_convex
  hg_effective_domain_subset_interior_f_effective_domain
  hf_toReal_smooth_on_interior_effective_domain in
/-- Helper for Theorem 10.15: lower semicontinuity bounds the value at the limit point by the
`liminf` along any convergent sequence. -/
private lemma lowerSemicontinuous_value_le_liminf_along_sequence
    {h : E → EReal} (hclosed : LowerSemicontinuous h) {z : ℕ → E} {xBar : E}
    (hz : Filter.Tendsto z Filter.atTop (nhds xBar)) :
    h xBar ≤ Filter.liminf (fun n ↦ h (z n)) Filter.atTop := by
  -- Compare the neighborhood-filter `liminf` at `xBar` with the mapped sequence filter.
  calc
    h xBar ≤ Filter.liminf h (nhds xBar) := hclosed.le_liminf xBar
    _ ≤ Filter.liminf h (Filter.map z Filter.atTop) := Filter.liminf_le_liminf_of_le hz
    _ = Filter.liminf (fun n ↦ h (z n)) Filter.atTop := by
      rw [← Filter.liminf_comp]
      rfl

omit hf_ne_bot hf_effective_domain_convex
  hg_effective_domain_subset_interior_f_effective_domain
  hf_toReal_smooth_on_interior_effective_domain in
/-- Helper for Theorem 10.15: an eventual upper bound by a constant forces the `liminf` to stay
below that constant. -/
private lemma liminf_le_constant_of_eventually_le_ereal
    {u : ℕ → EReal} {c : EReal} (huc : ∀ᶠ k in Filter.atTop, u k ≤ c) :
    Filter.liminf u Filter.atTop ≤ c := by
  -- Any eventual lower bound for `u` must eventually lie below the same constant.
  exact Filter.liminf_le_of_le (f := Filter.atTop) (u := u) (a := c) (hf := by isBoundedDefault)
    fun b hb ↦ by
    rcases (hb.and huc).exists with ⟨k, hbk, hkc⟩
    exact le_trans hbk hkc

omit hf_ne_bot hf_effective_domain_convex
  hg_effective_domain_subset_interior_f_effective_domain
  hf_toReal_smooth_on_interior_effective_domain in
/-- Helper for Theorem 10.15: if a convergent sequence has an eventual finite upper bound for the
regularizer values, then the limit point lies in `effective_domain g`. -/
lemma effective_domain_mem_of_tendsto_and_eventually_upper_bound
    {z : ℕ → E} {xBar : E} {c : ℝ}
    (hz : Filter.Tendsto z Filter.atTop (nhds xBar))
    (hupper : ∀ᶠ n in Filter.atTop, g (z n) ≤ (((c : ℝ) : EReal))) :
    xBar ∈ effective_domain g := by
  let hclosed : LowerSemicontinuous g := Fact.out
  have hxBar_le_liminf :
      g xBar ≤ Filter.liminf (fun n ↦ g (z n)) Filter.atTop :=
    lowerSemicontinuous_value_le_liminf_along_sequence
      (h := g)
      hclosed
      hz
  have hliminf_le :
      Filter.liminf (fun n ↦ g (z n)) Filter.atTop ≤ (((c : ℝ) : EReal)) :=
    liminf_le_constant_of_eventually_le_ereal hupper
  -- Chaining the lower-semicontinuity bound with the tail upper bound shows `g xBar < ⊤`.
  exact mem_effective_domain.mpr <|
    lt_of_le_of_lt (le_trans hxBar_le_liminf hliminf_le) (by simp)

omit hf_ne_bot hf_effective_domain_convex
  hg_effective_domain_subset_interior_f_effective_domain
  hf_toReal_smooth_on_interior_effective_domain in
/-- Helper for Theorem 10.15: once both the original and shifted subsequences converge to the same
cluster point, the support inequality gives an eventual finite upper bound on the shifted
regularizer values. -/
lemma proximal_gradient_shifted_subseq_regularizer_eventually_le_const
    (hf_ne_bot : ∀ y, f y ≠ ⊥)
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f))
    (hf_toReal_smooth_on_interior_effective_domain :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L)
    {ψ : ℕ → ℕ} {xBar yRef : E} {C : ℝ}
    (hψtendsto : Filter.Tendsto (fun n ↦ x (ψ n)) Filter.atTop (nhds xBar))
    (hψsucc_tendsto : Filter.Tendsto (fun n ↦ x (ψ n + 1)) Filter.atTop (nhds xBar))
    (hyRef : yRef ∈ effective_domain g)
    (hL_bound : ∀ n, (L (ψ n) : ℝ) ≤ C) :
    ∃ B : ℝ, ∀ᶠ n in Filter.atTop, g (x (ψ n + 1)) ≤ (((B : ℝ) : EReal)) := by
  -- Route correction: follow the source proof literally via the support inequality at each
  -- shifted iterate, then bound its three factors on a tail before converting back to `EReal`.
  let gradFun : E → ℝ := fun y ↦ (f y).toReal
  have hyRef_int : yRef ∈ interior (effective_domain f) :=
    hg_effective_domain_subset_interior_f_effective_domain hyRef
  have hsmooth := hf_toReal_smooth_on_interior_effective_domain
  rw [is_l_smooth_on_iff_forall_norm_sub_le] at hsmooth
  have hpointwise_support :
      ∀ n,
        (g (x (ψ n + 1))).toReal ≤
          (g yRef).toReal +
            (‖G[L (ψ n)] (proximal_gradient_trajectory_iterate htraj (ψ n))‖ +
                ‖∇ gradFun (x (ψ n))‖) *
              ‖yRef - x (ψ n + 1)‖ := by
    intro n
    let xk : interior (effective_domain f) := proximal_gradient_trajectory_iterate htraj (ψ n)
    have hsupport :=
      (gradient_mapping_support_ineq_real f g (L (ψ n)) xk).2 yRef hyRef
    have hsucc :
        T[L (ψ n), f, g] xk = x (ψ n + 1) := by
      simpa [xk] using
        (proximal_gradient_trajectory_succ_eq_prox_grad_operator
          (f := f) (g := g) htraj (ψ n)).symm
    let u : E := G[L (ψ n)] xk - ∇ gradFun (x (ψ n))
    let w : E := yRef - x (ψ n + 1)
    have hinner :
        inner ℝ u w ≤ (g yRef).toReal - (g (x (ψ n + 1))).toReal := by
      simpa [gradFun, xk, u, w, hsucc] using hsupport
    -- Bound the support-inequality inner product by the product of the residual-plus-gradient norm
    -- and the distance to the fixed anchor `yRef`.
    have hneg_inner :
        -inner ℝ u w ≤ ‖u‖ * ‖w‖ := by
      simpa using real_inner_le_norm (-u) w
    have hu_bound :
        ‖u‖ ≤
          ‖G[L (ψ n)] (proximal_gradient_trajectory_iterate htraj (ψ n))‖ +
            ‖∇ gradFun (x (ψ n))‖ := by
      simpa [gradFun, xk, u] using
        norm_sub_le
          (G[L (ψ n)] (proximal_gradient_trajectory_iterate htraj (ψ n)))
          (∇ gradFun (x (ψ n)))
    have hprod_bound :
        ‖u‖ * ‖w‖ ≤
          (‖G[L (ψ n)] (proximal_gradient_trajectory_iterate htraj (ψ n))‖ +
              ‖∇ gradFun (x (ψ n))‖) *
            ‖w‖ := by
      gcongr
    have hneg_inner' :
        -inner ℝ u w ≤
          (‖G[L (ψ n)] (proximal_gradient_trajectory_iterate htraj (ψ n))‖ +
              ‖∇ gradFun (x (ψ n))‖) *
            ‖w‖ := by
      exact le_trans hneg_inner hprod_bound
    linarith
  -- The shifted displacements tend to zero because both subsequences converge to the same limit.
  have hshift_step_tendsto_zero :
      Filter.Tendsto (fun n ↦ x (ψ n + 1) - x (ψ n)) Filter.atTop (nhds 0) := by
    simpa using hψsucc_tendsto.sub hψtendsto
  have hshift_step_norm_tendsto_zero :
      Filter.Tendsto (fun n ↦ ‖x (ψ n + 1) - x (ψ n)‖) Filter.atTop (nhds 0) := by
    simpa using hshift_step_tendsto_zero.norm
  have hshift_step_eventually_le_one :
      ∀ᶠ n in Filter.atTop, ‖x (ψ n + 1) - x (ψ n)‖ ≤ 1 := by
    have hs : Set.Iic (1 : ℝ) ∈ nhds (0 : ℝ) := Iic_mem_nhds (by norm_num)
    simpa [Set.mem_Iic] using hshift_step_norm_tendsto_zero.eventually hs
  -- Convert the small-step tail bound into a uniform bound for the gradient-mapping norms.
  have hresidual_eventually_le_C :
      ∀ᶠ n in Filter.atTop,
        ‖G[L (ψ n)] (proximal_gradient_trajectory_iterate htraj (ψ n))‖ ≤ C := by
    filter_upwards [hshift_step_eventually_le_one] with n hn
    have hstep_eq :=
      proximal_gradient_step_norm_eq_gradient_mapping_norm_div_stepsize
        (f := f)
        (g := g)
        htraj
        (ψ n)
    have hresidual_eq :
        ‖G[L (ψ n)] (proximal_gradient_trajectory_iterate htraj (ψ n))‖ =
          (L (ψ n) : ℝ) * ‖x (ψ n + 1) - x (ψ n)‖ := by
      have hstep_eq' := hstep_eq
      rw [eq_div_iff (show (L (ψ n) : ℝ) ≠ 0 by exact (L (ψ n)).2.ne')] at hstep_eq'
      simpa [mul_comm] using hstep_eq'.symm
    calc
      ‖G[L (ψ n)] (proximal_gradient_trajectory_iterate htraj (ψ n))‖ =
          (L (ψ n) : ℝ) * ‖x (ψ n + 1) - x (ψ n)‖ := hresidual_eq
      _ ≤ (L (ψ n) : ℝ) * 1 := by
        have hL_nonneg : 0 ≤ (L (ψ n) : ℝ) := le_of_lt (L (ψ n)).2
        gcongr
      _ = (L (ψ n) : ℝ) := by ring
      _ ≤ C := hL_bound n
  have hψ_norm_tendsto_zero :
      Filter.Tendsto (fun n ↦ ‖x (ψ n) - xBar‖) Filter.atTop (nhds 0) := by
    simpa [dist_eq_norm] using (tendsto_iff_norm_sub_tendsto_zero.mp hψtendsto)
  have hψ_eventually_le_one :
      ∀ᶠ n in Filter.atTop, ‖x (ψ n) - xBar‖ ≤ 1 := by
    have hs : Set.Iic (1 : ℝ) ∈ nhds (0 : ℝ) := Iic_mem_nhds (by norm_num)
    simpa [Set.mem_Iic] using hψ_norm_tendsto_zero.eventually hs
  have hψsucc_norm_tendsto_zero :
      Filter.Tendsto (fun n ↦ ‖x (ψ n + 1) - xBar‖) Filter.atTop (nhds 0) := by
    simpa [dist_eq_norm] using (tendsto_iff_norm_sub_tendsto_zero.mp hψsucc_tendsto)
  have hψsucc_eventually_le_one :
      ∀ᶠ n in Filter.atTop, ‖x (ψ n + 1) - xBar‖ ≤ 1 := by
    have hs : Set.Iic (1 : ℝ) ∈ nhds (0 : ℝ) := Iic_mem_nhds (by norm_num)
    simpa [Set.mem_Iic] using hψsucc_norm_tendsto_zero.eventually hs
  -- Bound the gradient term by comparing each iterate with the fixed feasible anchor `yRef`.
  have hgradient_eventually_bound :
      ∀ᶠ n in Filter.atTop,
        ‖∇ gradFun (x (ψ n))‖ ≤
          ‖∇ gradFun yRef‖ + (Lf : ℝ) * (‖xBar - yRef‖ + 1) := by
    have hdist_to_anchor :
        ∀ᶠ n in Filter.atTop, ‖x (ψ n) - yRef‖ ≤ ‖xBar - yRef‖ + 1 := by
      filter_upwards [hψ_eventually_le_one] with n hn
      have hdecomp :
          x (ψ n) - yRef = (x (ψ n) - xBar) + (xBar - yRef) := by
        abel
      calc
        ‖x (ψ n) - yRef‖ = ‖(x (ψ n) - xBar) + (xBar - yRef)‖ := by rw [hdecomp]
        _ ≤ ‖x (ψ n) - xBar‖ + ‖xBar - yRef‖ := norm_add_le _ _
        _ ≤ 1 + ‖xBar - yRef‖ := by gcongr
        _ = ‖xBar - yRef‖ + 1 := by ring
    have hLf_nonneg : 0 ≤ (Lf : ℝ) := by positivity
    filter_upwards [hdist_to_anchor] with n hn
    have hxk_int : x (ψ n) ∈ interior (effective_domain f) :=
      (proximal_gradient_trajectory_iterate htraj (ψ n)).property
    have hgrad_diff :
        ‖∇ gradFun (x (ψ n)) - ∇ gradFun yRef‖ ≤
          (Lf : ℝ) * ‖x (ψ n) - yRef‖ :=
      hsmooth.2 (x (ψ n)) hxk_int yRef hyRef_int
    have htriangle :
        ‖∇ gradFun (x (ψ n))‖ ≤
          ‖∇ gradFun (x (ψ n)) - ∇ gradFun yRef‖ + ‖∇ gradFun yRef‖ := by
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
        (norm_add_le (∇ gradFun (x (ψ n)) - ∇ gradFun yRef) (∇ gradFun yRef))
    nlinarith
  have hdistance_eventually_bound :
      ∀ᶠ n in Filter.atTop, ‖yRef - x (ψ n + 1)‖ ≤ ‖yRef - xBar‖ + 1 := by
    filter_upwards [hψsucc_eventually_le_one] with n hn
    have hdecomp :
        yRef - x (ψ n + 1) = (yRef - xBar) + (xBar - x (ψ n + 1)) := by
      abel
    calc
      ‖yRef - x (ψ n + 1)‖ = ‖(yRef - xBar) + (xBar - x (ψ n + 1))‖ := by rw [hdecomp]
      _ ≤ ‖yRef - xBar‖ + ‖xBar - x (ψ n + 1)‖ := norm_add_le _ _
      _ = ‖yRef - xBar‖ + ‖x (ψ n + 1) - xBar‖ := by
        congr 1
        exact norm_sub_rev _ _
      _ ≤ ‖yRef - xBar‖ + 1 := by gcongr
  have hC_nonneg : 0 ≤ C := by
    exact le_trans (le_of_lt (L (ψ 0)).2) (hL_bound 0)
  let Rf : ℝ := ‖∇ gradFun yRef‖ + (Lf : ℝ) * (‖xBar - yRef‖ + 1)
  have hRf_nonneg : 0 ≤ Rf := by
    dsimp [Rf]
    positivity
  let B : ℝ := (g yRef).toReal + (C + Rf) * (‖yRef - xBar‖ + 1)
  refine ⟨B, ?_⟩
  filter_upwards [hresidual_eventually_le_C, hgradient_eventually_bound, hdistance_eventually_bound]
    with n hres hgrad hdist
  have hxsuccg :
      x (ψ n + 1) ∈ effective_domain g := by
    rw [proximal_gradient_trajectory_succ_eq_prox_grad_operator (f := f) (g := g) htraj (ψ n)]
    exact
      prox_grad_operator_mem_effective_domain_g
        (f := f)
        (g := g)
        (L := L (ψ n))
        (x := proximal_gradient_trajectory_iterate htraj (ψ n))
  have hxsucc_val :
      g (x (ψ n + 1)) = ((((g (x (ψ n + 1))).toReal : ℝ)) : EReal) := by
    exact
      (EReal.coe_toReal (mem_effective_domain.mp hxsuccg).ne
        (‹IsProperExtendedRealFunction g›.ne_bot _)).symm
  have hsum_bound :
      ‖G[L (ψ n)] (proximal_gradient_trajectory_iterate htraj (ψ n))‖ +
          ‖∇ gradFun (x (ψ n))‖ ≤
        C + Rf := by
    linarith
  have hdist_nonneg : 0 ≤ ‖yRef - x (ψ n + 1)‖ := norm_nonneg _
  have hcoeff_nonneg : 0 ≤ C + Rf := add_nonneg hC_nonneg hRf_nonneg
  have hprod_bound :
      (‖G[L (ψ n)] (proximal_gradient_trajectory_iterate htraj (ψ n))‖ +
          ‖∇ gradFun (x (ψ n))‖) *
          ‖yRef - x (ψ n + 1)‖ ≤
        (C + Rf) * (‖yRef - xBar‖ + 1) := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hdist hcoeff_nonneg)
    exact mul_le_mul_of_nonneg_right hsum_bound hdist_nonneg
  have hreal :
      (g (x (ψ n + 1))).toReal ≤ B := by
    have hsupport := hpointwise_support n
    dsimp [B] at *
    linarith
  rw [hxsucc_val]
  exact EReal.coe_le_coe_iff.mpr hreal

omit hf_ne_bot hf_effective_domain_convex
  hg_effective_domain_subset_interior_f_effective_domain
  hf_toReal_smooth_on_interior_effective_domain in
/-- Helper for Theorem 10.15: the source-faithful domain bridge for cluster points combines the
shifted-sequence regularizer bound with lower semicontinuity of `g`. -/
lemma proximal_gradient_cluster_point_mem_effective_domain_g
    (hf_ne_bot : ∀ y, f y ≠ ⊥)
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f))
    (hf_toReal_smooth_on_interior_effective_domain :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L)
    {ψ : ℕ → ℕ} {xBar yRef : E} {C : ℝ}
    (hψtendsto : Filter.Tendsto (fun n ↦ x (ψ n)) Filter.atTop (nhds xBar))
    (hψsucc_tendsto : Filter.Tendsto (fun n ↦ x (ψ n + 1)) Filter.atTop (nhds xBar))
    (hyRef : yRef ∈ effective_domain g)
    (hL_bound : ∀ n, (L (ψ n) : ℝ) ≤ C) :
    xBar ∈ effective_domain g := by
  -- First obtain the eventual finite upper bound for the shifted regularizer values from the
  -- source-faithful support-inequality route.
  rcases proximal_gradient_shifted_subseq_regularizer_eventually_le_const
      (f := f)
      (g := g)
      (Lf := Lf)
      hf_ne_bot
      hg_effective_domain_subset_interior_f_effective_domain
      hf_toReal_smooth_on_interior_effective_domain
      htraj
      hψtendsto
      hψsucc_tendsto
      hyRef
      hL_bound with
    ⟨B, hupper⟩
  -- Lower semicontinuity now transfers that tail bound to the limit point.
  exact
    effective_domain_mem_of_tendsto_and_eventually_upper_bound
      (g := g)
      (z := fun n ↦ x (ψ n + 1))
      (xBar := xBar)
      (c := B)
      hψsucc_tendsto
      hupper

omit hf_ne_bot hf_effective_domain_convex
  hg_effective_domain_subset_interior_f_effective_domain
  hf_toReal_smooth_on_interior_effective_domain in
/-- Helper for Theorem 10.15: once a cluster point lies in `interior (effective_domain f)`, the
Lipschitz continuity of the gradient mapping and residual convergence force the residual to vanish
at that point. -/
lemma cluster_point_gradient_mapping_eq_zero_of_lipschitz
    (hf_ne_bot : ∀ y, f y ≠ ⊥)
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (hg_effective_domain_subset_interior_f_effective_domain :
      effective_domain g ⊆ interior (effective_domain f))
    (hf_toReal_smooth_on_interior_effective_domain :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L)
    (d : PosReal) {xBar : E}
    (hxBar : MapClusterPt xBar Filter.atTop x)
    (hxBar_int : xBar ∈ interior (effective_domain f))
    (hres :
      Filter.Tendsto
        (fun k ↦ G[d] (proximal_gradient_trajectory_iterate htraj k))
        Filter.atTop
        (nhds 0)) :
    G[d] ⟨xBar, hxBar_int⟩ = 0 := by
  obtain ⟨ψ, hψmono, hψtendsto⟩ := MapClusterPt.tendsto_subseq hxBar
  have hLip :=
    gradient_mapping_lipschitz
      (f := f)
      (g := g)
      (Lf := Lf)
      hf_toReal_smooth_on_interior_effective_domain
      d
  have hsubseq_res :
      Filter.Tendsto
        (fun n ↦ G[d] (proximal_gradient_trajectory_iterate htraj (ψ n)))
        Filter.atTop
        (nhds 0) :=
    hres.comp hψmono.tendsto_atTop
  have hsubseq_res_norm :
      Filter.Tendsto
        (fun n ↦ ‖G[d] (proximal_gradient_trajectory_iterate htraj (ψ n))‖)
        Filter.atTop
        (nhds 0) := by
    simpa using hsubseq_res.norm
  have hdist_tendsto_zero :
      Filter.Tendsto (fun n ↦ ‖x (ψ n) - xBar‖) Filter.atTop (nhds 0) := by
    simpa [dist_eq_norm] using
      (tendsto_iff_norm_sub_tendsto_zero.mp hψtendsto)
  have hcluster_rhs_tendsto_zero :
      Filter.Tendsto
        (fun n ↦ (((2 : ℝ) * (d : ℝ)) + (Lf : ℝ)) * ‖x (ψ n) - xBar‖ +
          ‖G[d] (proximal_gradient_trajectory_iterate htraj (ψ n))‖)
        Filter.atTop
        (nhds 0) := by
    -- Both terms in the textbook estimate vanish along the extracted subsequence.
    simpa using
      (hdist_tendsto_zero.const_mul (((2 : ℝ) * (d : ℝ)) + (Lf : ℝ))).add
        hsubseq_res_norm
  have hconst_norm_tendsto_zero :
      Filter.Tendsto
        (fun _ : ℕ ↦ ‖G[d] ⟨xBar, hxBar_int⟩‖)
        Filter.atTop
        (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hcluster_rhs_tendsto_zero ?_ ?_
    · intro n
      exact norm_nonneg _
    · intro n
      have hdist :
          ‖G[d] ⟨xBar, hxBar_int⟩ -
              G[d] (proximal_gradient_trajectory_iterate htraj (ψ n))‖ ≤
            (((2 : ℝ) * (d : ℝ)) + (Lf : ℝ)) * ‖x (ψ n) - xBar‖ := by
        simpa [Subtype.dist_eq, dist_eq_norm, norm_sub_rev] using
          hLip.dist_le_mul
            ⟨xBar, hxBar_int⟩
            (proximal_gradient_trajectory_iterate htraj (ψ n))
      have htriangle :
          ‖G[d] ⟨xBar, hxBar_int⟩‖ ≤
            ‖G[d] ⟨xBar, hxBar_int⟩ -
                G[d] (proximal_gradient_trajectory_iterate htraj (ψ n))‖ +
              ‖G[d] (proximal_gradient_trajectory_iterate htraj (ψ n))‖ := by
        -- Rewrite the residual at `xBar` as a difference plus the subsequence residual.
        simpa [sub_eq_add_neg, add_assoc] using
          (norm_add_le
            (G[d] ⟨xBar, hxBar_int⟩ -
              G[d] (proximal_gradient_trajectory_iterate htraj (ψ n)))
            (G[d] (proximal_gradient_trajectory_iterate htraj (ψ n))))
      calc
        ‖G[d] ⟨xBar, hxBar_int⟩‖ ≤
            ‖G[d] ⟨xBar, hxBar_int⟩ -
                G[d] (proximal_gradient_trajectory_iterate htraj (ψ n))‖ +
              ‖G[d] (proximal_gradient_trajectory_iterate htraj (ψ n))‖ := htriangle
        _ ≤ (((2 : ℝ) * (d : ℝ)) + (Lf : ℝ)) * ‖x (ψ n) - xBar‖ +
              ‖G[d] (proximal_gradient_trajectory_iterate htraj (ψ n))‖ := by
          simpa [add_assoc, add_left_comm, add_comm] using
            add_le_add_right
              hdist
              ‖G[d] (proximal_gradient_trajectory_iterate htraj (ψ n))‖
  have hnorm_zero :
      ‖G[d] ⟨xBar, hxBar_int⟩‖ = 0 := by
    exact tendsto_nhds_unique tendsto_const_nhds hconst_norm_tendsto_zero
  exact norm_eq_zero.mp hnorm_zero

-- Proof sketch: let `xBar` be a cluster point of the trajectory. The Lipschitz estimate from
-- Lemma 10.10 controls `‖G_d(xBar) - G_d(x^{k_j})‖` along a subsequence converging to `xBar`, and
-- clause (3) gives `G_d(x^{k_j}) → 0`; hence `G_d(xBar) = 0`. Theorem 10.7 then turns vanishing
-- of the gradient mapping into stationarity.
/-- Theorem 10.15 (5): clause (d), constant-step case. If `FOpt` is the greatest lower bound of
`Set.range (f + g)`, then every sequential limit point of a proximal-gradient trajectory
generated with the constant stepsize `barL ∈ (L_f / 2, ∞)` is a stationary point of the
composite problem `min_x {f(x) + g(x)}`. -/
theorem proximal_gradient_constant_stepsize_cluster_point_is_stationary
    {x : ℕ → E} (barL : ProximalGradientConstantStepsizeParameter Lf)
    (htraj : is_proximal_gradient_trajectory f g x
      (Function.const ℕ barL))
    (hFOpt : IsGLB (Set.range F) (FOpt : EReal))
    {xBar : E} (hxBar : MapClusterPt xBar Filter.atTop x) :
    is_stationary_point f g xBar := by
  -- Route correction: reduce to the source-faithful domain bridge
  -- `xBar ∈ effective_domain g`, then finish by residual vanishing and
  -- `gradient_mapping_eq_zero_iff_is_stationary_point`.
  obtain ⟨ψ, hψmono, hψtendsto⟩ := MapClusterPt.tendsto_subseq hxBar
  -- Clause (b) already gives residual decay for the constant-step regime.
  have hres :
      Filter.Tendsto
        (fun k ↦ G[barL] (proximal_gradient_trajectory_iterate htraj k))
        Filter.atTop
        (nhds 0) :=
    proximal_gradient_constant_stepsize_residual_tendsto_zero
      (f := f)
      (g := g)
      (Lf := Lf)
      hf_ne_bot
      hf_effective_domain_convex
      hg_effective_domain_subset_interior_f_effective_domain
      hf_toReal_smooth_on_interior_effective_domain
      barL
      htraj
      hFOpt
  -- Residual decay forces the trajectory steps to vanish, so the shifted subsequence has the
  -- same limit as the original cluster subsequence.
  have hstep :
      Filter.Tendsto (fun k ↦ x (k + 1) - x k) Filter.atTop (nhds 0) :=
    proximal_gradient_constant_stepsize_step_tendsto_zero
      (f := f)
      (g := g)
      (Lf := Lf)
      barL
      htraj
      hres
  have hψsucc_tendsto :
      Filter.Tendsto (fun n ↦ x (ψ n + 1)) Filter.atTop (nhds xBar) :=
    subseq_succ_tendsto_of_step_tendsto_zero
      (x := x)
      (ψ := ψ)
      (xBar := xBar)
      hψmono
      hψtendsto
      hstep
  have hyRef : x 1 ∈ effective_domain g :=
    proximal_gradient_positive_iterate_mem_effective_domain_g
      (f := f)
      (g := g)
      (Lf := Lf)
      (hf_ne_bot := hf_ne_bot)
      (hf_effective_domain_convex := hf_effective_domain_convex)
      (hg_effective_domain_subset_interior_f_effective_domain :=
        hg_effective_domain_subset_interior_f_effective_domain)
      (hf_toReal_smooth_on_interior_effective_domain :=
        hf_toReal_smooth_on_interior_effective_domain)
      (htraj := htraj)
      0
  -- The shifted-subsequence regularizer bound puts the cluster point back in `effective_domain g`.
  have hxBar_g :
      xBar ∈ effective_domain g :=
    proximal_gradient_cluster_point_mem_effective_domain_g
      (f := f)
      (g := g)
      (Lf := Lf)
      hf_ne_bot
      hg_effective_domain_subset_interior_f_effective_domain
      hf_toReal_smooth_on_interior_effective_domain
      htraj
      (ψ := ψ)
      (xBar := xBar)
      (yRef := x 1)
      (C := (barL : ℝ))
      hψtendsto
      hψsucc_tendsto
      hyRef
      (by
        intro n
        simp)
  have hxBar_int :
      xBar ∈ interior (effective_domain f) :=
    hg_effective_domain_subset_interior_f_effective_domain hxBar_g
  -- The Lipschitz closure lemma then identifies the vanishing residual at the cluster point.
  have hGzero :
      G[barL] ⟨xBar, hxBar_int⟩ = 0 :=
    cluster_point_gradient_mapping_eq_zero_of_lipschitz
      (f := f)
      (g := g)
      (Lf := Lf)
      hf_ne_bot
      hf_effective_domain_convex
      hg_effective_domain_subset_interior_f_effective_domain
      hf_toReal_smooth_on_interior_effective_domain
      htraj
      barL
      hxBar
      hxBar_int
      hres
  have hdiff :
      is_differentiable_at f xBar :=
    is_differentiable_at_of_mem_interior_effective_domain
      hf_ne_bot
      hf_toReal_smooth_on_interior_effective_domain
      hxBar_int
  -- Finally convert vanishing of the gradient mapping to the textbook stationarity condition.
  exact
    (gradient_mapping_eq_zero_iff_is_stationary_point
      (f := f)
      (g := g)
      barL
      ⟨xBar, hxBar_int⟩
      hdiff).mp
      hGzero

-- Proof sketch: let `xBar` be a cluster point of the trajectory. The Lipschitz estimate from
-- Lemma 10.10 controls `‖G_s(xBar) - G_s(x^{k_j})‖` along a subsequence converging to `xBar`, and
-- clause (3) gives `G_s(x^{k_j}) → 0`; hence `G_s(xBar) = 0`. Theorem 10.7 then turns vanishing
-- of the gradient mapping into stationarity.
/-- Theorem 10.15 (5): clause (d), backtracking-B1 case. If `FOpt` is the greatest lower bound of
`Set.range (f + g)`, then every sequential limit point of a proximal-gradient trajectory
generated with backtracking procedure B1 is a stationary point of the composite problem
`min_x {f(x) + g(x)}`. -/
theorem proximal_gradient_backtracking_B1_cluster_point_is_stationary
    {x : ℕ → E} {L : ℕ → PosReal}
    (htraj : is_proximal_gradient_trajectory f g x L)
    (s : PosReal) (γ : ProximalGradientBacktrackingDecreaseFraction)
    (η : ProximalGradientBacktrackingGrowthFactor)
    (hB1 : uses_proximal_gradient_backtracking_B1_rule
      f g hg_effective_domain_subset_interior_f_effective_domain x L htraj s γ η)
    (hFOpt : IsGLB (Set.range F) (FOpt : EReal))
    {xBar : E} (hxBar : MapClusterPt xBar Filter.atTop x) :
    is_stationary_point f g xBar := by
  -- Route correction: the B1 branch uses the same cluster-point closure once the source-faithful
  -- domain bridge is established with the B1 stepsize upper bound.
  obtain ⟨ψ, hψmono, hψtendsto⟩ := MapClusterPt.tendsto_subseq hxBar
  -- Clause (b) provides residual decay for the baseline B1 residual `G_s`.
  have hres :
      Filter.Tendsto
        (fun k ↦ G[s] (proximal_gradient_trajectory_iterate htraj k))
        Filter.atTop
        (nhds 0) :=
    proximal_gradient_backtracking_B1_residual_tendsto_zero
      (f := f)
      (g := g)
      (Lf := Lf)
      hf_ne_bot
      hf_effective_domain_convex
      hg_effective_domain_subset_interior_f_effective_domain
      hf_toReal_smooth_on_interior_effective_domain
      hf_ne_bot
      hf_effective_domain_convex
      hg_effective_domain_subset_interior_f_effective_domain
      hf_toReal_smooth_on_interior_effective_domain
      htraj
      s
      γ
      η
      hB1
      hFOpt
  -- The same step-to-zero argument transfers the cluster limit to the shifted subsequence.
  have hstep :
      Filter.Tendsto (fun k ↦ x (k + 1) - x k) Filter.atTop (nhds 0) :=
    proximal_gradient_backtracking_B1_step_tendsto_zero
      (f := f)
      (g := g)
      (hg_subset := hg_effective_domain_subset_interior_f_effective_domain)
      (htraj := htraj)
      (s := s)
      (γ := γ)
      (η := η)
      (hB1 := hB1)
      (hres := hres)
  have hψsucc_tendsto :
      Filter.Tendsto (fun n ↦ x (ψ n + 1)) Filter.atTop (nhds xBar) :=
    subseq_succ_tendsto_of_step_tendsto_zero
      (x := x)
      (ψ := ψ)
      (xBar := xBar)
      hψmono
      hψtendsto
      hstep
  have hyRef : x 0 ∈ effective_domain g :=
    proximal_gradient_backtracking_iterate_mem_effective_domain_g
      (f := f)
      (g := g)
      (htraj := htraj)
      (s := s)
      (γ := γ)
      (η := η)
      (hB1 := hB1)
      (k := 0)
  let C : ℝ := max (s : ℝ) (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ))))
  have hL_bound : ∀ n, (L (ψ n) : ℝ) ≤ C := by
    -- Remark 10.13 already bounds every accepted B1 stepsize uniformly.
    intro n
    exact
      backtracking_B1_stepsize_le_max_at_iterate
        (f := f)
        (g := g)
        (Lf := Lf)
        (hf_ne_bot := hf_ne_bot)
        (hf_effective_domain_convex := hf_effective_domain_convex)
        (hg_effective_domain_subset_interior_f_effective_domain :=
          hg_effective_domain_subset_interior_f_effective_domain)
        (hf_toReal_smooth_on_interior_effective_domain :=
          hf_toReal_smooth_on_interior_effective_domain)
        s
        γ
        η
        htraj
        hB1
        (ψ n)
  -- The same domain bridge now applies with the B1 feasible reference point `x^0`.
  have hxBar_g :
      xBar ∈ effective_domain g :=
    proximal_gradient_cluster_point_mem_effective_domain_g
      (f := f)
      (g := g)
      (Lf := Lf)
      hf_ne_bot
      hg_effective_domain_subset_interior_f_effective_domain
      hf_toReal_smooth_on_interior_effective_domain
      htraj
      (ψ := ψ)
      (xBar := xBar)
      (yRef := x 0)
      (C := C)
      hψtendsto
      hψsucc_tendsto
      hyRef
      hL_bound
  have hxBar_int :
      xBar ∈ interior (effective_domain f) :=
    hg_effective_domain_subset_interior_f_effective_domain hxBar_g
  have hGzero :
      G[s] ⟨xBar, hxBar_int⟩ = 0 :=
    cluster_point_gradient_mapping_eq_zero_of_lipschitz
      (f := f)
      (g := g)
      (Lf := Lf)
      hf_ne_bot
      hf_effective_domain_convex
      hg_effective_domain_subset_interior_f_effective_domain
      hf_toReal_smooth_on_interior_effective_domain
      htraj
      s
      hxBar
      hxBar_int
      hres
  have hdiff :
      is_differentiable_at f xBar :=
    is_differentiable_at_of_mem_interior_effective_domain
      hf_ne_bot
      hf_toReal_smooth_on_interior_effective_domain
      hxBar_int
  -- As in the constant-step case, the cluster residual criterion closes the stationarity proof.
  exact
    (gradient_mapping_eq_zero_iff_is_stationary_point
      (f := f)
      (g := g)
      s
      ⟨xBar, hxBar_int⟩
      hdiff).mp
      hGzero

end

end LowerBound

end

end
