/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_4
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_15
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_5
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Assumption_13_1
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Definition_13_1
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Definition_13_22

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- `prompt_add/` is absent in this workspace, so the statement design is sampled directly from the
nearby Chapter 5, Chapter 8, and Chapter 13 owners.

This item is `source-facing`: it fixes the standing hypotheses for the constrained conditional-
gradient regime with a strongly convex feasible set. The canonical owners already present in the
project are:

- `IsConditionalGradientProblem` for the baseline constrained conditional-gradient data;
- `Set.StrongConvex` for the primitive `σ`-strong convexity of the feasible set `C`, together with
  the separate positivity clause `0 < σ`;
- `is_l_smooth_on` for the `L_f`-smoothness of the finite-valued restriction of `f`;
- `constrained_problem_solutions` for the optimal set `X^*` of Definition 13.15; and
- `generalized_conditional_gradient_optimal_value f (extendedIndicator C)` for the canonical
  constrained optimal value, obtained by specializing the Chapter 13 generalized owner to the
  indicator model.

The clean public API is therefore one Prop-valued assumption class carrying only the primitive
source-facing clauses. The baseline Chapter 13 owner `IsConditionalGradientProblem f C` is
recovered below as `bridge/view` API rather than inherited as primitive data, because two of its
fields are redundant here: `constraint_convex` already follows from `0 < σ` together with
`Set.StrongConvex C σ`, and `f_toReal_differentiableOn_effective_domain` already follows from the
owner smoothness clause
`is_l_smooth_on (fun x ↦ (f x).toReal) (effective_domain f) Lf`. The source-facing wrapper
`Set.StronglyConvexWith C σ` is likewise recovered below as derived bridge API rather than stored
redundantly. The constrained argmin, optimal-value, and gap quantities already live downstream as
the Chapter 13 owners `generalized_conditional_gradient_argmin`,
`generalized_conditional_gradient_optimal_value`, and `S`, specialized to
`g = extendedIndicator C`; they should not be rebuilt here as parallel constrained-only wrappers.
The optimizer set itself is already the Chapter 8 owner `constrained_problem_solutions f C`, so it
should remain on the public surface directly rather than being passed through a second parameter
`XStar` plus an equality field, and optimizer attainment / optimal-value characterization are
recovered below as bridge theorems from the canonical indicator specialization. -/

/-- Assumption 13.25 (1): clauses (A)-(D) for the strongly convex conditional-gradient setting mean
that `f` never takes the value `⊥`, the constrained feasible set `C` is nonempty and compact,
`f` is convex with `C ⊆ dom(f)` and open effective domain, `σ > 0`, `C` is `σ`-strongly convex
in the primitive sense `Set.StrongConvex C σ`, `x ↦ (f x).toReal` is `L_f`-smooth on `dom(f)`
with `L_f > 0`, and the gradient norm on `C` is bounded below by `δ > 0`, for the constrained
problem `min {f x : x ∈ C}`. The baseline owner `IsConditionalGradientProblem f C` is derived
below as bridge API rather than inherited. The canonical optimizer set
`constrained_problem_solutions f C` and optimal value
`generalized_conditional_gradient_optimal_value f (extendedIndicator C)` are derived below rather
than stored as primitive fields. -/
class IsStronglyConvexConditionalGradientProblem
    (f : E → EReal) (C : Set E) (σ δ : ℝ) (Lf : NNReal) : Prop where
  f_ne_bot (x : E) : f x ≠ ⊥
  constraint_nonempty : C.Nonempty
  constraint_compact : IsCompact C
  f_convex : is_convex_function f
  feasible_subset_effective_domain : C ⊆ effective_domain f
  f_effective_domain_open : IsOpen (effective_domain f)
  sigma_pos : 0 < σ
  strongConvex : Set.StrongConvex C σ
  f_toReal_smooth_on_effective_domain :
    is_l_smooth_on (fun x ↦ (f x).toReal) (effective_domain f) Lf
  Lf_pos : 0 < (Lf : ℝ)
  delta_pos : 0 < δ
  gradient_norm_lower_bound {x : E} (hx : x ∈ C) :
    δ ≤ ‖∇ (fun y ↦ (f y).toReal) x‖

namespace IsStronglyConvexConditionalGradientProblem

theorem constraint_convex
    {f : E → EReal} {C : Set E} {σ δ : ℝ} {Lf : NNReal}
    (h : IsStronglyConvexConditionalGradientProblem f C σ δ Lf) :
    Convex ℝ C :=
  h.strongConvex.convex h.sigma_pos.le

theorem f_toReal_differentiableOn_effective_domain
    {f : E → EReal} {C : Set E} {σ δ : ℝ} {Lf : NNReal}
    (h : IsStronglyConvexConditionalGradientProblem f C σ δ Lf) :
    DifferentiableOn ℝ (fun x ↦ (f x).toReal) (effective_domain f) :=
  fun x hx ↦ (h.f_toReal_smooth_on_effective_domain.1 x hx).differentiableWithinAt

theorem toIsConditionalGradientProblem
    {f : E → EReal} {C : Set E} {σ δ : ℝ} {Lf : NNReal}
    (h : IsStronglyConvexConditionalGradientProblem f C σ δ Lf) :
    IsConditionalGradientProblem f C where
  f_ne_bot := h.f_ne_bot
  constraint_nonempty := h.constraint_nonempty
  constraint_convex := h.constraint_convex
  constraint_compact := h.constraint_compact
  f_convex := h.f_convex
  feasible_subset_effective_domain := h.feasible_subset_effective_domain
  f_effective_domain_open := h.f_effective_domain_open
  f_toReal_differentiableOn_effective_domain :=
    h.f_toReal_differentiableOn_effective_domain

theorem toIsGeneralizedConditionalGradientProblem
    {f : E → EReal} {C : Set E} {σ δ : ℝ} {Lf : NNReal}
    (h : IsStronglyConvexConditionalGradientProblem f C σ δ Lf) :
    IsGeneralizedConditionalGradientProblem f (extendedIndicator C) Lf := by
  have h_indicator_proper : IsProperExtendedRealFunction (extendedIndicator C) := by
    refine
      { ne_bot := ?_
        effective_domain_nonempty := ?_ }
    · intro x
      by_cases hx : x ∈ C <;> simp [extendedIndicator, hx]
    · rcases h.constraint_nonempty with ⟨x, hx⟩
      exact ⟨x, by simpa using hx⟩
  have h_zero_convex : is_convex_function (0 : E → EReal) := by
    refine (is_convex_function_iff_convexOn_toReal ?_).2 ?_
    · intro x hx
      simp
    · simpa [effective_domain] using
        (convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (Set.univ : Set E)))
  have h_indicator_convex : is_convex_function (extendedIndicator C) := by
    have h_constrained_convex :
        is_convex_function (constrained_problem_objective (0 : E → EReal) C) :=
      is_convex_function_constrained_problem_objective h_zero_convex h.constraint_convex
    rw [constrained_problem_objective_eq_add_extendedIndicator
      (0 : E → EReal) C (fun _ _ ↦ by simp)] at h_constrained_convex
    simpa [composite_model_objective] using h_constrained_convex
  refine
    { toIsProperExtendedRealFunction := h_indicator_proper
      g_closed :=
        (extendedIndicator_lowerSemicontinuous_iff_isClosed C).2 h.constraint_compact.isClosed
      g_convex := h_indicator_convex
      g_effective_domain_compact := by
        simpa [effective_domain_extendedIndicator] using h.constraint_compact
      f_ne_bot := h.f_ne_bot
      f_effective_domain_open := h.f_effective_domain_open
      f_effective_domain_convex :=
        effective_domain_convex_of_is_convex_function h.f_convex
      g_effective_domain_subset_f_effective_domain := by
        simpa [effective_domain_extendedIndicator] using h.feasible_subset_effective_domain
      f_toReal_smooth_on_effective_domain := h.f_toReal_smooth_on_effective_domain
      Lf_pos := h.Lf_pos }

/-- Assumption 13.25 (2): the standing strongly convex conditional-gradient hypotheses canonically
induce the source-facing positive/nonempty strong-convex-set
owner from Definition 13.22. -/
theorem stronglyConvexWith
    {f : E → EReal} {C : Set E} {σ δ : ℝ} {Lf : NNReal}
    (h : IsStronglyConvexConditionalGradientProblem f C σ δ Lf) :
    Set.StronglyConvexWith C σ where
  sigma_pos := h.sigma_pos
  nonempty := h.constraint_nonempty
  strongConvex := h.strongConvex

/-- The strongly convex conditional-gradient standing assumptions form a proof-irrelevant owner. -/
instance instSubsingleton
    {f : E → EReal} {C : Set E} {σ δ : ℝ} {Lf : NNReal}
    : Subsingleton (IsStronglyConvexConditionalGradientProblem f C σ δ Lf) :=
  inferInstance

/-- The feasible set of Assumption 13.25 meets the effective domain of `f`. -/
theorem constraint_inter_effective_domain_nonempty
    {f : E → EReal} {C : Set E} {σ δ : ℝ} {Lf : NNReal}
    (h : IsStronglyConvexConditionalGradientProblem f C σ δ Lf) :
    (C ∩ effective_domain f).Nonempty := by
  rcases h.constraint_nonempty with ⟨x, hx⟩
  exact ⟨x, hx, h.feasible_subset_effective_domain hx⟩

/-- On the feasible set of Assumption 13.25, the objective is lower semicontinuous because the
finite-valued restriction `x ↦ (f x).toReal` is smooth, hence continuous, on `dom(f)`. -/
theorem lowerSemicontinuousOn_constraint
    {f : E → EReal} {C : Set E} {σ δ : ℝ} {Lf : NNReal}
    (h : IsStronglyConvexConditionalGradientProblem f C σ δ Lf) :
    LowerSemicontinuousOn f C := by
  have hf_cont : ContinuousOn (fun x ↦ ((f x).toReal : EReal)) C := by
    refine
      (continuous_coe_real_ereal.continuousOn : ContinuousOn ((↑) : ℝ → EReal) Set.univ).comp
        ?_ ?_
    · intro x hx
      exact
        ((h.f_toReal_smooth_on_effective_domain.1 x
          (h.feasible_subset_effective_domain hx)).continuousAt).continuousWithinAt
    · intro x hx
      simp
  intro x hx
  refine (hf_cont.lowerSemicontinuousOn x hx).congr_of_eventuallyEq hx ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp [EReal.coe_toReal
    (mem_effective_domain.mp (h.feasible_subset_effective_domain hy)).ne
    (h.f_ne_bot y)]

/-- Assumption 13.25 (3): the standing hypotheses imply attainment of the constrained minimum on
the canonical solution set
`constrained_problem_solutions f C`. -/
theorem constrained_problem_solutions_nonempty
    {f : E → EReal} {C : Set E} {σ δ : ℝ} {Lf : NNReal}
    (h : IsStronglyConvexConditionalGradientProblem f C σ δ Lf) :
    (constrained_problem_solutions f C).Nonempty := by
  obtain ⟨x, hx, hxmin⟩ :=
    exists_isMinOn_on_compact f C h.lowerSemicontinuousOn_constraint h.constraint_compact
      h.constraint_inter_effective_domain_nonempty
  refine ⟨x, ?_⟩
  simpa using (show x ∈ C ∧ IsMinOn f C x from ⟨hx.1, hxmin⟩)

/-- Every constrained optimizer attains the canonical Chapter 13 optimal value for the indicator
specialization. -/
theorem optimal_value_eq_of_mem_constrained_problem_solutions
    {f : E → EReal} {C : Set E} {σ δ : ℝ} {Lf : NNReal} {xStar : E}
    (h : IsStronglyConvexConditionalGradientProblem f C σ δ Lf)
    (hxStar : xStar ∈ constrained_problem_solutions f C) :
    generalized_conditional_gradient_optimal_value f (extendedIndicator C) = f xStar := by
  have hxStar_data : xStar ∈ C ∧ IsMinOn f C xStar := by
    simpa using hxStar
  have hxStar_min :
      IsMinOn (composite_model_objective f (extendedIndicator C)) Set.univ xStar := by
    rw [isMinOn_univ_iff]
    intro y
    by_cases hyC : y ∈ C
    · simpa [composite_model_objective, extendedIndicator, hxStar_data.1, hyC] using
        hxStar_data.2 hyC
    · have hy_top : composite_model_objective f (extendedIndicator C) y = ⊤ := by
        simp [composite_model_objective, extendedIndicator, hyC, h.f_ne_bot y]
      rw [hy_top]
      exact le_top
  have hglb :
      IsGLB (Set.range (composite_model_objective f (extendedIndicator C)))
        (composite_model_objective f (extendedIndicator C) xStar) := by
    simpa using hxStar_min.isGLB (by simp : xStar ∈ (Set.univ : Set E))
  rw [generalized_conditional_gradient_optimal_value_eq_sInf]
  calc
    sInf (Set.range (composite_model_objective f (extendedIndicator C))) =
        composite_model_objective f (extendedIndicator C) xStar :=
      hglb.csInf_eq (Set.range_nonempty _)
    _ = f xStar := by
      simp [composite_model_objective, extendedIndicator, hxStar_data.1]

/-- Assumption 13.25 (4): the canonical optimizer set and optimal-value owners recover the
greatest-lower-bound characterization of the constrained
optimal value from the canonical optimizer set and optimal-value owners. -/
theorem optimal_value_isGLB
    {f : E → EReal} {C : Set E} {σ δ : ℝ} {Lf : NNReal}
    (h : IsStronglyConvexConditionalGradientProblem f C σ δ Lf) :
    IsGLB (f '' C) (generalized_conditional_gradient_optimal_value f (extendedIndicator C)) := by
  rcases h.constrained_problem_solutions_nonempty with ⟨xStar, hxStar⟩
  have hxStar_data : xStar ∈ C ∧ IsMinOn f C xStar := by
    simpa using hxStar
  have hglb : IsGLB (f '' C) (f xStar) := by
    simpa [Set.mem_image] using hxStar_data.2.isGLB hxStar_data.1
  rw [h.optimal_value_eq_of_mem_constrained_problem_solutions hxStar]
  exact hglb

end IsStronglyConvexConditionalGradientProblem

end
