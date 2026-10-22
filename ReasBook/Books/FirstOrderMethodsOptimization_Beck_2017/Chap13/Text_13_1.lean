/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_4
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Assumption_13_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f g : E → EReal} {Lf : NNReal}

/-- Minimizing `f + g` globally is equivalent to minimizing it on `effective_domain g` when
`f` never takes the value `-∞`. -/
private theorem isMinOn_composite_model_objective_univ_iff_isMinOn_effective_domain_local
    (hf_ne_bot : ∀ y, f y ≠ ⊥) {xStar : E} :
    IsMinOn (composite_model_objective f g) Set.univ xStar ↔
      IsMinOn (composite_model_objective f g) (effective_domain g) xStar := by
  rw [isMinOn_univ_iff, isMinOn_iff]
  constructor
  · intro hxMin y _
    exact hxMin y
  · intro hxMin y
    by_cases hy : y ∈ effective_domain g
    · exact hxMin y hy
    · have hgy_top : g y = ⊤ :=
        le_antisymm le_top (not_lt.mp (by simpa using hy))
      simp [composite_model_objective_apply, hgy_top, hf_ne_bot y]

namespace IsGeneralizedConditionalGradientProblem

/-- Under Assumption 13.1, the composite objective `F(x) = f(x) + g(x)` is lower semicontinuous on
the compact feasible core `effective_domain g`. -/
theorem composite_model_objective_lowerSemicontinuousOn_effective_domain
    (h : IsGeneralizedConditionalGradientProblem f g Lf) :
    LowerSemicontinuousOn (composite_model_objective f g) (effective_domain g) := by
  have hf_cont : ContinuousOn (fun x ↦ ((f x).toReal : EReal)) (effective_domain g) := by
    refine
      (continuous_coe_real_ereal.continuousOn : ContinuousOn ((↑) : ℝ → EReal) Set.univ).comp
        ?_ ?_
    · intro x hx
      exact
        ((h.f_toReal_smooth_on_effective_domain.1 x
          (h.g_effective_domain_subset_f_effective_domain hx)).continuousAt).continuousWithinAt
    · intro x hx
      simp
  have hsum :
      LowerSemicontinuousOn (fun x ↦ ((f x).toReal : EReal) + g x) (effective_domain g) := by
    refine hf_cont.lowerSemicontinuousOn.add' (h.g_closed.lowerSemicontinuousOn _) ?_
    intro x hx
    exact EReal.continuousAt_add (.inl (EReal.coe_ne_top _)) (.inl (EReal.coe_ne_bot _))
  intro x hx
  refine (hsum x hx).congr_of_eventuallyEq hx ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp [EReal.coe_toReal
    (mem_effective_domain.mp (h.g_effective_domain_subset_f_effective_domain hy)).ne
    (h.f_ne_bot y)]

end IsGeneralizedConditionalGradientProblem

-- Proof sketch: use compactness and nonemptiness of `effective_domain g` from properness of `g`,
-- continuity of `f.toReal` on `effective_domain g` from the smoothness hypothesis and domain
-- inclusion, and lower semicontinuity of `g`; then `x ↦ f x + g x` is lower semicontinuous on the
-- nonempty compact set `effective_domain g`, so a generalized Weierstrass theorem yields a global
-- minimizer.
/-- Text 13.1: under Assumption 13.1 (A) and (B), the optimal set `X^*` of the composite
optimization problem `min_x {F(x) ≡ f(x) + g(x)}` is nonempty. -/
theorem generalized_conditional_gradient_optimal_set_nonempty
    (h : IsGeneralizedConditionalGradientProblem f g Lf) :
    (unconstrained_problem_solutions (composite_model_objective f g)).Nonempty := by
  obtain ⟨y, hy⟩ := h.toIsProperExtendedRealFunction.effective_domain_nonempty
  have hyF : y ∈ effective_domain (composite_model_objective f g) := by
    exact mem_effective_domain.mpr <|
      by
        simpa [composite_model_objective_apply] using
          (EReal.add_lt_top
            (mem_effective_domain.mp (h.g_effective_domain_subset_f_effective_domain hy)).ne
            (mem_effective_domain.mp hy).ne)
  obtain ⟨x, _, hxmin⟩ :=
    exists_isMinOn_on_compact
      (composite_model_objective f g)
      (effective_domain g)
      h.composite_model_objective_lowerSemicontinuousOn_effective_domain
      h.g_effective_domain_compact
      ⟨y, ⟨hy, hyF⟩⟩
  have hxmin_univ : IsMinOn (composite_model_objective f g) Set.univ x :=
    (isMinOn_composite_model_objective_univ_iff_isMinOn_effective_domain_local
      h.f_ne_bot).2 hxmin
  exact ⟨x, mem_unconstrained_problem_solutions_iff.mpr hxmin_univ⟩

end
