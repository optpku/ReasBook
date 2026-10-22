/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_15
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_7
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u}

/- Definition 10.4.2 is `source-facing`, but its owner abstractions already live upstream:

- `IsConstrainedConvexProblem` from Chapter 8 owns the constrained problem data
  `min {f x : x ∈ C}`;
- `is_l_smooth_on` from Chapter 5 owns the smoothness clause on `f.toReal`;
- `IsCompositeSmoothMinimizationProblem` from Definition 10.3 is the Chapter 10 canonical owner
  after specializing the nonsmooth term to `extendedIndicator C`.

The public surface here should therefore be a bridge between those owners, not a parallel wrapper
class. In this bridge layer the primitive data are only `f`, `C`, and the domain/nonemptiness
side conditions needed to compare the upstream solution-set owners; no normed-space structure is
mathematically active. Because `IsMinOn f C x` does not itself encode feasibility, the faithful
minimizer comparison is at the Chapter 8 solution-set level. -/

/-- If `C` contains a feasible point in the effective domain of `f`, then the ambient minimizers
of the constrained objective are exactly the constrained minimizers of `f` on `C`. -/
theorem unconstrained_problem_solutions_constrained_problem_objective_eq
    (f : E → EReal) (C : Set E) (hC_dom : (C ∩ effective_domain f).Nonempty) :
    unconstrained_problem_solutions (constrained_problem_objective f C) =
      constrained_problem_solutions f C := by
  rcases hC_dom with ⟨z, hzC, hz_dom⟩
  ext x
  rw [mem_unconstrained_problem_solutions_iff, mem_constrained_problem_solutions_iff]
  rw [isMinOn_univ_iff, isMinOn_iff]
  constructor
  · intro hx
    have hx_le_z : constrained_problem_objective f C x ≤ constrained_problem_objective f C z := hx z
    have hxC : x ∈ C := by
      by_contra hxC
      have hx_top : constrained_problem_objective f C x = ⊤ := by
        simp [constrained_problem_objective, hxC]
      have hz_lt_top : constrained_problem_objective f C z < ⊤ := by
        simpa [constrained_problem_objective, hzC] using hz_dom
      exact (not_le_of_gt hz_lt_top) (hx_top ▸ hx_le_z)
    refine ⟨hxC, ?_⟩
    intro y hyC
    simpa [constrained_problem_objective, hxC, hyC] using hx y
  · rintro ⟨hxC, hx⟩ y
    by_cases hyC : y ∈ C
    · simpa [constrained_problem_objective, hxC, hyC] using hx y hyC
    · simp [constrained_problem_objective, hxC, hyC]

/-- Under the standard side condition excluding the value `-∞` off the feasible set, the Chapter
10 composite model with `g = extendedIndicator C` has the same solution set as the constrained
problem `min {f x : x ∈ C}`. -/
theorem unconstrained_problem_solutions_composite_model_objective_extendedIndicator_eq
    (f : E → EReal) (C : Set E) (hC_dom : (C ∩ effective_domain f).Nonempty)
    (h_ne_bot : ∀ y ∉ C, f y ≠ ⊥) :
    unconstrained_problem_solutions (composite_model_objective f (extendedIndicator C)) =
      constrained_problem_solutions f C := by
  rw [composite_model_objective_eq_add]
  rw [← constrained_problem_objective_eq_add_extendedIndicator f C h_ne_bot]
  exact unconstrained_problem_solutions_constrained_problem_objective_eq f C hC_dom

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (f : E → EReal) (C XStar : Set E) (fOpt : ℝ) (Lf : NNReal)

/- Definition 10.4.2 itself is the Chapter 8 constrained convex owner together with the Chapter 5
smoothness clause on `f.toReal`; its Chapter 10 content is the canonical indicator specialization
to `IsCompositeSmoothMinimizationProblem`, not a second root owner. -/

/- Definition 10.4.2: the constrained problem itself is the Chapter 8 owner
`IsConstrainedConvexProblem f C XStar fOpt`. -/
#check IsConstrainedConvexProblem f C XStar fOpt

/- Definition 10.4.2: the smoothness clause is the Chapter 5 condition on `f.toReal` over
`interior (effective_domain f)`. -/
#check is_l_smooth_on (fun x ↦ (f x).toReal) (interior (effective_domain f)) Lf

/-- A Chapter 8 constrained convex problem together with the Chapter 5 smoothness clause on
`f.toReal` canonically induces the Chapter 10 composite smooth minimization owner with
`g = extendedIndicator C`. -/
theorem IsConstrainedConvexProblem.toIsCompositeSmoothMinimizationProblem
    {f : E → EReal} {C XStar : Set E} {fOpt : ℝ} {Lf : NNReal}
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    (h_smooth : is_l_smooth_on (fun x ↦ (f x).toReal) (interior (effective_domain f)) Lf) :
    IsCompositeSmoothMinimizationProblem f (extendedIndicator C) XStar fOpt Lf := by
  have h_ne_bot_off : ∀ y ∉ C, f y ≠ ⊥ := fun y _ ↦ h_problem.ne_bot y
  have hC_dom : (C ∩ effective_domain f).Nonempty := by
    rcases h_problem.feasible_nonempty with ⟨x, hxC⟩
    exact ⟨x, hxC, interior_subset (h_problem.feasible_subset_interior_effective_domain hxC)⟩
  have h_indicator_proper : IsProperExtendedRealFunction (extendedIndicator C) := by
    refine
      { ne_bot := ?_
        effective_domain_nonempty := ?_ }
    · intro x
      by_cases hx : x ∈ C <;> simp [extendedIndicator, hx]
    · rcases h_problem.feasible_nonempty with ⟨x, hxC⟩
      exact ⟨x, by simpa using hxC⟩
  have h_zero_convex : is_convex_function (0 : E → EReal) := by
    refine (is_convex_function_iff_convexOn_toReal ?_).2 ?_
    · intro x hx
      simp
    · simpa [effective_domain] using
        (convexOn_const (0 : ℝ) (convex_univ : Convex ℝ (Set.univ : Set E)))
  have h_indicator_convex : is_convex_function (extendedIndicator C) := by
    have h_constrained_convex :
        is_convex_function (constrained_problem_objective (0 : E → EReal) C) :=
      is_convex_function_constrained_problem_objective h_zero_convex h_problem.feasible_convex
    rw [constrained_problem_objective_eq_add_extendedIndicator
      (0 : E → EReal) C (fun _ _ ↦ by simp)] at h_constrained_convex
    simpa [composite_model_objective] using h_constrained_convex
  refine
    { f_ne_bot := h_problem.ne_bot
      g_proper := h_indicator_proper
      f_closed := h_problem.closed
      g_closed :=
        (extendedIndicator_lowerSemicontinuous_iff_isClosed C).2 h_problem.feasible_closed
      g_convex := h_indicator_convex
      f_effective_domain_convex :=
        effective_domain_convex_of_is_convex_function h_problem.convex
      g_effective_domain_subset_interior_f_effective_domain := by
        simpa using h_problem.feasible_subset_interior_effective_domain
      f_toReal_smooth_on_interior_effective_domain := h_smooth
      optimal_set_eq := by
        calc
          XStar = constrained_problem_solutions f C := h_problem.optimal_set_eq
          _ = unconstrained_problem_solutions
              (composite_model_objective f (extendedIndicator C)) := by
            symm
            exact
              unconstrained_problem_solutions_composite_model_objective_extendedIndicator_eq
                f C hC_dom h_ne_bot_off
      optimal_set_nonempty := h_problem.optimal_set_nonempty
      optimal_value_isGLB := by
        refine ⟨?_, ?_⟩
        · rintro _ ⟨x, rfl⟩
          by_cases hxC : x ∈ C
          · simpa [composite_model_objective, extendedIndicator, hxC] using
              h_problem.optimal_value_isGLB.left ⟨x, hxC, rfl⟩
          · have hx_top :
                composite_model_objective f (extendedIndicator C) x = ⊤ := by
              simpa [composite_model_objective_apply, extendedIndicator, hxC] using
                EReal.add_top_of_ne_bot (h_ne_bot_off x hxC)
            simp [hx_top]
        · intro b hb
          exact h_problem.optimal_value_isGLB.right <| by
            rintro _ ⟨x, hxC, rfl⟩
            exact hb ⟨x, by simp [composite_model_objective, extendedIndicator, hxC]⟩ }

end
