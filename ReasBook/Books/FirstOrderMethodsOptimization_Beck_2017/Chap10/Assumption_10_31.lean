/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_67

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Assumption 10.31 is `source-facing`: it fixes the standing hypotheses for the fast proximal
gradient method with a real-valued smooth term and an extended-real-valued convex regularizer.

Domain sampling:
- `IsConvexCompositeSmoothMinimizationProblem` from Definition 10.67 is the Chapter 10
  `core/canonical` owner for convex composite smooth minimization data;
- `IsCompositeSmoothMinimizationProblem` is its weaker inherited owner;
- Assumption 13.25 shows the local project pattern for a source-facing standing-assumption class
  with a canonical bridge to the ambient owner abstraction.

Primitive data here are only the textbook clauses special to the fast proximal-gradient regime:
the regularity of `g`, the real-valued convex/global-smoothness clauses on `f`, and the
optimizer/value data. The Chapter 10 convex composite owner for `f.toEReal` is derived API and
should be recovered canonically rather than rebuilt later from duplicate field-level instances. -/

/-- Assumption 10.31: clauses (A)-(C) for the fast proximal-gradient method mean that
`g : E → (-∞, ∞]` is proper, closed, and convex, `f : E → ℝ` is convex and globally
`L_f`-smooth, and `XStar = X^*` is the nonempty optimal set of the composite problem
`min_x ((f x : EReal) + g x)` with optimal value `FOpt = F_opt`. -/
class IsFastProximalGradientProblem
    (f : E → ℝ) (g : E → EReal) (XStar : outParam (Set E)) (FOpt : outParam ℝ)
    (Lf : outParam NNReal) : Prop where
  g_proper : IsProperExtendedRealFunction g
  g_closed : LowerSemicontinuous g
  g_convex : is_convex_function g
  f_convex : ConvexOn ℝ Set.univ f
  f_smooth : is_l_smooth_on f Set.univ Lf
  optimal_set_eq :
    XStar = unconstrained_problem_solutions (composite_model_objective f.toEReal g)
  optimal_set_nonempty : XStar.Nonempty
  optimal_value_isGLB :
    IsGLB (Set.range (composite_model_objective f.toEReal g)) (FOpt : EReal)

-- Proof sketch for the bridge theorem below: a real-valued `L_f`-smooth convex function is
-- continuous, hence lower
-- semicontinuous, and its `EReal` coercion never takes the value `-∞` and has full effective
-- domain `Set.univ`. Combine these derived facts with the source-facing fields of
-- `IsFastProximalGradientProblem` and the convexity bridge `Function.toEReal_isConvexFunction`.
/-- Helper for Assumption 10.31: the `EReal` lift of the smooth term never attains `-∞`. -/
theorem IsFastProximalGradientProblem.toEReal_ne_bot
    {f : E → ℝ} {g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
    (_h : IsFastProximalGradientProblem f g XStar FOpt Lf) :
    ∀ x, f.toEReal x ≠ ⊥ := by
  -- The canonical `EReal` lift of a real-valued function is always finite.
  intro x
  simp [Function.toEReal]

/-- Helper for Assumption 10.31: global smoothness makes the `EReal` lift of `f` lower
semicontinuous. -/
theorem IsFastProximalGradientProblem.toEReal_lowerSemicontinuous
    {f : E → ℝ} {g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
    (h : IsFastProximalGradientProblem f g XStar FOpt Lf) :
    LowerSemicontinuous f.toEReal := by
  -- Global smoothness on `Set.univ` gives differentiability, hence continuity, everywhere.
  have hcont : Continuous f := by
    refine continuous_iff_continuousAt.2 ?_
    intro x
    exact (h.f_smooth.1 x (by simp)).continuousAt
  -- Continuous real-valued maps are lower semicontinuous after coercion to `EReal`.
  exact Function.toEReal_lowerSemicontinuous_of_continuous hcont

/-- Helper for Assumption 10.31: convexity of the real-valued smooth term passes to its `EReal`
lift. -/
theorem IsFastProximalGradientProblem.toEReal_convex
    {f : E → ℝ} {g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
    (h : IsFastProximalGradientProblem f g XStar FOpt Lf) :
    is_convex_function f.toEReal := by
  -- The Chapter 9 coercion lemma transports convexity from `f` to `f.toEReal`.
  exact Function.toEReal_isConvexFunction h.f_convex

/-- Helper for Assumption 10.31: every effective point of `g` lies in the interior of the full
effective domain of `f.toEReal`. -/
theorem IsFastProximalGradientProblem.g_effective_domain_subset_interior_toEReal_effective_domain
    {f : E → ℝ} {g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
    (_h : IsFastProximalGradientProblem f g XStar FOpt Lf) :
    effective_domain g ⊆ interior (effective_domain f.toEReal) := by
  -- The `EReal` lift of a real-valued function has effective domain `Set.univ`.
  intro x hx
  simp [effective_domain, Function.toEReal]

/-- Helper for Assumption 10.31: after identifying the effective domain of `f.toEReal` with
`Set.univ`, the Chapter 10 smoothness field is exactly the stored global smoothness of `f`. -/
theorem IsFastProximalGradientProblem.toEReal_smooth_on_interior_effective_domain
    {f : E → ℝ} {g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
    (h : IsFastProximalGradientProblem f g XStar FOpt Lf) :
    is_l_smooth_on (fun x ↦ (f.toEReal x).toReal) (interior (effective_domain f.toEReal)) Lf := by
  -- The lifted function is finite everywhere, so its `toReal` is just `f` on `Set.univ`.
  simpa [effective_domain, Function.toEReal] using h.f_smooth

/-- Assumption 10.31: a fast proximal-gradient problem canonically induces the Chapter 10 convex
composite smooth minimization assumptions after coercing the real-valued smooth term to `EReal`.
-/
theorem IsFastProximalGradientProblem.toIsConvexCompositeSmoothMinimizationProblem
    {f : E → ℝ} {g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
    (h : IsFastProximalGradientProblem f g XStar FOpt Lf) :
    IsConvexCompositeSmoothMinimizationProblem f.toEReal g XStar FOpt Lf := by
  -- Package the derived `f.toEReal` facts with the stored `g`-side and optimizer data.
  refine
    { f_ne_bot := h.toEReal_ne_bot
      g_proper := h.g_proper
      f_closed := h.toEReal_lowerSemicontinuous
      g_closed := h.g_closed
      f_convex := h.toEReal_convex
      g_convex := h.g_convex
      g_effective_domain_subset_interior_f_effective_domain :=
        h.g_effective_domain_subset_interior_toEReal_effective_domain
      f_toReal_smooth_on_interior_effective_domain :=
        h.toEReal_smooth_on_interior_effective_domain
      optimal_set_eq := h.optimal_set_eq
      optimal_set_nonempty := h.optimal_set_nonempty
      optimal_value_isGLB := h.optimal_value_isGLB }

/-- A fast proximal-gradient problem canonically induces the Chapter 10 composite smooth
minimization assumptions after coercing the real-valued smooth term to `EReal`. -/
theorem IsFastProximalGradientProblem.toIsCompositeSmoothMinimizationProblem
    {f : E → ℝ} {g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
    (h : IsFastProximalGradientProblem f g XStar FOpt Lf) :
    IsCompositeSmoothMinimizationProblem f.toEReal g XStar FOpt Lf :=
  h.toIsConvexCompositeSmoothMinimizationProblem.toIsCompositeSmoothMinimizationProblem

/-- In Assumption 10.31, the nonsmooth term `g` is proper. -/
instance instIsProperExtendedRealFunctionRightOfIsFastProximalGradientProblem
    {f : E → ℝ} {g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
    (h : IsFastProximalGradientProblem f g XStar FOpt Lf) :
    IsProperExtendedRealFunction g :=
  h.g_proper

/-- In Assumption 10.31, the nonsmooth term `g` is lower semicontinuous. -/
instance instFactLowerSemicontinuousRightOfIsFastProximalGradientProblem
    {f : E → ℝ} {g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
    (h : IsFastProximalGradientProblem f g XStar FOpt Lf) :
    Fact (LowerSemicontinuous g) :=
  ⟨h.g_closed⟩

/-- In Assumption 10.31, the nonsmooth term `g` is convex. -/
instance instFactIsConvexFunctionRightOfIsFastProximalGradientProblem
    {f : E → ℝ} {g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
    (h : IsFastProximalGradientProblem f g XStar FOpt Lf) :
    Fact (is_convex_function g) :=
  ⟨h.g_convex⟩

namespace IsFastProximalGradientProblem

/-- For the zero regularizer, the optimal set in Assumption 10.31 is exactly the canonical
unconstrained solution set of the real-valued objective `f`. -/
theorem optimal_set_eq_unconstrained_problem_solutions
    {f : E → ℝ} {XStar : Set E} {fOpt : ℝ} {Lf : NNReal}
    (h : IsFastProximalGradientProblem f (0 : E → EReal) XStar fOpt Lf) :
    XStar = unconstrained_problem_solutions f := by
  ext x
  rw [h.optimal_set_eq, mem_unconstrained_problem_solutions_iff_forall_le,
    mem_unconstrained_problem_solutions_iff_forall_le]
  simp [composite_model_objective]

/-- For the zero regularizer, the optimal set in Assumption 10.31 is exactly the set of global
minimizers of `f`. -/
theorem optimal_set_eq_global_minimizers
    {f : E → ℝ} {XStar : Set E} {fOpt : ℝ} {Lf : NNReal}
    (h : IsFastProximalGradientProblem f (0 : E → EReal) XStar fOpt Lf) :
    XStar = {x | IsMinOn f Set.univ x} := by
  simpa [unconstrained_problem_solutions] using
    optimal_set_eq_unconstrained_problem_solutions h

/-- For the zero regularizer, the optimal value in Assumption 10.31 is the greatest lower bound
of the real-valued objective range. -/
theorem optimal_value_isGLB_range
    {f : E → ℝ} {XStar : Set E} {fOpt : ℝ} {Lf : NNReal}
    (h : IsFastProximalGradientProblem f (0 : E → EReal) XStar fOpt Lf) :
    IsGLB (Set.range f) fOpt := by
  constructor
  · rintro _ ⟨x, rfl⟩
    exact EReal.coe_le_coe_iff.mp <|
      h.optimal_value_isGLB.1 ⟨x, by simp [composite_model_objective]⟩
  · intro b hb
    exact EReal.coe_le_coe_iff.mp <|
      h.optimal_value_isGLB.2 <| by
        rintro _ ⟨x, rfl⟩
        simpa [composite_model_objective] using
          (EReal.coe_le_coe_iff.mpr (hb ⟨x, rfl⟩))

end IsFastProximalGradientProblem

end
