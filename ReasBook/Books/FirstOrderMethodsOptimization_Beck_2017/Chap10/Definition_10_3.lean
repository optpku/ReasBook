/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_2
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 10.3 is `source-facing`: it fixes the standing hypotheses for the composite model
`min_x {F(x) = f(x) + g(x)}` used by the proximal gradient method. Domain sampling points to the
Chapter 2 owner `IsProperExtendedRealFunction` for extended-real properness, Chapter 8's
`unconstrained_problem_solutions` for the optimizer set, and Chapter 10's
`composite_model_objective` for the objective itself. Primitive data here are the closedness,
convexity, domain-compatibility, smoothness, and optimizer-value clauses, together with the
genuinely needed non-`⊥` hypothesis on `f`; full properness of `f` is derived from `g_proper`
plus `effective_domain g ⊆ interior (effective_domain f)`, so it should not remain primitive
public data. -/

/-- Definition 10.3: clauses (A)-(C) for the composite model
`min_x {F(x) = f(x) + g(x)}` mean that `g` is proper, closed, and convex; `f` never takes the
value `-∞`, is closed, `effective_domain f` is convex, `effective_domain g ⊆
interior (effective_domain f)`, and `(fun x ↦ (f x).toReal)` is `L_f`-smooth on
`interior (effective_domain f)`; these clauses therefore imply that `f` is proper; and
`XStar = X^*` is the nonempty optimal set with optimal value `FOpt = F_opt`. -/
class IsCompositeSmoothMinimizationProblem
    (f g : E → EReal) (XStar : outParam (Set E)) (FOpt : outParam ℝ) (Lf : NNReal) : Prop where
  f_ne_bot : ∀ x, f x ≠ ⊥
  g_proper : IsProperExtendedRealFunction g
  f_closed : LowerSemicontinuous f
  g_closed : LowerSemicontinuous g
  g_convex : is_convex_function g
  f_effective_domain_convex : Convex ℝ (effective_domain f)
  g_effective_domain_subset_interior_f_effective_domain :
    effective_domain g ⊆ interior (effective_domain f)
  f_toReal_smooth_on_interior_effective_domain :
    is_l_smooth_on (fun x ↦ (f x).toReal) (interior (effective_domain f)) Lf
  optimal_set_eq :
    XStar = unconstrained_problem_solutions (composite_model_objective f g)
  optimal_set_nonempty : XStar.Nonempty
  optimal_value_isGLB :
    IsGLB (Set.range (composite_model_objective f g)) (FOpt : EReal)

namespace IsCompositeSmoothMinimizationProblem

variable {f g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}

/-- The compatibility hypothesis `effective_domain g ⊆ interior (effective_domain f)` and
properness of `g` force `effective_domain f` to be nonempty. -/
theorem f_effective_domain_nonempty
    (h : IsCompositeSmoothMinimizationProblem f g XStar FOpt Lf) :
    (effective_domain f).Nonempty := by
  rcases h.g_proper.effective_domain_nonempty with ⟨x, hx⟩
  refine ⟨x, interior_subset (h.g_effective_domain_subset_interior_f_effective_domain hx)⟩

/-- A composite smooth minimization problem canonically provides properness of the smooth term
`f`. -/
theorem f_proper
    (h : IsCompositeSmoothMinimizationProblem f g XStar FOpt Lf) :
    IsProperExtendedRealFunction f where
  ne_bot := h.f_ne_bot
  effective_domain_nonempty := h.f_effective_domain_nonempty

/-- The smooth term of a composite smooth minimization problem is proper. -/
instance instIsProperExtendedRealFunctionOfIsCompositeSmoothMinimizationProblem
    (h : IsCompositeSmoothMinimizationProblem f g XStar FOpt Lf) :
    IsProperExtendedRealFunction f :=
  h.f_proper

/-- The nonsmooth term of a composite smooth minimization problem is proper. -/
instance instIsProperExtendedRealFunctionRightOfIsCompositeSmoothMinimizationProblem
    (h : IsCompositeSmoothMinimizationProblem f g XStar FOpt Lf) :
    IsProperExtendedRealFunction g :=
  h.g_proper

/-- The nonsmooth term of a composite smooth minimization problem yields a `Fact` witness for
lower semicontinuity. -/
instance instFactLowerSemicontinuousRightOfIsCompositeSmoothMinimizationProblem
    (h : IsCompositeSmoothMinimizationProblem f g XStar FOpt Lf) :
    Fact (LowerSemicontinuous g) :=
  ⟨h.g_closed⟩

/-- The nonsmooth term of a composite smooth minimization problem yields a `Fact` witness for
convexity. -/
instance instFactIsConvexFunctionRightOfIsCompositeSmoothMinimizationProblem
    (h : IsCompositeSmoothMinimizationProblem f g XStar FOpt Lf) :
    Fact (is_convex_function g) :=
  ⟨h.g_convex⟩

end IsCompositeSmoothMinimizationProblem

end
