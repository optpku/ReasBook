/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_3
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 10.67 is `source-facing`: it records the standing assumptions for the non-Euclidean
proximal gradient method. Domain sampling in the surrounding chapter points to the Chapter 10
owner `IsCompositeSmoothMinimizationProblem` from Definition 10.3 as the `core/canonical` ambient
problem class, while Definition 10.67 adds the extra convexity clause for the smooth term `f`.
Because `f_effective_domain_convex` is derivable from `f_convex`, the primitive 10.67 data should
expose the underlying textbook clauses directly and recover the Chapter 10 owner by a separate
bridge theorem rather than storing the stronger owner as primitive data. -/

/-- Definition 10.67: Assumption 10.77 for the non-Euclidean proximal gradient method means that
`g : E → (-∞, ∞]` is proper, closed, and convex; `f : E → (-∞, ∞]` is proper, closed, and convex
with `effective_domain g ⊆ interior (effective_domain f)` and
`(fun x ↦ (f x).toReal)` `L_f`-smooth on `interior (effective_domain f)`; and
`XStar = X^*` is the nonempty optimal solution set of `min_x (f x + g x)` with optimal value
`FOpt = F_opt`. -/
class IsConvexCompositeSmoothMinimizationProblem
    (f g : E → EReal) (XStar : outParam (Set E)) (FOpt : outParam ℝ) (Lf : NNReal) : Prop
    where
  f_ne_bot : ∀ x, f x ≠ ⊥
  g_proper : IsProperExtendedRealFunction g
  f_closed : LowerSemicontinuous f
  g_closed : LowerSemicontinuous g
  f_convex : is_convex_function f
  g_convex : is_convex_function g
  g_effective_domain_subset_interior_f_effective_domain :
    effective_domain g ⊆ interior (effective_domain f)
  f_toReal_smooth_on_interior_effective_domain :
    is_l_smooth_on (fun x ↦ (f x).toReal) (interior (effective_domain f)) Lf
  optimal_set_eq :
    XStar = unconstrained_problem_solutions (composite_model_objective f g)
  optimal_set_nonempty : XStar.Nonempty
  optimal_value_isGLB :
    IsGLB (Set.range (composite_model_objective f g)) (FOpt : EReal)

/-- In Definition 10.67, convexity of `effective_domain f` is derived from convexity of `f`. -/
theorem IsConvexCompositeSmoothMinimizationProblem.f_effective_domain_convex
    {f g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
    (h : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf) :
    Convex ℝ (effective_domain f) :=
  effective_domain_convex_of_is_convex_function h.f_convex

/-- Definition 10.67 canonically induces the Chapter 10 composite smooth minimization owner, with
the convexity of `effective_domain f` recovered from `f_convex`. -/
theorem IsConvexCompositeSmoothMinimizationProblem.toIsCompositeSmoothMinimizationProblem
    {f g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
    (h : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf) :
    IsCompositeSmoothMinimizationProblem f g XStar FOpt Lf := by
  refine
    { f_ne_bot := h.f_ne_bot
      g_proper := h.g_proper
      f_closed := h.f_closed
      g_closed := h.g_closed
      g_convex := h.g_convex
      f_effective_domain_convex := h.f_effective_domain_convex
      g_effective_domain_subset_interior_f_effective_domain :=
        h.g_effective_domain_subset_interior_f_effective_domain
      f_toReal_smooth_on_interior_effective_domain :=
        h.f_toReal_smooth_on_interior_effective_domain
      optimal_set_eq := h.optimal_set_eq
      optimal_set_nonempty := h.optimal_set_nonempty
      optimal_value_isGLB := h.optimal_value_isGLB }

/-- The nonsmooth term of a convex composite smooth minimization problem is proper. -/
instance instIsProperExtendedRealFunctionRightOfIsConvexCompositeSmoothMinimizationProblem
    {f g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
    (h : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf) :
    IsProperExtendedRealFunction g :=
  h.g_proper

/-- The nonsmooth term of a convex composite smooth minimization problem yields a `Fact` witness
for lower semicontinuity. -/
instance instFactLowerSemicontinuousRightOfIsConvexCompositeSmoothMinimizationProblem
    {f g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
    (h : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf) :
    Fact (LowerSemicontinuous g) :=
  ⟨h.g_closed⟩

/-- The nonsmooth term of a convex composite smooth minimization problem yields a `Fact` witness
for convexity. -/
instance instFactIsConvexFunctionRightOfIsConvexCompositeSmoothMinimizationProblem
    {f g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
    (h : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf) :
    Fact (is_convex_function g) :=
  ⟨h.g_convex⟩

/-- The smooth term of a convex composite smooth minimization problem yields a `Fact` witness for
convexity. -/
instance instIsConvexFunctionLeftOfIsConvexCompositeSmoothMinimizationProblem
    {f g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
    (h : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf) :
    is_convex_function f :=
  h.f_convex

/-- The smooth term of a convex composite smooth minimization problem yields a `Fact` witness for
convexity. -/
instance instFactIsConvexFunctionLeftOfIsConvexCompositeSmoothMinimizationProblem
    {f g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
    (h : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf) :
    Fact (is_convex_function f) :=
  ⟨h.f_convex⟩

/-- Any point in the optimal set `XStar` attains the optimal value `FOpt` for the composite
objective. -/
theorem IsConvexCompositeSmoothMinimizationProblem.objective_eq_optimalValue_of_mem_optimalSet
    {f g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
    (h : IsConvexCompositeSmoothMinimizationProblem f g XStar FOpt Lf)
    {x : E} (hx : x ∈ XStar) :
    composite_model_objective f g x = (FOpt : EReal) := by
  apply le_antisymm
  · exact h.optimal_value_isGLB.2 <| by
      rintro _ ⟨y, rfl⟩
      have hx_opt : x ∈ unconstrained_problem_solutions (composite_model_objective f g) := by
        simpa [h.optimal_set_eq] using hx
      exact (mem_unconstrained_problem_solutions_iff_forall_le.mp hx_opt) y
  · exact h.optimal_value_isGLB.1 ⟨x, rfl⟩

end

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

namespace IsConvexCompositeSmoothMinimizationProblem

/-- Bridge/view layer: a convex composite smooth minimization problem for `f.toEReal` canonically
supplies the Chapter 10 prox-gradient residual at parameter `L` without repeating the regularity
data for `g` on the theorem surface. -/
abbrev gradientMapping
    {f : E → ℝ} {g : E → EReal} {XStar : Set E} {FOpt : ℝ} {Lf : NNReal}
    (hproblem : IsConvexCompositeSmoothMinimizationProblem f.toEReal g XStar FOpt Lf)
    (L : PosReal) : E → E :=
  letI : IsProperExtendedRealFunction g := hproblem.g_proper
  letI : Fact (LowerSemicontinuous g) := ⟨hproblem.g_closed⟩
  letI : Fact (is_convex_function g) := ⟨hproblem.g_convex⟩
  G[L; f, g]

end IsConvexCompositeSmoothMinimizationProblem

end
