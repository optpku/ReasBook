/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/- Assumption 8.7 is `source-facing`: it fixes the standing convex-optimization hypotheses for the
constrained problem `min {f x : x ∈ C}` used later by the projected subgradient method. The
canonical owners already present in the project are `IsProperExtendedRealFunction`,
`LowerSemicontinuous`, `is_convex_function`, `constrained_problem_solutions`, and `IsGLB`, so the
assumption is recorded directly as a Prop-valued class on the objective, feasible set, optimal
set, and optimal value, with no surrogate algorithm-branded wrapper. -/

/-- Assumption 8.7: clauses (A)-(D) hold for the constrained convex problem `min {f x : x ∈ C}`,
namely `f` is
proper, closed, and convex, `C` is a nonempty closed convex subset of `interior (dom(f))`,
`XStar` is the nonempty optimal set of the constrained problem `min {f x : x ∈ C}`, and `fOpt`
is its optimal value. -/
class IsConstrainedConvexProblem
    (f : E → EReal) (C XStar : Set E) (fOpt : ℝ) : Prop
    extends IsProperExtendedRealFunction f where
  closed : LowerSemicontinuous f
  convex : is_convex_function f
  feasible_nonempty : C.Nonempty
  feasible_closed : IsClosed C
  feasible_convex : Convex ℝ C
  feasible_subset_interior_effective_domain : C ⊆ interior (effective_domain f)
  optimal_set_eq : XStar = constrained_problem_solutions f C
  optimal_set_nonempty : XStar.Nonempty
  optimal_value_isGLB : IsGLB (f '' C) (fOpt : EReal)

/-- A constrained convex problem packages both existence of minimizers and the
greatest-lower-bound characterization of the optimal value. -/
instance instFactConstrainedConvexOptimalSetNonemptyAndOptimalValueIsGLB
    {f : E → EReal} {C XStar : Set E} {fOpt : ℝ}
    [h : IsConstrainedConvexProblem f C XStar fOpt] :
    Fact (XStar.Nonempty ∧ IsGLB (f '' C) (fOpt : EReal)) where
  out := ⟨h.optimal_set_nonempty, h.optimal_value_isGLB⟩

end
