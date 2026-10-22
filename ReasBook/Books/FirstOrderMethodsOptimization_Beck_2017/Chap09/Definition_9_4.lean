/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Source-facing note: this item fixes the standing assumptions for the composite mirror-descent
problem `min_x (f x + g x)`. The canonical owners already present in the project are
`IsProperExtendedRealFunction`, `LowerSemicontinuous`, `is_convex_function`,
`SubgradientNormBoundOn`, mathlib's minimizer predicate `IsMinOn`, and `IsGLB`. The source item
includes both the optimizer/value data and the bounded-subgradient constant `L_f`, but later
Chapter 9 statements do not always use the bound. To avoid baking the `L_f` package into
unrelated theorem surfaces, the public API separates the core composite convex minimization owner
from the stronger source-facing mirror-descent problem owner. -/

/-- The core composite-convex minimization assumptions for `min_x (f x + g x)`: `f` and `g` are
proper, closed, and convex, `dom(g) ⊆ interior(dom(f))`, and `XStar = X^*` is the nonempty
optimal set with optimal value `FOpt = F_opt`. -/
class IsCompositeConvexMinimizationProblem
    (f g : E → EReal) (XStar : Set E) (FOpt : ℝ)
    : Prop extends IsProperExtendedRealFunction f where
  g_proper : IsProperExtendedRealFunction g
  f_closed : LowerSemicontinuous f
  f_convex : is_convex_function f
  g_closed : LowerSemicontinuous g
  g_convex : is_convex_function g
  g_effective_domain_subset_interior_f_effective_domain :
    effective_domain g ⊆ interior (effective_domain f)
  optimal_set_eq : XStar = {x | IsMinOn (fun y ↦ f y + g y) Set.univ x}
  optimal_set_nonempty : XStar.Nonempty
  optimal_value_isGLB : IsGLB (Set.range (fun x ↦ f x + g x)) (FOpt : EReal)

/-- Definition 9.4: clauses (A)-(D) for the composite mirror-descent problem
`min_x {F(x) = f(x) + g(x)}` mean the core composite-convex assumptions together with the
bounded-subgradient clause that every continuous-dual subgradient of `f` at every point of
`dom(g)` has norm at most `L_f > 0`. -/
class IsCompositeMirrorDescentProblem
    (f g : E → EReal) (XStar : Set E) (FOpt Lf : ℝ)
    : Prop extends IsCompositeConvexMinimizationProblem f g XStar FOpt where
  Lf_pos : 0 < Lf
  subgradient_norm_le {x : E} {s : StrongDual ℝ E}
      (hx : x ∈ effective_domain g) (hs : s ∈ strongDualSubdifferential f x) :
      ‖s‖ ≤ Lf

/-- A composite convex minimization problem packages both existence of minimizers and the
greatest-lower-bound characterization of the optimal value. -/
instance instFactCompositeOptimalSetNonemptyAndOptimalValueIsGLB
    {f g : E → EReal} {XStar : Set E} {FOpt : ℝ}
    [h : IsCompositeConvexMinimizationProblem f g XStar FOpt] :
    Fact (XStar.Nonempty ∧ IsGLB (Set.range (fun x ↦ f x + g x)) (FOpt : EReal)) where
  out := ⟨h.optimal_set_nonempty, h.optimal_value_isGLB⟩

/-- A composite mirror-descent problem canonically induces the Chapter 8 bounded-subgradient
owner on `effective_domain g`. -/
def IsCompositeMirrorDescentProblem.subgradientNormBoundOn
    {f g : E → EReal} {XStar : Set E} {FOpt Lf : ℝ}
    (h : IsCompositeMirrorDescentProblem f g XStar FOpt Lf) :
    SubgradientNormBoundOn f (effective_domain g) :=
  { L_f := Lf
    L_f_pos := h.Lf_pos
    norm_le := h.subgradient_norm_le }

/-- A composite mirror-descent problem canonically packages nonemptiness of the optimal set, the
greatest-lower-bound characterization of the optimal value, and positivity of `L_f`. -/
instance instFactCompositeOptimalSetNonemptyOptimalValueIsGLBAndLfPos
    {f g : E → EReal} {XStar : Set E} {FOpt Lf : ℝ}
    [h : IsCompositeMirrorDescentProblem f g XStar FOpt Lf] :
    Fact (XStar.Nonempty ∧ IsGLB (Set.range (fun x ↦ f x + g x)) (FOpt : EReal) ∧ 0 < Lf) where
  out := ⟨h.optimal_set_nonempty, h.optimal_value_isGLB, h.Lf_pos⟩

end
