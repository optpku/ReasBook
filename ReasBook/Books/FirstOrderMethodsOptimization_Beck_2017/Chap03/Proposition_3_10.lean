/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_9
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_9
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_10
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Lemma_3_2_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Topology
open Module.Dual

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 3.10 is a `bridge/view` reformulation of the Chapter 3 max formula from
`Definition_3_9`: the owner notions remain `directional_derivative` and `subdifferential`, while
the support-function expression is the Chapter 2 canonical reformulation. -/
recall support_function
recall directional_derivative
recall is_convex_function
recall subdifferential
recall finite_domain
recall directional_derivative_isGreatest_subgradient_pairings_at_interior_point
recall support_function_eq_of_isGreatest_image
recall properExtendedRealFunctionOfConvexInteriorFiniteDomain

-- Proof sketch: apply the owner theorem
-- `directional_derivative_isGreatest_subgradient_pairings_at_interior_point` from
-- `Definition_3_9`, then rewrite the resulting maximum formula through the canonical support
-- function owner lemma `support_function_eq_of_isGreatest_image`. The chapter's owner-side
-- qualification is `x ∈ interior (finite_domain f)`, from which the properness instance and the
-- effective-domain interior hypothesis are derived internally.
/-- Proposition 3.10: for a convex extended-real-valued function, at a point in the interior of
its finite domain the directional derivative equals the support function of the subdifferential
evaluated at the canonical functional `Module.Dual.eval ℝ E d`. -/
theorem directional_derivative_eq_support_function_subdifferential_at_interior_point
    {f : E → EReal} {x d : E} (hconvex : is_convex_function f)
    (hx : x ∈ interior (finite_domain f)) :
    directional_derivative f x d = support_function (∂f(x)) (eval ℝ E d) := by
  letI : IsProperExtendedRealFunction f :=
    properExtendedRealFunctionOfConvexInteriorFiniteDomain (f := f) (x := x) hconvex hx
  have hx_effective : x ∈ interior (effective_domain f) :=
    interior_mono (fun _ hz ↦ hz.1) hx
  symm
  refine support_function_eq_of_isGreatest_image (∂f(x)) (eval ℝ E d) ?_
  simpa [eval_apply] using
    directional_derivative_isGreatest_subgradient_pairings_at_interior_point
      hconvex hx_effective

end
