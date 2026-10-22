/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_49
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_30
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Proposition_10_2
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Proposition_10_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

universe u

namespace ERealFunction

section Linear

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

private theorem convex_epigraph_of_convexOn_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f)) :
    Convex ℝ (epigraph (fun x : H ↦ (f x : EReal))) := by
  refine (convex_epigraph_iff_jensen_on_dom (fun x : H ↦ (f x : EReal))).2 ?_
  intro x y hx hy α hα hα_lt_one
  have hx' : x ∈ effectiveDomain f := by
    simpa [effectiveDomain, dom] using hx
  have hy' : y ∈ effectiveDomain f := by
    simpa [effectiveDomain, dom] using hy
  simpa using hconv.ineq hx' hy' hα hα_lt_one

-- Proof sketch: identify the epigraph of the recession function with the recession cone of the
-- epigraph, then use that recession cones of convex sets are cones.
/-- The recession function of a proper convex `]-∞,+∞]`-valued function is positively
homogeneous. -/
theorem recessionFunction_positivelyHomogeneous
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f)) :
    PositivelyHomogeneous (fun y : H ↦ (recessionFunction f hconv.nonempty y : EReal)) := by
  have hconv_epi := convex_epigraph_of_convexOn_effectiveDomain f hconv
  rw [positivelyHomogeneous_iff_isCone_epigraph]
  rw [epigraph_recessionFunction_eq_recessionCone_epigraph f hconv]
  simpa using Set.recessionCone_isCone hconv_epi

-- Proof sketch: the epigraph identity with the recession cone preserves convexity, while
-- Example 10.6 (1) gives positive homogeneity. Proposition 10.3 then identifies convex epigraph
-- with sublinearity for a positively homogeneous `]-∞,+∞]`-valued function.
/-- The recession function of a proper convex `]-∞,+∞]`-valued function is sublinear. -/
theorem recessionFunction_sublinear
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f)) :
    Sublinear (fun y : H ↦ (recessionFunction f hconv.nonempty y : EReal)) := by
  let g : H → Set.Ioi (⊥ : EReal) := recessionFunction f hconv.nonempty
  have hconv_epi_f := convex_epigraph_of_convexOn_effectiveDomain f hconv
  have hph : PositivelyHomogeneous (fun y : H ↦ (g y : EReal)) := by
    simpa [g] using recessionFunction_positivelyHomogeneous f hconv
  have hconv_epi_g : Convex ℝ (epigraph (fun y : H ↦ (g y : EReal))) := by
    rw [show epigraph (fun y : H ↦ (g y : EReal)) =
      epigraph (fun y : H ↦ (recessionFunction f hconv.nonempty y : EReal)) by rfl]
    rw [epigraph_recessionFunction_eq_recessionCone_epigraph f hconv]
    simpa using Set.recessionCone_convex hconv_epi_f
  exact (sublinear_iff_isConvex_of_positivelyHomogeneous g hph).2
    (isConvex_of_convex_epigraph g hconv_epi_g)

end Linear

section LinearTopological

variable {H : Type u} [TopologicalSpace H] [AddCommGroup H] [Module ℝ H]

/-- Example 10.6: the recession function of a `Γ₀(H)` function is sublinear. -/
theorem recessionFunction_sublinear_of_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    Sublinear (fun y : H ↦ (recessionFunction f hf.2.nonempty y : EReal)) := by
  simpa using recessionFunction_sublinear f hf.2

end LinearTopological

end ERealFunction
