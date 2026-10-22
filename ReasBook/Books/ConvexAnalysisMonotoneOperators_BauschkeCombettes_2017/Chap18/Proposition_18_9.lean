/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_10
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Definition_2_54
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Definition_8_7
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section DifferentiabilityAndStrictConvexity

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: fix `x ∈ interior (effectiveDomain f)`. Corollary 8.39 gives continuity of `f`
-- on the effective domain at `x`, so Proposition 17.31 (2) will apply once the subdifferential is
-- shown to be a singleton. If `u₁, u₂ ∈ (∂ f) x`, then Corollary 16.30 moves the whole segment
-- `segment ℝ u₁ u₂` into `dom (∂ f*)`, where the hypothesis gives strict convexity of `f*` on
-- that segment. Proposition 16.37 (1) also makes `f*` affine on the segment, forcing `u₁ = u₂`;
-- then Proposition 17.31 (2) yields Gâteaux differentiability at `x`.
/-- Proposition 18.9: if `f ∈ Γ₀(H)` and the Fenchel conjugate `f*`, represented by
`f∗[hf]`, is strictly convex on every nonempty convex subset of the domain of its
subdifferential, then the finite-valued representative of `f` is Gâteaux differentiable on
`interior (effectiveDomain f)`. -/
theorem
    gateauxDifferentiableOn_interior_effectiveDomain_of_strictlyConvexOn_every_nonempty_convex_subset_subdifferentialDom_gammaZeroConjugate
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (hstrict :
      ∀ ⦃C : Set H⦄, C.Nonempty → Convex ℝ C →
        C ⊆ SetValuedOperator.dom (∂ (f∗[hf])) →
        StrictlyConvexOn (f∗[hf]) C) :
    GateauxDifferentiableOn (fun x ↦ (f x : EReal).toReal) (interior (effectiveDomain f)) := sorry

end DifferentiabilityAndStrictConvexity

end ERealFunction
