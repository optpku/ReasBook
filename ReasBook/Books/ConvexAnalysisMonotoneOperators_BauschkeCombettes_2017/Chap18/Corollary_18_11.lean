/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap18.Proposition_18_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap18.Proposition_18_10

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped InnerProductSpace

universe u

namespace ERealFunction

section DifferentiabilityAndStrictConvexity

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: apply Proposition 18.9 for the reverse implication. For the forward implication,
-- use Proposition 18.10 on the source-facing gradient image and then rewrite
-- `SetValuedOperator.dom (∂ (f∗[hf]))` as that gradient image via
-- `subdifferentialDom_gammaZeroConjugate_eq_gradientImage_of_hasGateauxDerivativeOn`; the extra
-- hypothesis `dom (∂ f) = interior (effectiveDomain f)` is exactly what supplies that bridge.
/-- Corollary 18.11: if `f ∈ Γ₀(H)` and `dom (∂ f) = interior (effectiveDomain f)`, then the
finite-valued representative of `f` is Gâteaux differentiable on `interior (effectiveDomain f)` if
and only if the Fenchel conjugate `f*`, represented by `f∗[hf]`, is strictly
convex on every nonempty convex subset of the domain of its subdifferential. -/
theorem
    gateauxDifferentiableOn_interior_effectiveDomain_iff_strictlyConvexOn_every_nonempty_convex_subset_subdifferentialDom_gammaZeroConjugate
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (hdom : SetValuedOperator.dom (∂ f) = interior (effectiveDomain f)) :
    GateauxDifferentiableOn (fun x ↦ (f x : EReal).toReal) (interior (effectiveDomain f)) ↔
      ∀ ⦃C : Set H⦄, C.Nonempty → Convex ℝ C →
        C ⊆ SetValuedOperator.dom (∂ (f∗[hf])) →
        StrictlyConvexOn (f∗[hf]) C := sorry

end DifferentiabilityAndStrictConvexity

end ERealFunction
