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

open InnerProductSpace
open scoped InnerProductSpace

universe u

namespace ERealFunction

section DifferentiabilityAndStrictConvexity

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: apply Corollary 18.11 to convert Gâteaux differentiability of `f` into strict
-- convexity of `f∗[hf]` on every nonempty convex subset of `dom (∂ f*)`, then use `hdom_conj` to
-- identify that domain with `interior (effectiveDomain (f∗[hf]))`.
-- The reverse implication restricts strict convexity on the whole interior effective domain to the
-- convex subsets required by Corollary 18.11.
/-- Corollary 18.12 (1): if `f ∈ Γ₀(H)` and both `f` and its Fenchel conjugate `f*`, represented
by `f∗[hf]`, satisfy `dom (∂ ·) = interior (effectiveDomain ·)`, then the
finite-valued representative of `f` is Gâteaux differentiable on `interior (effectiveDomain f)` if
and only if `f*` is strictly convex on `interior (effectiveDomain f*)`. -/
theorem
    gateauxDifferentiableOn_interior_effectiveDomain_iff_strictlyConvexOn_interior_effectiveDomain_gammaZeroConjugate
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (hdom : SetValuedOperator.dom (∂ f) = interior (effectiveDomain f))
    (hdom_conj :
      SetValuedOperator.dom (∂ (f∗[hf])) = interior (effectiveDomain (f∗[hf]))) :
    GateauxDifferentiableOn (fun x ↦ (f x : EReal).toReal) (interior (effectiveDomain f)) ↔
      StrictlyConvexOn (f∗[hf]) (interior (effectiveDomain (f∗[hf]))) := sorry

-- Proof sketch: apply Corollary 18.12 (1) to `f∗[hf]`. Corollary 13.38 supplies that
-- `f∗[hf] ∈ Γ₀(H)`, and the biconjugate-identification part of Corollary
-- 13.38 converts strict convexity of the double conjugate back to strict convexity of `f` on
-- `interior (effectiveDomain f)`.
/-- Corollary 18.12 (2): if `f ∈ Γ₀(H)` and both `f` and its Fenchel conjugate `f*`, represented
by `f∗[hf]`, satisfy `dom (∂ ·) = interior (effectiveDomain ·)`, then `f` is
strictly convex on `interior (effectiveDomain f)` if and only if `f*` is Gâteaux differentiable on
`interior (effectiveDomain f*)`. -/
theorem
    strictlyConvexOn_interior_effectiveDomain_iff_gateauxDifferentiableOn_interior_effectiveDomain_gammaZeroConjugate
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (hdom : SetValuedOperator.dom (∂ f) = interior (effectiveDomain f))
    (hdom_conj :
      SetValuedOperator.dom (∂ (f∗[hf])) = interior (effectiveDomain (f∗[hf]))) :
    StrictlyConvexOn f (interior (effectiveDomain f)) ↔
      GateauxDifferentiableOn (fun u ↦ (f∗[hf] u : EReal).toReal)
        (interior (effectiveDomain (f∗[hf]))) := sorry

end DifferentiabilityAndStrictConvexity

end ERealFunction
