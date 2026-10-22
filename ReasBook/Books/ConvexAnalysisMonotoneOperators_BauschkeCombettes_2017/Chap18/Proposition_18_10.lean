/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
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

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (gradf : H → H)

/- Source/core/bridge triage:
- `source-facing`: Proposition 18.10 is the strict-convexity statement on the gradient image
  `gradf '' interior (effectiveDomain f)`.
- `core/canonical`: Proposition 18.9 uses strict convexity on nonempty convex subsets of
  `SetValuedOperator.dom (∂ (f∗[hf]))`.
- `bridge/view`: the Gâteaux gradient image maps into that canonical subdifferential domain, and
  the next theorem upgrades this bridge to an equality under the additional hypothesis
  `SetValuedOperator.dom (∂ f) = interior (effectiveDomain f)`.

This file therefore stays source-facing: it keeps the gradient-image statement as the main public
result and records only the inclusion bridge needed by the later domain-equality reformulation. -/

-- Proof sketch: for `u ∈ dom (∂ f*)`, choose `x` with `x ∈ ∂ f*(u)`. Corollary 16.30 moves this
-- to `u ∈ ∂ f(x)`, and Proposition 17.31 identifies `u` with the Gâteaux gradient at `x`.
theorem gradientImage_subset_subdifferentialDom_gammaZeroConjugate_of_hasGateauxDerivativeOn
    (hgrad :
      HasGateauxDerivativeOn (fun x ↦ (f x : EReal).toReal)
        (fun x ↦ toDualMap ℝ H (gradf x))
        (interior (effectiveDomain f)))
    :
    gradf '' interior (effectiveDomain f) ⊆ SetValuedOperator.dom (∂ (f∗[hf])) := sorry

-- Proof sketch: Proposition 18.10 supplies the inclusion from the gradient image into
-- `dom (∂ f*)`. Conversely, if `y ∈ dom (∂ f*)`, Corollary 16.30 yields some
-- `x ∈ dom (∂ f) = interior (effectiveDomain f)` with `y ∈ (∂ f) x`, and Proposition 17.31 (1)
-- identifies that subgradient with `gradf x`.
/-- If `f ∈ Γ₀(H)` has `dom (∂ f) = interior (effectiveDomain f)` and an explicit Gâteaux gradient
field `gradf` on `interior (effectiveDomain f)`, then the domain of the subdifferential of
`f∗[hf]` is exactly the gradient image `gradf '' interior (effectiveDomain f)`. -/
theorem subdifferentialDom_gammaZeroConjugate_eq_gradientImage_of_hasGateauxDerivativeOn
    (hdom : SetValuedOperator.dom (∂ f) = interior (effectiveDomain f))
    (hgrad :
      HasGateauxDerivativeOn (fun x ↦ (f x : EReal).toReal)
        (fun x ↦ toDualMap ℝ H (gradf x))
        (interior (effectiveDomain f))) :
    SetValuedOperator.dom (∂ (f∗[hf])) = gradf '' interior (effectiveDomain f) :=
  sorry

-- Proof sketch: if `f*` were affine on a nontrivial segment inside a convex set `C`, then every
-- interior point of that segment would still belong to `C` and hence to the gradient image
-- `gradf '' interior (effectiveDomain f)`. Choose `x` in the interior effective domain with
-- `gradf x` on the open segment. Proposition 17.31 identifies `gradf x` with the unique
-- subgradient of `f` at `x`, so Corollary 16.30 puts `x` in the subdifferential of `f*` at
-- `gradf x`. Proposition 16.37 (2) then forces the whole segment into `(∂ f) x`, contradicting
-- the singleton subdifferential furnished by Gâteaux differentiability at `x`.
/-- Proposition 18.10: if `f ∈ Γ₀(H)` and `gradf` is a Gâteaux gradient field of the finite-valued
representative of `f` on `interior (effectiveDomain f)`, then the Fenchel conjugate `f*`,
represented by `f∗[hf]`, is strictly convex on every nonempty convex subset of the
gradient image `gradf '' interior (effectiveDomain f)`. -/
theorem gammaZeroConjugate_strictlyConvexOn_of_hasGateauxDerivativeOn
    (hgrad :
      HasGateauxDerivativeOn (fun x ↦ (f x : EReal).toReal)
        (fun x ↦ toDualMap ℝ H (gradf x))
        (interior (effectiveDomain f)))
    {C : Set H} (hC_nonempty : C.Nonempty) (hC_convex : Convex ℝ C)
    (hC_subset : C ⊆ gradf '' interior (effectiveDomain f)) :
    StrictlyConvexOn (f∗[hf]) C := sorry

end DifferentiabilityAndStrictConvexity

end ERealFunction
