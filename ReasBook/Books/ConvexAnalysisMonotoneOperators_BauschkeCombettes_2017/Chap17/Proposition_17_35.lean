/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_10
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_31

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped InnerProductSpace

universe u

namespace ERealFunction

section DifferentiabilityOfConvexFunctions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 17.35 evaluates the source-facing Fenchel conjugate of `f` at the
  Gâteaux gradient `gradf` of `f` at `x`.
- `core/canonical`: the owner abstractions are the conjugate `f.asEReal∗`, the subdifferential
  `∂ f`, and `HasGateauxDerivativeAt`.
- `bridge/view`: Proposition 17.31 turns the Gâteaux gradient into the singleton subdifferential
  at `x`, and Proposition 16.10 rewrites subgradient membership as Fenchel--Young equality. -/

-- Proof sketch: Proposition 17.31 (1) identifies the subdifferential at `x` with the singleton
-- `{gradf}`, so `gradf ∈ (∂ f) x`. Proposition 16.10 then gives the Fenchel--Young equality
-- `(f x : EReal) + f^*(gradf) = ⟪x, gradf⟫`, and rearranging isolates the conjugate value.
/-- Proposition 17.35: if a proper convex `]-∞,+∞]`-valued function is Gâteaux differentiable at
`x` with gradient `gradf`, then the Fenchel conjugate of `f` at `gradf` is
`⟪x, gradf⟫ - f x`. -/
theorem conjugate_gateauxGradient_eq_inner_sub_of_hasGateauxDerivativeAt
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) (gradf : H)
    (hgrad :
      HasGateauxDerivativeAt (fun z ↦ (f z : EReal).toReal) (toDualMap ℝ H gradf) x) :
    f.asEReal∗ gradf = ((⟪x, gradf⟫_ℝ : ℝ) : EReal) - f x := sorry

end DifferentiabilityOfConvexFunctions

end ERealFunction
