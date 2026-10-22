/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_6
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_14
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Theorem_17_18

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped InnerProductSpace

universe u

namespace ERealFunction

section DifferentiabilityOfConvexFunctions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))

/- Source/core/bridge triage:
- `source-facing`: Proposition 17.31 identifies Gâteaux differentiability at `x` with the
  singleton shape of the source-facing subdifferential `∂ f x`.
- `core/canonical`: the owner abstractions are `HasGateauxDerivativeAt`, `∂`, `directionalDerivative`,
  and `ContinuousAtOnEffectiveDomain`.
- `bridge/view`: Proposition 17.6 supplies the canonical map from a Gâteaux gradient to a
  subgradient, Proposition 17.14 compares subgradients with directional derivatives, and
  Theorem 17.18 rewrites `directionalDerivative f x` as the support function of `∂ f x`. -/

-- Proof sketch: Proposition 17.6 shows that a Gâteaux gradient `gradf` at `x` is a subgradient.
-- For any other `u ∈ ∂ f(x)`, Proposition 17.14 (1) compares both `u` and `gradf` with the
-- directional derivative, and the Gâteaux derivative formula forces
-- `⟪u - gradf, u - gradf⟫ ≤ 0`, hence `u = gradf`.
/-- Proposition 17.31 (1): at an effective-domain point of a convex `]-∞,+∞]`-valued function,
the subdifferential of `f` is the singleton consisting of its Gâteaux gradient. -/
theorem subdifferential_eq_singleton_of_hasGateauxDerivativeAt
    {x : H} (hx : x ∈ effectiveDomain f) (gradf : H)
    (hgrad :
      HasGateauxDerivativeAt (fun z ↦ (f z : EReal).toReal) (toDualMap ℝ H gradf) x) :
    (∂ f) x = ({gradf} : Set H) := sorry

variable [CompleteSpace H]

-- Proof sketch: Theorem 17.18 identifies the directional derivative at `x` with the support
-- function of the singleton subdifferential `{u}`, so `f'(x; y) = ⟪y, u⟫` for every direction
-- `y`. The characterization of Gâteaux differentiability by directional derivatives then gives the
-- derivative `toDualMap ℝ H u` at `x`.
/-- Proposition 17.31 (2): at a continuity point on the effective domain of a convex
`]-∞,+∞]`-valued function, if the subdifferential at `x` is the singleton `{u}`, then the finite
representative of `f` is Gâteaux differentiable at `x` with gradient `u`. -/
theorem hasGateauxDerivativeAt_of_subdifferential_eq_singleton_of_continuousAtOnEffectiveDomain
    {x u : H} (hxcont : ContinuousAtOnEffectiveDomain f x) (hsub : (∂ f) x = ({u} : Set H)) :
    HasGateauxDerivativeAt (fun z ↦ (f z : EReal).toReal) (toDualMap ℝ H u) x := sorry

end DifferentiabilityOfConvexFunctions

end ERealFunction
