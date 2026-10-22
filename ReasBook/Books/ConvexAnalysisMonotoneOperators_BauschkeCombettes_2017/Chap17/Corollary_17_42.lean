/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_41

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped InnerProductSpace

universe u

namespace ERealFunction

section DifferentiabilityOfConvexFunctions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-
Source/core/bridge triage:
- `source-facing`: Corollary 17.42 is the open-set continuity consequence for a convex gradient
  field.
- `core/canonical`: the owner abstractions are `HasGateauxDerivativeOn`,
  `SelectionContinuousAt`, and ordinary continuity into `WeakSpace ℝ H`.
- `bridge/view`: Propositions 17.39 and 17.41 convert differentiability into continuity of
  subdifferential selections; the given gradient field is the source-facing singleton selection on
  `D`.
-/

-- Proof sketch: for each `y ∈ D`, openness of `D` upgrades the assumed Gâteaux derivative field on
-- `D` to a local gradient around `y`. Proposition 17.39 then identifies `gradf` with the unique
-- subgradient selection on `D`, so the induced map `D → H` is strong-to-weak continuous.
/-- Corollary 17.42 (1): if `f ∈ Γ₀(H)` admits a Gâteaux gradient field `gradf` on an open set
`D ⊆ effectiveDomain f`, then `gradf` is strong-to-weak continuous on `D`. -/
theorem gradientField_strongToWeakContinuousOn_of_mem_gammaZero_of_hasGateauxDerivativeOn
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {D : Set H} (hD_open : IsOpen D)
    (hD_dom : D ⊆ effectiveDomain f) (gradf : H → H)
    (hgrad :
      HasGateauxDerivativeOn (fun y ↦ (f y : EReal).toReal) (fun y ↦ toDual ℝ H (gradf y)) D) :
    Continuous (fun y : D ↦ toWeakSpace ℝ H (gradf y)) := sorry

-- Proof sketch: apply Proposition 17.41 at `x` to the subgradient selection induced by `gradf`.
-- The assumed Gâteaux derivative field identifies that selection with the gradient of `f` on `D`,
-- so Fréchet differentiability at `x` is equivalent to continuity of `gradf` within `D` at `x`.
/-- Corollary 17.42 (2): for `x ∈ D`, the finite representative of `f` is Fréchet differentiable
at `x` if and only if the Gâteaux gradient field `gradf` is continuous within `D` at `x`. -/
theorem
    frechetDifferentiableAt_iff_gradientField_continuousWithinAt_of_mem_gammaZero_of_hasGateauxDerivativeOn
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {D : Set H} (hD_open : IsOpen D)
    (hD_dom : D ⊆ effectiveDomain f) (gradf : H → H)
    (hgrad :
      HasGateauxDerivativeOn (fun y ↦ (f y : EReal).toReal) (fun y ↦ toDual ℝ H (gradf y)) D)
    {x : H} (hx : x ∈ D) :
    DifferentiableAt ℝ (fun y ↦ (f y : EReal).toReal) x ↔ ContinuousWithinAt gradf D x := sorry

end DifferentiabilityOfConvexFunctions

end ERealFunction
