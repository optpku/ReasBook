/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_41

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section DifferentiabilityOfConvexFunctions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/- 
Source/core/bridge triage:
- `source-facing`: Corollary 17.44 is the finite-dimensional identification of Gâteaux and
  Fréchet differentiability for a convex function on `interior (effectiveDomain f)`.
- `core/canonical`: the owner abstractions are `GateauxDifferentiableAt`,
  `DifferentiableAt`, and the subdifferential-selection criteria from Propositions 17.39 and
  17.41.
- `bridge/view`: finite dimensionality identifies weak continuity with ordinary continuity, so the
  two selection criteria become equivalent.
-/

-- Proof sketch: Proposition 17.39 characterizes Gâteaux differentiability of a `Γ₀(H)` function
-- at an interior effective-domain point by strong-to-weak continuity of subdifferential
-- selections, while Proposition 17.41 gives the analogous characterization of Fréchet
-- differentiability by ordinary continuity of selections. In finite dimensions the weak and norm
-- topologies coincide, so the two continuity conditions are equivalent.
/-- Corollary 17.44: on a finite-dimensional real Hilbert space, Gâteaux differentiability and
Fréchet differentiability coincide for a function in `Γ₀(H)` at every point of
`interior (effectiveDomain f)`. -/
theorem gateauxDifferentiableAt_iff_frechetDifferentiableAt_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x : H}
    (hx : x ∈ interior (effectiveDomain f)) :
    GateauxDifferentiableAt (fun y ↦ (f y : EReal).toReal) x ↔
      DifferentiableAt ℝ (fun y ↦ (f y : EReal).toReal) x := sorry

end DifferentiabilityOfConvexFunctions

end ERealFunction
