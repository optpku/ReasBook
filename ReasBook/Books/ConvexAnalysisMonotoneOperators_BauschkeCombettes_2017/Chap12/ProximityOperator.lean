/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_23

universe u

open scoped InnerProductSpace

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

section GammaZero

variable (f : H → Set.Ioi (⊥ : EReal))

-- Proof sketch: use the existence and uniqueness theory of proximal points for proper lower
-- semicontinuous convex functions on a Hilbert space.
/-- A function in `Γ₀(H)` has a unique proximal point at every base point. -/
theorem hasUniqueProxPoint_of_mem_gammaZero (hf : f ∈ Γ₀(H)) :
    HasUniqueProxPoint f := sorry

/-- Source-facing notation for the proximity operator of a `Γ₀(H)` function, obtained from the
canonical owner `proximityOperator` via the unique-prox-point bridge above. -/
notation "Prox[" f ", " hf "]" =>
  proximityOperator f (hasUniqueProxPoint_of_mem_gammaZero f hf)

end GammaZero

end ERealFunction
