/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Definition_2_54
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Theorem_16_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_31

-- Declarations for this item will be appended below by the statement pipeline.

open InnerProductSpace
open scoped InnerProductSpace

universe u

namespace ERealFunction

section DifferentiabilityOfConvexFunctions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: Fermat's rule identifies global minimizers with zeros of the subdifferential.
-- Proposition 17.31 identifies the subdifferential at `x` with the singleton `{gradf}`, so
-- `0 ∈ (∂ f) x` is equivalent to `gradf = 0`.
/-- Proposition 17.4: if a convex `]-∞,+∞]`-valued function is Gâteaux differentiable at an
effective-domain point `x` with Gâteaux gradient `gradf`, then `x` is a global minimizer exactly
when the gradient vanishes. -/
theorem mem_argmin_iff_gateauxGradient_eq_zero
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hx : x ∈ effectiveDomain f) (gradf : H)
    (hgrad :
      HasGateauxDerivativeAt (fun z ↦ (f z : EReal).toReal) (toDual ℝ H gradf) x) :
    x ∈ Argmin f ↔ gradf = 0 := by
  rw [argmin_eq_zeros_subdifferential, SetValuedOperator.mem_zeros_iff,
    subdifferential_eq_singleton_of_hasGateauxDerivativeAt f hx gradf hgrad]
  simp [eq_comm]

end DifferentiabilityOfConvexFunctions

end ERealFunction
