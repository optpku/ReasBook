/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Corollary_12_18
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap18.Theorem_18_15

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient InnerProductSpace

universe u

namespace ERealFunction

section MoreauCharacterizationOfSmoothConvexFunctions

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: use `hf : f.toEReal ∈ Γ₀(H)` to recover the continuity and convexity
-- hypotheses needed for Theorem 18.15, then apply the equivalence between clause `(i)` and clause
-- `(viii)`.
/-- Corollary 18.19: for `f ∈ Γ₀(H)` viewed through its real-valued representative and
`β ∈ ℝ_{++}`, `f` is Fréchet differentiable on `H` with `β`-Lipschitz gradient if and only if
`f` is the Moreau envelope of parameter `1 / β` of the canonical function
`(f^* - β⁻¹ q)^*`, where `q(x) = ‖x‖² / 2`. -/
theorem hasLipschitzGradient_iff_hasMoreauEnvelopeRepresentation_of_mem_gammaZero
    (f : H → ℝ) (hf : f.toEReal ∈ Γ₀(H)) (β : Set.Ioi (0 : ℝ)) :
    HasLipschitzGradient f β ↔ HasMoreauEnvelopeRepresentation f β := sorry

-- Proof sketch: this is exactly the `primal_moreau_eq` field of
-- `HasMoreauEnvelopeRepresentation f β`.
/-- The Moreau-envelope side of the corollary yields the explicit identity
`f = ((f^* - β⁻¹ q)^*) □ β q`, encoded as an equality with the parameter `1 / β` Moreau envelope
of the shifted conjugate. -/
theorem toEReal_eq_moreauEnvelope_shiftedConjugate_of_hasMoreauEnvelopeRepresentation
    (f : H → ℝ) (β : Set.Ioi (0 : ℝ)) (hrep : HasMoreauEnvelopeRepresentation f β) :
    f.toEReal.asEReal =
      {}^[(β⁻¹ : PosReal)]
        (gammaZeroConjugate (conjugateSubInvHalfSquaredNorm f β) hrep.mem_gammaZero) :=
  sorry

end MoreauCharacterizationOfSmoothConvexFunctions

end ERealFunction
