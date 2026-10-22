/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Corollary_16_40

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section SubdifferentialCalculus

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: Corollary 16.40 identifies `f.asEReal∗` with the conjugate of the
-- canonical constrained function `f + ι[SetValuedOperator.dom (∂ f)]`. Since `hf : f ∈ Γ₀(H)`,
-- Corollary 13.38 gives `f = f**`; applying the same biconjugation principle to the common
-- conjugate yields the desired equality.
/-- Corollary 16.41: if `f ∈ Γ₀(H)`, then `f` is the Fenchel biconjugate of the function obtained
by adding the indicator of the subdifferential domain `dom (∂ f)`. -/
theorem eq_biconjugate_add_indicator_subdifferentiabilityDomain_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    f.asEReal = ((f + ι[SetValuedOperator.dom (∂ f)]).asEReal)∗∗ := by
  exact (biconjugate_eq_of_mem_gammaZero hf).symm.trans <|
    congrArg ERealFunction.conjugate
      (conjugate_eq_conjugate_add_indicator_subdifferentiabilityDomain_of_mem_gammaZero hf)

end SubdifferentialCalculus

end ERealFunction
