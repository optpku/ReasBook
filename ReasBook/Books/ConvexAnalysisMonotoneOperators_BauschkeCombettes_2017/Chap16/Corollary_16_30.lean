/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_11
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Corollary_13_38
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section SubdifferentialConjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Corollary 16.30 is the `Γ₀(H)` reading of the inverse-subdifferential identity.
- `core/canonical`: Proposition 16.10 is the owner theorem at the primitive nonempty-domain layer.
- `bridge/view`: `f∗[hf]` is the canonical `Γ₀(H)` package
  `properConjugateIoi f hf.2.nonempty`.

Corollary 16.30 is therefore the source-facing `Γ₀(H)` specialization of Proposition 16.10,
obtained by rewriting the packaged conjugate through `gammaZeroConjugate`. -/
/-- Corollary 16.30: if `f ∈ Γ₀(H)`, then the inverse of the subdifferential of `f` is the
subdifferential of its Fenchel conjugate `f*`, represented by `f∗[hf]`. -/
theorem inverse_subdifferential_eq_subdifferential_gammaZeroConjugate
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    ((∂ f).inverse : SetValuedOperator H H) = ∂ (f∗[hf]) := by
  simpa [gammaZeroConjugate] using
    inverse_subdifferential_eq_subdifferential_properConjugateIoi f hf.2.nonempty

end SubdifferentialConjugation

end ERealFunction
