/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Corollary_16_30
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Theorem_16_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section SubdifferentialConjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 16.33 is the minimizer/subgradient-at-zero statement for `f*`.
- `core/canonical`: the owner declarations are `Argmin`, `∂`, `SetValuedOperator.zeros`, and
  `SetValuedOperator.inverse`.
- `bridge/view`: `f∗[hf]` is the canonical `Γ₀(H)` packaging of the Fenchel conjugate.

The proposition should therefore stay source-facing, while its implementation is the direct owner
combination of Theorem 16.3 with Corollary 16.30, evaluated at `0`. -/
/-- Proposition 16.33: for `f ∈ Γ₀(H)`, the set of minimizers of `f` coincides with the
subdifferential of its Fenchel conjugate at `0`, represented here by `f∗[hf]`. -/
theorem argmin_eq_subdifferential_gammaZeroConjugate_zero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    Argmin f.asEReal = (∂ (f∗[hf])) 0 := by
  ext x
  rw [argmin_eq_zeros_subdifferential, SetValuedOperator.mem_zeros_iff]
  rw [← inverse_subdifferential_eq_subdifferential_gammaZeroConjugate f hf]
  exact (SetValuedOperator.mem_inverse_iff (∂ f) 0 x).symm

end SubdifferentialConjugation

end ERealFunction
