/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Corollary_16_39

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section Subdifferentials

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: `effectiveDomain f` is nonempty because `hf : f ∈ Γ₀(H)` packages convexity on a
-- nonempty domain. Corollary 16.39 says subdifferentiability points are dense in that effective
-- domain, hence there exists `p ∈ effectiveDomain f` with `SubdifferentiableAt f p.1`, i.e.
-- `p ∈ dom (∂ f)`.
/-- Remark 16.2: if `f ∈ Γ₀(H)`, then the domain of the subdifferential of `f` is nonempty. -/
theorem subdifferential_dom_nonempty_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    (SetValuedOperator.dom (((∂ (f : H → EReal)) : H → Set H))).Nonempty := by
  letI : Nonempty (effectiveDomain f) := hf.2.nonempty.to_subtype
  rcases (dense_subdifferentiableAt_in_effectiveDomain_of_mem_gammaZero hf).nonempty with
    ⟨y, hy⟩
  exact ⟨y.1, by simpa using hy⟩

end Subdifferentials

end ERealFunction
