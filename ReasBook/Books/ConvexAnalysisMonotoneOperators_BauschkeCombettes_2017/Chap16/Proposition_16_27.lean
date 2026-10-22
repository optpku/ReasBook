/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Corollary_8_39
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_17
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section SubdifferentialContinuity

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: apply Corollary 8.39 to a member of `Γ₀(H)` to identify interior-domain points
-- with the canonical continuity set of the finite-valued restriction to `effectiveDomain f`.
/-- Proposition 16.27: for `f ∈ Γ₀(H)`, the interior of the effective domain is exactly the set of
points where the finite-valued restriction of `f` to its effective domain is continuous. -/
theorem interior_effectiveDomain_eq_setOf_continuousAtOnEffectiveDomain_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    interior (effectiveDomain f) = {x : H | ContinuousAtOnEffectiveDomain f x} := sorry

-- Proof sketch: if `x` is continuous on the effective domain, Proposition 16.17 (2) gives a
-- nonempty subdifferential at `x`, so `x` belongs to the domain of `∂ f`.
/-- A `Γ₀(H)` continuity point on the effective domain is a subdifferentiability point. -/
theorem continuitySet_subset_subdifferentialDomain_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    {x : H | ContinuousAtOnEffectiveDomain f x} ⊆ SetValuedOperator.dom (∂ f) := sorry

-- Proof sketch: Proposition 16.4 already supplies the canonical inclusion from the
-- subdifferential domain to the effective domain for functions with nonempty effective domain; a
-- `Γ₀(H)` function has that nonempty effective domain by convexity.
omit [CompleteSpace H] in
/-- Proposition 16.27, final inclusion: if `f ∈ Γ₀(H)`, then every point where `∂ f` is nonempty
lies in the effective domain of `f`. -/
theorem subdifferentialDomain_subset_effectiveDomain_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    SetValuedOperator.dom (∂ f) ⊆ effectiveDomain f := by
  simpa using subdifferential_domain_subset_effectiveDomain f hf.2.nonempty

end SubdifferentialContinuity

end ERealFunction
