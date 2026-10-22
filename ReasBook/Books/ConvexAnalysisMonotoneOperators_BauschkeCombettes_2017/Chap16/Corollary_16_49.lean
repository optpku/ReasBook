/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Fact_6_14
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_27

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace Pointwise

universe u

namespace ERealFunction

section SubdifferentialCalculus

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Corollary 16.49 (1) is Proposition 16.27. -/
#check interior_effectiveDomain_eq_setOf_continuousAtOnEffectiveDomain_of_mem_gammaZero

-- Proof sketch: rewrite the continuity set using Proposition 16.27, then use convexity of
-- `effectiveDomain f` from `hf` together with the Chapter 6 fact that the interior of a convex set
-- is contained in its strong relative interior.
/-- Corollary 16.49 (2): for `f ∈ Γ₀(H)`, every continuity point on the effective domain belongs to
the strong relative interior of the effective domain. -/
theorem continuitySet_subset_strongRelativeInterior_effectiveDomain_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    {x : H | ContinuousAtOnEffectiveDomain f x} ⊆ sri (effectiveDomain f) := by
  rw [← interior_effectiveDomain_eq_setOf_continuousAtOnEffectiveDomain_of_mem_gammaZero hf]
  by_cases hinter : (interior (effectiveDomain f)).Nonempty
  · rw [interior_eq_strongRelativeInterior_of_convex_nonempty_interior
      hf.2.convex_effectiveDomain hinter]
  · simp [Set.not_nonempty_iff_eq_empty.mp hinter]

-- Proof sketch: fix `y ∈ sri (effectiveDomain f)` and apply Corollary 16.48 to `f` and the
-- singleton indicator at `y`. The regularity hypothesis becomes `0 ∈ sri (effectiveDomain f -
-- {y})`, and the resulting sum rule shows that `∂ f y` must be nonempty.
/-- Corollary 16.49 (3): for `f ∈ Γ₀(H)`, the strong relative interior of the effective domain is
contained in the subdifferentiability domain. -/
theorem strongRelativeInterior_effectiveDomain_subset_subdifferentiabilityDomain_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    sri (effectiveDomain f) ⊆ {x : H | SubdifferentiableAt f x} := sorry

/- Corollary 16.49 (4) is Proposition 16.4 (1). -/
#check subdifferential_domain_subset_effectiveDomain

end SubdifferentialCalculus

end ERealFunction
