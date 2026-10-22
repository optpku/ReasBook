/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_27
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap17.Proposition_17_48

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section DifferentiabilityAndContinuity

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))

/- Source/core/bridge triage:
- `source-facing`: Proposition 17.50 records interior-domain and continuity consequences for
  members of `Γ₀(H)`.
- `core/canonical`: the owner abstractions are `Γ₀(H)`, `interior (effectiveDomain f)`, and
  `ContinuousAtOnEffectiveDomain`.
- `bridge/view`: clause (1) is exactly Proposition 17.48 (2) specialized from `ConvexOn f
  (effectiveDomain f)` to the convexity field packaged by `hf : f ∈ Γ₀(H)`, so the file should
  reuse that owner directly instead of restating a parallel local theorem. -/

/- Proposition 17.50 (1): this is Proposition 17.48 (2) specialized to `hf.2 :
ConvexOn f (effectiveDomain f)`. -/
#check mem_interior_effectiveDomain_of_convexOn_of_gateauxDifferentiableAt

-- Proof sketch: Corollary 8.39 identifies the points where the finite real representative of a
-- convex lower semicontinuous function is continuous with `interior (effectiveDomain f)`. Since
-- membership in `Γ₀(H)` packages lower semicontinuity and convexity on the effective domain, this
-- yields continuity on the whole interior.
/-- Proposition 17.50 (2): every function in `Γ₀(H)` is continuous on the interior of its
effective domain. -/
theorem continuousOn_toReal_interior_effectiveDomain_of_mem_gammaZero
    (hf : f ∈ Γ₀(H))
    :
    ContinuousOn (fun y ↦ (f y : EReal).toReal) (interior (effectiveDomain f)) := by
  intro x hx
  have hxcont : x ∈ {z : H | ContinuousAtOnEffectiveDomain f z} := by
    rw [← interior_effectiveDomain_eq_setOf_continuousAtOnEffectiveDomain_of_mem_gammaZero hf]
    exact hx
  exact hxcont.continuousWithinAt.mono interior_subset

end DifferentiabilityAndContinuity

end ERealFunction
