/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Corollary_16_19
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_27

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

namespace ERealFunction

section Conjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: use the interior-point hypothesis to obtain supporting affine minorants on
-- `interior (effectiveDomain f)`, identify the indicator-augmented function with `f` there, and
-- then apply the Fenchel--Moreau reconstruction theorem to recover `f` as the biconjugate of that
-- restriction.
/-- Proposition 16.25: if `f ∈ Γ₀(H)` and the interior of its effective domain is nonempty, then
`f` equals the biconjugate of its restriction to `interior (effectiveDomain f)`, encoded by the
canonical constrained function `f + ι[interior (effectiveDomain f)]`. -/
theorem eq_biconjugate_add_indicator_interior_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (hinter : (interior (effectiveDomain f)).Nonempty) :
    f.asEReal = ((f + ι[interior (effectiveDomain f)]).asEReal)∗∗ := by
  have hconv : ConvexOn f (effectiveDomain f) := hf.2
  have hcont :
      interior (effectiveDomain f) ⊆ {x : H | ContinuousAtOnEffectiveDomain f x} := by
    simpa using
      (interior_effectiveDomain_eq_setOf_continuousAtOnEffectiveDomain_of_mem_gammaZero hf).subset
  have hdom : effectiveDomain f ⊆ closure (interior (effectiveDomain f)) := by
    simpa [hconv.convex_effectiveDomain.closure_interior_eq_closure_of_nonempty_interior hinter]
      using (subset_closure : effectiveDomain f ⊆ closure (effectiveDomain f))
  simpa using
    eq_biconjugate_add_indicator_of_mem_gammaZero_subset_closure_eqOn
      f (interior (effectiveDomain f)) hf hdom (fun _ _ ↦ rfl)

end Conjugation

end ERealFunction
