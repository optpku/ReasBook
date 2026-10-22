/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Proposition_15_24
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Theorem_15_23

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Pointwise

noncomputable section

universe u v

namespace ERealFunction

section FenchelRockafellarDuality

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-
Source/core/bridge triage:
- `source-facing`: Proposition 15.22 is the Attouch--Brézis `core` regularity version of
  composite Fenchel--Rockafellar dual attainment.
- `core/canonical`: Theorem 15.23 is the chapter owner theorem under
  `0 ∈ sri (effectiveDomain g - L '' effectiveDomain f)`.
- `bridge/view`: Proposition 15.24 packages the `core` hypothesis as one branch of the chapter
  regularity owner and converts it to the owner hypothesis
  `0 ∈ sri (effectiveDomain g - L '' effectiveDomain f)`.
-/

-- Proof sketch: feed the source-facing `core` hypothesis into the Chapter 15 regularity owner from
-- Proposition 15.24 to obtain `0 ∈ sri (effectiveDomain g - L '' effectiveDomain f)`, then apply
-- the composite attainment theorem.
set_option linter.style.longLine false in
/-- Proposition 15.22: if `f ∈ Γ₀(H)`, `g ∈ Γ₀(K)`, and
`0 ∈ core (effectiveDomain g - L '' effectiveDomain f)`, then the infimum of the composite primal
objective `x ↦ f x + g (L x)` equals the negative of the minimum of the dual objective
`v ↦ f^*(-L^* v) + g^*(v)`. -/
theorem exists_mem_argmin_compositeDualObjective_of_zero_mem_core_sub_image_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hcore : (0 : K) ∈ Set.core (effectiveDomain g - L '' effectiveDomain f)) :
    ∃ v ∈ Argmin (compositeDualObjective f g L),
      compositePrimalOptimalValue f g L = -(compositeDualObjective f g L v) := by
  have hregular : effectiveDomainSubImageStrongRelativeInteriorRegularity f g L := by
    rw [effectiveDomainSubImageStrongRelativeInteriorRegularity]
    exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl hcore
  have hsri : (0 : K) ∈ sri (effectiveDomain g - L '' effectiveDomain f) :=
    zero_mem_strongRelativeInterior_sub_image_effectiveDomain_of_regularity hf hg L hregular
  exact
    exists_mem_argmin_compositeDualObjective_eq_neg_compositePrimalOptimalValue_of_zero_mem_sri_sub_image_effectiveDomain
      f hf g hg L hsri

end FenchelRockafellarDuality

end ERealFunction
