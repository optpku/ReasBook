/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_9
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Definition_9_12
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap15.Definition_15_19

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
- `source-facing`: Theorem 15.23 is the chapter's composite Fenchel--Rockafellar attainment
  theorem under the textbook regularity hypothesis
  `0 ∈ sri (effectiveDomain g - L '' effectiveDomain f)`.
- `core/canonical`: the owner objects are the Chapter 15 declarations
  `compositePrimalObjective`, `compositePrimalOptimalValue`, and `compositeDualObjective` from
  Definition 15.19.
- `bridge/view`: Proposition 15.22 and Fact 15.25 are downstream bridge results converting other
  regularity packages (`core`, polyhedral hypotheses) to this owner `sri` hypothesis.
-/

-- Proof sketch: package the composite problem through the owner API from Definition 15.19 and
-- perform the standard product-space reduction behind Fenchel--Rockafellar duality. The
-- strong-relative-interior hypothesis `0 ∈ sri (effectiveDomain g - L '' effectiveDomain f)` is
-- the regularity condition that yields strong duality and attainment for the adjoint-based dual
-- objective `compositeDualObjective f g L`.
set_option linter.style.longLine false in
/-- Theorem 15.23: if `f ∈ Γ₀(H)`, `g ∈ Γ₀(K)`, and
`0 ∈ sri (effectiveDomain g - L '' effectiveDomain f)`, then the composite primal optimal value is
the negative of the minimum of the owner dual objective `compositeDualObjective f g L`, i.e.
of `v ↦ f^*(-L^* v) + g^*(v)`. -/
theorem exists_mem_argmin_compositeDualObjective_eq_neg_compositePrimalOptimalValue_of_zero_mem_sri_sub_image_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (effectiveDomain g - L '' effectiveDomain f)) :
    ∃ v ∈ Argmin (compositeDualObjective f g L),
      compositePrimalOptimalValue f g L = -(compositeDualObjective f g L v) := sorry

-- Proof sketch: the source-facing theorem above supplies a minimizing dual vector `v`. Since
-- `v ∈ Argmin (compositeDualObjective f g L)`, its dual value is exactly
-- `compositeDualOptimalValue f g L`, so the displayed equality rewrites to the owner optimal-value
-- identity.
/-- Companion reformulation of Theorem 15.23: the attained minimum of
`compositeDualObjective f g L` rewrites to the canonical dual optimal value
`compositeDualOptimalValue f g L`. -/
theorem compositePrimalOptimalValue_eq_neg_compositeDualOptimalValue_of_zero_mem_sri_sub_image_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (g : K → Set.Ioi (⊥ : EReal)) (hg : g ∈ Γ₀(K))
    (L : H →L[ℝ] K)
    (hsri : (0 : K) ∈ sri (effectiveDomain g - L '' effectiveDomain f)) :
    compositePrimalOptimalValue f g L = -compositeDualOptimalValue f g L := by
  obtain ⟨v, hvArg, hvEq⟩ :=
    exists_mem_argmin_compositeDualObjective_eq_neg_compositePrimalOptimalValue_of_zero_mem_sri_sub_image_effectiveDomain
      f hf g hg L hsri
  have hvValue : compositeDualObjective f g L v = compositeDualOptimalValue f g L := by
    rw [compositeDualOptimalValue_def]
    exact (mem_argmin_iff_eq_sInf).1 hvArg
  rw [hvValue] at hvEq
  exact hvEq

end FenchelRockafellarDuality

end ERealFunction
