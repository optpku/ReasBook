/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Definition_7_14

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

namespace Set

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

-- Proof sketch: rewrite membership in each polar set using
-- `mem_polarSet_iff_forall_inner_le_one`; the condition for `u ∈ (C ∪ D)ᵒ⊙`
-- is exactly the conjunction of the conditions for `u ∈ Cᵒ⊙` and `u ∈ Dᵒ⊙`.
/-- Exercise 7.5: the polar set of the union of two subsets of a real Hilbert space is the
intersection of their polar sets. -/
theorem polarSet_union_eq_inter (C D : Set 𝓗) :
    (C ∪ D)ᵒ⊙ = Cᵒ⊙ ∩ Dᵒ⊙ := by
  ext u
  constructor
  · intro hu
    -- Rewrite the union-side hypothesis into its pointwise form.
    rw [mem_polarSet_iff_forall_inner_le_one] at hu
    -- A point belongs to the intersection exactly when it belongs to both polar sets.
    rw [Set.mem_inter_iff, mem_polarSet_iff_forall_inner_le_one,
      mem_polarSet_iff_forall_inner_le_one]
    -- A bound on the union restricts to bounds on each subset.
    constructor
    · intro x hx
      exact hu x (Or.inl hx)
    · intro x hx
      exact hu x (Or.inr hx)
  · rw [Set.mem_inter_iff, mem_polarSet_iff_forall_inner_le_one,
      mem_polarSet_iff_forall_inner_le_one]
    intro hu
    rcases hu with ⟨hC, hD⟩
    rw [mem_polarSet_iff_forall_inner_le_one]
    -- Conversely, membership in the union is handled by cases.
    intro x hx
    rcases hx with hxC | hxD
    · exact hC x hxC
    · exact hD x hxD

end

end Set
