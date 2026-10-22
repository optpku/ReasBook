/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Proposition_3_45
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_45
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Proposition_7_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace Pointwise

namespace Set

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

-- Proof sketch: a boundary point of `C` belongs to `closure C` but not to `interior (closure C)`
-- because `interior (closure C) = interior C` for convex sets with nonempty interior.
-- Proposition 6.45 then gives a nontrivial normal cone at that point, and Proposition 7.3 turns
-- that canonical normal-cone criterion directly into `x ∈ spts (closure C)`.
/-- Proposition 7.5 (1): if `C` is convex with nonempty interior, then every boundary point of `C`
is a support point of `closure C`, formalized as membership in `spts (closure C)`. -/
theorem frontier_subset_supportPoints_closure_of_convex_nonempty_interior
    {C : Set 𝓗} (hC_convex : Convex ℝ C) (hC_int_nonempty : (interior C).Nonempty) :
    frontier C ⊆ spts (closure C) := by
  intro x hx
  rw [supportPoints_eq_setOf_nontrivial_normalCone]
  change N[closure C] x \ ({0} : Set 𝓗) ≠ ∅
  have hx_closure : x ∈ closure C := by
    simpa [frontier] using hx.1
  have hclosure_int_nonempty : (interior (closure C)).Nonempty := by
    rw [interior_closure_eq_interior_of_convex_nonempty_interior hC_convex hC_int_nonempty]
    exact hC_int_nonempty
  have hx_not_interior_closure : x ∉ interior (closure C) := by
    rw [interior_closure_eq_interior_of_convex_nonempty_interior hC_convex hC_int_nonempty]
    simpa [frontier] using hx.2
  have hN_ne : N[closure C] x ≠ ({0} : Set 𝓗) := by
    intro hN
    exact hx_not_interior_closure <|
      (mem_interior_iff_normalCone_eq_singleton_zero_of_convex hC_convex.closure
        hclosure_int_nonempty hx_closure).2 hN
  have hzero : (0 : 𝓗) ∈ N[closure C] x := by
    rw [normalCone_of_mem hx_closure]
    simp [innerSupremumOn_eq_sSup_image]
  intro hdiff
  apply hN_ne
  refine Subset.antisymm ?_ (singleton_subset_iff.mpr hzero)
  rw [diff_eq_empty] at hdiff
  exact hdiff

-- Proof sketch: apply the first clause to obtain a supporting direction for `closure C`, then
-- restrict from `closure C` to `C` by the same monotonicity step that underlies Proposition 7.2.
/-- Proposition 7.5 (2): if `C` is convex with nonempty interior, then every boundary point of `C`
that belongs to `C` is a support point of `C`, formalized as membership in `spts C`. -/
theorem inter_frontier_subset_supportPoints_of_convex_nonempty_interior
    {C : Set 𝓗} (hC_convex : Convex ℝ C) (hC_int_nonempty : (interior C).Nonempty) :
    C ∩ frontier C ⊆ spts C := by
  intro x hx
  rcases hx with ⟨hxC, hx_frontier⟩
  have hx_support_closure : x ∈ spts (closure C) :=
    frontier_subset_supportPoints_closure_of_convex_nonempty_interior hC_convex hC_int_nonempty
      hx_frontier
  -- Unpack the support-point witness on `closure C` and reuse the same vector on `C`.
  rw [mem_supportPoints_iff] at hx_support_closure ⊢
  rcases hx_support_closure with ⟨_, u, hu_ne, hu_support⟩
  -- Restrict the support inequality along `C ⊆ closure C`.
  have hmono : innerSupremumOn C u ≤ innerSupremumOn (closure C) u := by
    rw [innerSupremumOn_eq_sSup_image, innerSupremumOn_eq_sSup_image]
    exact sSup_le_sSup <| by
      rintro _ ⟨y, hy, rfl⟩
      exact ⟨y, subset_closure hy, rfl⟩
  exact ⟨hxC, u, hu_ne, le_trans hmono hu_support⟩

end

end Set
