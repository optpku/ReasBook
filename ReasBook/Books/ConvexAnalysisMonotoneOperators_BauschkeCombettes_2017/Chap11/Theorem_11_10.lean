/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Theorem_1_29
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_37
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap10.Proposition_10_25
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap11.Definition_11_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Topology

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Theorem 11.10: if a lower semicontinuous quasiconvex `]-∞,+∞]`-valued function on a real
Hilbert space has a nonempty bounded intersection of a closed convex constraint set with one of
its lower level sets, then its constrained argmin set is nonempty. -/
-- Proof sketch: set `D := C ∩ lowerLevelSet f ξ`. Proposition 10.25 upgrades `hf_lsc` and
-- `hf_quasi` to weak lower semicontinuity, i.e. lower semicontinuity of
-- `f ∘ (toWeakSpace ℝ H).symm`. The set `D` is bounded, closed, and convex, hence weakly compact
-- by Theorem 3.37. Apply Theorem 1.29 in the weak topology to the weak image of `D`, then use the
-- lower-level-set bound `f x ≤ ξ` on `D` to extend minimality from `D` to all of `C`.
theorem argminOn_nonempty_of_quasiconvexOn_univ_of_nonempty_bounded_inter_lowerLevelSet
    {f : H → EReal} {C : Set H} (hf_quasi : QuasiconvexOn ℝ Set.univ f)
    (hf_lsc : LowerSemicontinuous f) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (ξ : ℝ)
    (hlevel_nonempty : (C ∩ lowerLevelSet f ξ).Nonempty)
    (hlevel_bounded : Bornology.IsBounded (C ∩ lowerLevelSet f ξ)) :
    (Argmin[C] f).Nonempty := by
  let D := C ∩ lowerLevelSet f ξ
  let g : WeakSpace ℝ H → EReal := f ∘ (toWeakSpace ℝ H).symm
  have hlevel_convex : Convex ℝ (lowerLevelSet f ξ) :=
    ((quasiconvexOn_univ_iff_convex_lowerLevelSet ℝ f).1 hf_quasi) ξ
  have hD_closed : IsClosed D := by
    refine hC_closed.inter ?_
    exact (lowerSemicontinuous_iff_isClosed_lowerLevelSet f).1 hf_lsc ξ
  have hD_convex : Convex ℝ D :=
    hC_convex.inter hlevel_convex
  have hD_compact : IsCompact (toWeakSpace ℝ H '' D) :=
    weaklyCompact_of_bounded_closed_convex hlevel_bounded hD_closed hD_convex
  have hg_lsc : LowerSemicontinuous g := by
    exact weaklyLowerSemicontinuous_of_quasiconvexOn_univ hf_quasi hf_lsc
  have hD_dom : (toWeakSpace ℝ H '' D ∩ {x | g x < ⊤}).Nonempty := by
    rcases hlevel_nonempty with ⟨x, hxD⟩
    have hxD' : x ∈ C ∩ lowerLevelSet f ξ := by
      simpa [D] using hxD
    refine ⟨toWeakSpace ℝ H x, ⟨⟨x, hxD, rfl⟩, ?_⟩⟩
    exact lt_of_le_of_lt ((mem_lowerLevelSet_iff f ξ x).1 hxD'.2) (by simp)
  obtain ⟨w, hwD, hwmin⟩ :=
    lowerSemicontinuous_exists_isMinOn_of_isCompact hg_lsc hD_compact hD_dom
  rcases hwD with ⟨x, hxD, rfl⟩
  have hxD' : x ∈ C ∩ lowerLevelSet f ξ := by
    simpa [D] using hxD
  have hxD_min : ∀ y ∈ D, f x ≤ f y := by
    rw [isMinOn_iff] at hwmin
    intro y hyD
    simpa [g] using hwmin (toWeakSpace ℝ H y) ⟨y, hyD, rfl⟩
  have hx_le : f x ≤ (ξ : EReal) := by
    exact (mem_lowerLevelSet_iff f ξ x).1 hxD'.2
  refine ⟨x, ?_⟩
  rw [mem_argminOn_iff, isMinOn_iff]
  refine ⟨hxD'.1, ?_⟩
  intro y hyC
  by_cases hy_level : y ∈ lowerLevelSet f ξ
  · exact hxD_min y ⟨hyC, hy_level⟩
  · have hy_gt : (ξ : EReal) < f y := by
      simpa [mem_lowerLevelSet_iff, not_le] using hy_level
    exact le_trans hx_le hy_gt.le

end ERealFunction
