/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Lemma_2_36
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Fact_2_37
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_34

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: a Hilbert space is reflexive, so closed bounded sets are weakly compact after
-- passing to the weak topology. A norm-closed convex subset is weakly closed, hence a weakly
-- closed subset of a weakly compact closed ball and therefore weakly compact.
/-- Canonical weak compactness form of Theorem 3.37. The weak topology is expressed by viewing the
set inside `WeakSpace ℝ H`. -/
theorem weaklyCompact_of_bounded_closed_convex
    {C : Set H} (hCbdd : Bornology.IsBounded C) (hCclosed : IsClosed C)
    (hCconv : Convex ℝ C) :
    IsCompact (toWeakSpace ℝ H '' C) := by
  -- Reuse the earlier canonical closed-convex weak-closedness criterion.
  have hweakClosed : IsClosed ((toWeakSpace ℝ H) '' C) :=
    (isClosed_iff_weak_image_isClosed_of_convex hCconv).1 hCclosed
  -- The Hilbert-space weak compactness criterion finishes once weak closedness and boundedness
  -- are available.
  exact
    (weaklyCompact_iff_weaklyClosed_and_bounded :
      IsCompact ((toWeakSpace ℝ H) '' C) ↔
        IsClosed ((toWeakSpace ℝ H) '' C) ∧ Bornology.IsBounded C).2
      ⟨hweakClosed, hCbdd⟩

/-- Theorem 3.37: a nonempty bounded closed convex subset of a real Hilbert space is weakly
compact. The weak topology is expressed by viewing the set inside `WeakSpace ℝ H`. -/
theorem weaklyCompact_of_nonempty_bounded_closed_convex
    {C : Set H} (_hCne : C.Nonempty) (hCbdd : Bornology.IsBounded C) (hCclosed : IsClosed C)
    (hCconv : Convex ℝ C) :
    IsCompact (toWeakSpace ℝ H '' C) :=
  weaklyCompact_of_bounded_closed_convex hCbdd hCclosed hCconv

-- Proof sketch: apply weak compactness from the previous theorem, then use the Hilbert-space
-- form of the Eberlein-Smulian theorem to identify weak compactness with weak sequential
-- compactness on subsets of `H`.
/-- Weak sequential compactness companion in canonical bounded/closed/convex form. -/
theorem weaklySeqCompact_of_bounded_closed_convex
    {C : Set H} (hCbdd : Bornology.IsBounded C) (hCclosed : IsClosed C)
    (hCconv : Convex ℝ C) :
    IsSeqCompact (toWeakSpace ℝ H '' C) := by
  -- First obtain weak compactness from the closed-convex bounded criterion.
  have hcompact : IsCompact (toWeakSpace ℝ H '' C) :=
    weaklyCompact_of_bounded_closed_convex hCbdd hCclosed hCconv
  -- Then apply the Hilbert-space Eberlein-Smulian equivalence on the same weak image.
  exact (weaklyCompact_iff_weaklySeqCompact C).1 hcompact

/-- Weak sequential compactness companion for a nonempty bounded closed convex subset of a real
Hilbert space. -/
theorem weaklySeqCompact_of_nonempty_bounded_closed_convex
    {C : Set H} (_hCne : C.Nonempty) (hCbdd : Bornology.IsBounded C) (hCclosed : IsClosed C)
    (hCconv : Convex ℝ C) :
    IsSeqCompact (toWeakSpace ℝ H '' C) :=
  weaklySeqCompact_of_bounded_closed_convex hCbdd hCclosed hCconv
