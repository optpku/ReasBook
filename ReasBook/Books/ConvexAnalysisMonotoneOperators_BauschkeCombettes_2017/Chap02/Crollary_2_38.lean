/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Data.List.TFAE
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Fact_2_37
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Lemma_2_36

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

/-- Corollary 2.38: for a subset `C` of a real Hilbert space, weak compactness, weak sequential
compactness, and weak closedness together with norm-boundedness are equivalent. The weak-topology
conditions are expressed by viewing `C` inside `WeakSpace ℝ 𝓗`. -/
-- Proof sketch: combine the weak compactness versus weak sequential compactness equivalence from
-- the Eberlein-Smulian theorem with the weak compactness versus weak closed and bounded
-- characterization in Hilbert spaces, and then package the resulting cycle as a `TFAE`.
theorem weaklyCompact_weaklySeqCompact_weaklyClosed_bounded_tfae (C : Set 𝓗) :
    List.TFAE
      [IsCompact ((toWeakSpace ℝ 𝓗) '' C),
        IsSeqCompact ((toWeakSpace ℝ 𝓗) '' C),
        IsClosed ((toWeakSpace ℝ 𝓗) '' C) ∧ Bornology.IsBounded C] := by
  -- Package the two canonical equivalences against weak compactness into the three-way `TFAE`.
  tfae_have 1 ↔ 2 := by
    exact weaklyCompact_iff_weaklySeqCompact C
  tfae_have 1 ↔ 3 := by
    exact weaklyCompact_iff_weaklyClosed_and_bounded
  tfae_finish
