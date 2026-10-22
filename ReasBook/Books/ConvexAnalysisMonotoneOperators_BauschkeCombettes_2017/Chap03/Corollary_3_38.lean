/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_46
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_34
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_37

-- Declarations for this item will be appended below by the statement pipeline.

open Filter

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Every weak sequential cluster point of a sequence in a closed convex subset of a real Hilbert
space belongs to that set. -/
-- Proof sketch: weak closedness of a closed convex set identifies the weak limit of any weakly
-- convergent subsequence with a point in the weak image of the set; injectivity of `toWeakSpace`
-- then returns the corresponding point of `C`.
private theorem mem_of_weakSequentialClusterPt_of_isClosed_convex {C : Set H}
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) {u : ℕ → H} (hu : ∀ n, u n ∈ C)
    {x : H}
    (hx : IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (u n)) (toWeakSpace ℝ H x)) :
    x ∈ C := by
  have hweakClosed : IsClosed ((toWeakSpace ℝ H) '' C) :=
    (isClosed_iff_weak_image_isClosed_of_convex hC_convex).1 hC_closed
  rcases hx.exists_subseq_tendsto with ⟨φ, hφ, hφx⟩
  have hsubseq_mem :
      ∀ n, toWeakSpace ℝ H (u (φ n)) ∈ (toWeakSpace ℝ H) '' C := by
    intro n
    exact ⟨u (φ n), hu (φ n), rfl⟩
  have hx_mem : toWeakSpace ℝ H x ∈ closure ((toWeakSpace ℝ H) '' C) :=
    mem_closure_of_tendsto hφx (Filter.Eventually.of_forall hsubseq_mem)
  rw [hweakClosed.closure_eq] at hx_mem
  rcases hx_mem with ⟨y, hyC, hyx⟩
  exact (toWeakSpace ℝ H).injective hyx ▸ hyC

/-- Corollary 3.38: every sequence with values in a bounded closed convex subset of a real Hilbert
space admits a weakly convergent subsequence whose weak limit belongs to the set. -/
-- Proof sketch: weak sequential compactness of the weak image of `C` produces a weakly
-- convergent subsequence in `WeakSpace`; pulling the limit back along `toWeakSpace` gives the
-- desired `x ∈ C`.
theorem exists_subsequence_tendsto_weakly_mem_of_bounded_isClosed_convex {C : Set H}
    (hC_bounded : Bornology.IsBounded C) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (u : ℕ → H) (hu : ∀ n, u n ∈ C) :
    ∃ x ∈ C, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n ↦ toWeakSpace ℝ H (u (φ n))) atTop (nhds (toWeakSpace ℝ H x)) := by
  have hseqCompact : IsSeqCompact ((toWeakSpace ℝ H) '' C) :=
    weaklySeqCompact_of_bounded_closed_convex hC_bounded hC_closed hC_convex
  have hu_mem : ∀ n, toWeakSpace ℝ H (u n) ∈ (toWeakSpace ℝ H) '' C := by
    intro n
    exact ⟨u n, hu n, rfl⟩
  obtain ⟨w, hw, φ, hφ, hφw⟩ := hseqCompact hu_mem
  rcases hw with ⟨x, hxC, hwx⟩
  refine ⟨x, hxC, φ, hφ, ?_⟩
  simpa [hwx] using hφw
