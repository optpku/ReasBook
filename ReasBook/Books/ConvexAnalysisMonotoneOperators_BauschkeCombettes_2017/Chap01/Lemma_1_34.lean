/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section SeqClosed

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X}

/-- Lemma 1.34 (1): a sequentially compact subset of a Hausdorff space is sequentially closed. -/
-- Proof sketch: given a convergent sequence in `C`, use sequential compactness to extract a
-- convergent subsequence with limit in `C`; in a Hausdorff space the subsequence has the same limit
-- as the original sequence, so the ambient limit belongs to `C`.
theorem IsSeqCompact.isSeqClosed (hC : IsSeqCompact C) :
    IsSeqClosed C := by
  intro u x hu hx
  -- Extract a convergent subsequence whose limit stays inside `C`.
  obtain ⟨y, hyC, φ, hφ_mono, hφ_tendsto⟩ := hC hu
  -- Reindex the original convergence along the subsequence map.
  have hφ_tendsto_x := hx.comp hφ_mono.tendsto_atTop
  -- In a Hausdorff space the subsequence limit must agree with the ambient limit.
  have hy_eq_x : y = x := tendsto_nhds_unique hφ_tendsto hφ_tendsto_x
  simpa [hy_eq_x] using hyC

end SeqClosed

section SeqCompact

variable {X : Type u} [TopologicalSpace X]
variable {A C : Set X}

/-- Lemma 1.34 (2): a sequentially closed subset of a sequentially compact set is sequentially
compact. -/
-- Proof sketch: start with a sequence in `A`; since `A ⊆ C`, sequential compactness of `C`
-- provides a convergent subsequence with limit in `C`; sequential closedness of `A` forces that
-- limit to lie in `A`, yielding sequential compactness of `A`.
theorem IsSeqCompact.of_isSeqClosed_subset (hC : IsSeqCompact C) (hA_closed : IsSeqClosed A)
    (hA : A ⊆ C) :
    IsSeqCompact A := by
  intro u huA
  -- View the sequence as taking values in `C` and extract a convergent subsequence there.
  obtain ⟨x, hxC, φ, hφ_mono, hφ_tendsto⟩ := hC (fun n ↦ hA (huA n))
  -- The subsequence still lies in `A`, so sequential closedness forces its limit back into `A`.
  have hsubseq_mem_A : ∀ n, (u ∘ φ) n ∈ A := by
    intro n
    exact huA (φ n)
  have hxA : x ∈ A := hA_closed hsubseq_mem_A hφ_tendsto
  exact ⟨x, hxA, φ, hφ_mono, hφ_tendsto⟩

end SeqCompact
