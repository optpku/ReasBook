/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Metric

universe u

variable {α : Type u} [MetricSpace α]

/-- Lemma 1.40: if every intersection `C ∩ B[z; n]` with a closed ball of integer radius
`n ≥ 1` centered at `z` is closed, then `C` itself is closed. -/
-- Proof sketch: Use the sequential characterization of closed sets in metric spaces. A sequence
-- in `C` converging in the ambient space is bounded, so it is contained in some
-- `closedBall z n` with `1 ≤ n`; the assumed closedness of `C ∩ closedBall z n`
-- then forces the limit to lie in `C`.
theorem isClosed_of_isClosed_inter_closedBall_nat (C : Set α) (z : α)
    (hC : ∀ n : ℕ, 1 ≤ n → IsClosed (C ∩ closedBall z n)) :
    IsClosed C := by
  rw [← isSeqClosed_iff_isClosed]
  intro u x hu hx
  -- A convergent sequence has bounded range, so one integer closed ball captures every term.
  obtain ⟨n, hn, hrange⟩ : ∃ n : ℕ, 1 ≤ n ∧ Set.range u ⊆ closedBall z n := by
    obtain ⟨r, hr, hsubset⟩ := (isBounded_range_of_tendsto u hx).subset_closedBall_lt 0 z
    refine ⟨Nat.ceil r, Nat.one_le_ceil_iff.mpr hr, ?_⟩
    exact hsubset.trans <| closedBall_subset_closedBall (Nat.le_ceil r)
  have hu_inter : ∀ k, u k ∈ C ∩ closedBall z n := by
    intro k
    exact ⟨hu k, hrange (Set.mem_range_self k)⟩
  -- Closedness of the trapped intersection forces the limit into the same intersection.
  have hx_inter : x ∈ C ∩ closedBall z n := by
    exact (hC n hn).mem_of_tendsto hx (Filter.Eventually.of_forall hu_inter)
  exact hx_inter.1
