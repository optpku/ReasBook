/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Filter

variable {X : Type u} [TopologicalSpace X] [SequentialSpace X]

/-- Text 1.0.61: for an extended-real-valued function on a sequential topological space, lower
semicontinuity is equivalent to sequential lower semicontinuity, meaning that every convergent
sequence satisfies the liminf inequality at its limit.
-/
-- Proof sketch: use `lowerSemicontinuous_iff_isClosed_preimage` to identify lower
-- semicontinuity with closedness of all real sublevel sets, then use `isSeqClosed_iff_isClosed`
-- in a sequential space to pass between closedness and sequential closedness. The sequential
-- closedness of all sublevel sets is equivalent to the stated sequence-`liminf` inequality.
theorem lowerSemicontinuous_iff_forall_seq_tendsto_le_liminf (f : X → EReal) :
    LowerSemicontinuous f ↔
      ∀ ⦃x : X⦄ ⦃u : ℕ → X⦄,
        Tendsto u atTop (nhds x) → f x ≤ liminf (f ∘ u) atTop := by
  constructor
  · intro hf x u hu
    -- Transport the neighborhood-filter `liminf` inequality along the convergent sequence.
    calc
      f x ≤ liminf f (nhds x) := hf.le_liminf x
      _ ≤ liminf f (map u atTop) := liminf_le_liminf_of_le hu
      _ = liminf (f ∘ u) atTop := rfl
  · intro hseq
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro a
    rw [← isSeqClosed_iff_isClosed]
    intro u x hu_mem hu
    -- The sequence hypothesis gives the lower bound at the limit point.
    have hx_le : f x ≤ liminf (f ∘ u) atTop := hseq hu
    -- Pointwise membership in the sublevel set forces the sequence `liminf` below `a`.
    have hliminf_le : liminf (f ∘ u) atTop ≤ a := by
      refine liminf_le_of_frequently_le ?_
      refine Frequently.of_forall fun n ↦ ?_
      simpa [Set.mem_preimage, Set.mem_Iic] using hu_mem n
    -- Combining the two inequalities puts the limit point back in the same sublevel set.
    show x ∈ f ⁻¹' Set.Iic a
    simpa [Set.mem_preimage, Set.mem_Iic] using hx_le.trans hliminf_le
