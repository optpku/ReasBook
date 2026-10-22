/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Filter
open scoped Topology

/- Text 1.0.58: for a subset `C` of a Hausdorff topological space, being sequentially closed is
formalized by the canonical predicate `IsSeqClosed C`, meaning that every convergent sequence in
`C` has its limit in `C`. The separation assumption is not needed for this definition. -/
recall IsSeqClosed

/-- Text 1.0.58: the canonical predicate `IsSeqClosed C` means that every convergent sequence in
`C` has its limit in `C`. This is just the defining equation of `IsSeqClosed`. -/
theorem isSeqClosed_iff_forall_tendsto_mem {X : Type u} [TopologicalSpace X] {C : Set X} :
    IsSeqClosed C ↔
      ∀ ⦃x : ℕ → X⦄ ⦃p : X⦄, (∀ n, x n ∈ C) → Tendsto x atTop (𝓝 p) → p ∈ C :=
  Iff.rfl
