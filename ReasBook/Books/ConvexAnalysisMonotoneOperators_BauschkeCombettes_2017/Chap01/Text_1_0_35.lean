/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Text 1.0.35: for a topological space `X` and a point `x : X`, the family `𝓥(x)` of
neighborhoods of `x` is formalized by the neighborhood filter `nhds x`. -/
recall nhds {X : Type u} [TopologicalSpace X] (x : X) : Filter X

/-- A set belongs to the neighborhood filter of `x` exactly when it contains an open set
containing `x`. -/
-- Proof sketch: this is a direct restatement of `mem_nhds_iff`, rearranging the existential
-- witnesses into the textbook order `IsOpen U ∧ x ∈ U ∧ U ⊆ V`.
theorem mem_nhds_iff_exists_open_subset {X : Type u} [TopologicalSpace X] {x : X} {V : Set X} :
    V ∈ nhds x ↔ ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ V := by
  simpa [and_assoc, and_left_comm, and_comm] using
    (mem_nhds_iff : V ∈ nhds x ↔ ∃ U ⊆ V, IsOpen U ∧ x ∈ U)
