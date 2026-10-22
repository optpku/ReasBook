/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {A : Type u} [Nonempty A] [Preorder A] [IsDirectedOrder A]
variable {X : Type v} [TopologicalSpace X]

/-- Text 1.0.45: for a net `ξ : A → X`, the canonical predicate `MapClusterPt x Filter.atTop ξ`
means that every neighborhood of `x` is visited arbitrarily far out in the directed index set. -/
-- Proof sketch: unfold `MapClusterPt`, rewrite cluster points using
-- `mapClusterPt_iff_frequently`, and then rewrite frequent membership in `Filter.atTop`
-- as the textbook tail condition.
theorem mapClusterPt_atTop_iff_forall_forall_exists_ge_mem_nhds (ξ : A → X) (x : X) :
    MapClusterPt x Filter.atTop ξ ↔
      ∀ V : Set X, V ∈ nhds x → ∀ b : A, ∃ a : A, b ≤ a ∧ ξ a ∈ V := by
  rw [mapClusterPt_iff_frequently]
  constructor
  · intro h V hV b
    exact (Filter.frequently_atTop.mp (h V hV)) b
  · intro h V hV
    exact Filter.frequently_atTop.mpr (h V hV)
