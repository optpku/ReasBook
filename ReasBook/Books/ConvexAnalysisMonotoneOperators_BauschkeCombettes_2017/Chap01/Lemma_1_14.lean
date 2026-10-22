/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Filter

/-- Lemma 1.14: if a net in a compact subset of a Hausdorff space has `x` as its unique cluster
point, then the net converges to `x`. -/
-- Proof sketch: apply `IsCompact.tendsto_nhds_of_unique_mapClusterPt` to the compact set `C`.
-- The hypothesis `hξC` gives eventual membership in `C`, and uniqueness of cluster points in `X`
-- restricts to uniqueness among points of `C`.
theorem tendsto_of_unique_cluster_point_on_compact {X : Type u} [TopologicalSpace X] [T2Space X]
    {A : Type v} [Preorder A] [IsDirectedOrder A] {C : Set X} (hC : IsCompact C) {ξ : A → X}
    (hξC : ∀ a, ξ a ∈ C) {x : X} (_hx : MapClusterPt x atTop ξ)
    (hunique : ∀ y : X, MapClusterPt y atTop ξ → y = x) :
    Tendsto ξ atTop (nhds x) := by
  exact hC.tendsto_nhds_of_unique_mapClusterPt (Filter.Eventually.of_forall hξC) fun y _ hy ↦
    hunique y hy
