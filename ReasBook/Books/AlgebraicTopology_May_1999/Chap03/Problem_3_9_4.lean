/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Example_3_1_7

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

namespace IsLocalHomeomorph

/-- Compactness of the source and singleton-closedness of the target force the fibers of a local
homeomorphism to be finite. -/
theorem finite_preimage_singleton [CompactSpace X] [T1Space Y] {f : X → Y}
    (hf : IsLocalHomeomorph f) (y : Y) : Set.Finite (f ⁻¹' ({y} : Set Y)) := by
  let s : Set X := f ⁻¹' ({y} : Set Y)
  have hsLocal : IsLocalHomeomorphOn f s := hf.isLocalHomeomorphOn
  letI : Subsingleton (f '' s) := by
    refine ⟨?_⟩
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    apply Subtype.ext
    rcases ha with ⟨x, hx, rfl⟩
    rcases hb with ⟨x', hx', rfl⟩
    simp only [s, Set.mem_preimage, Set.mem_singleton_iff] at hx hx'
    simp [hx, hx']
  letI : DiscreteTopology (f '' s) := inferInstance
  letI : DiscreteTopology s := hsLocal.discreteTopology_of_image
  have hsClosed : IsClosed s := by
    simpa [s] using (isClosed_singleton : IsClosed ({y} : Set Y)).preimage hf.continuous
  letI : CompactSpace s := isCompact_iff_compactSpace.mp hsClosed.isCompact
  have hsFinite : Finite s := finite_of_compact_of_discrete
  exact Set.toFinite s

/-- A compact-domain Hausdorff local homeomorphism to a Hausdorff target is a covering map. -/
-- Proof sketch: use `finite_preimage_singleton` to identify the finite discrete fiber over each
-- base point. Then choose local homeomorphism charts around the finitely many points of that
-- fiber, shrink their images to a common open neighborhood, and assemble the resulting disjoint
-- local sheets into the evenly covered neighborhood required by `IsCoveringMap`.
theorem isCoveringMap_of_compact [CompactSpace X] [T2Space X] [T2Space Y] {f : X → Y}
    (hf : IsLocalHomeomorph f) : IsCoveringMap f := by
  -- Work over `Set.univ`, where mathlib's covering-on criterion matches the global statement.
  refine isCoveringMap_iff_isCoveringMapOn_univ.mpr ?_
  -- Every point of the source lies in a local homeomorphism chart realizing `f`.
  refine IsCoveringMapOn.of_openPartialHomeomorph hf.continuous ?_
  intro e _
  obtain ⟨φ, heφ, hφ⟩ := hf e
  exact ⟨φ, heφ, hφ.symm⟩

/-- Problem 3.9.4: a compact-domain local homeomorphism from a nonempty Hausdorff space to a
preconnected locally path-connected Hausdorff target is a path-connected covering map. -/
-- Proof sketch: first apply `isCoveringMap_of_compact` to obtain the canonical covering-map
-- owner. The image of a compact-domain local homeomorphism is compact and therefore closed in a
-- Hausdorff codomain, while local homeomorphisms are open; connectedness of the target then
-- forces the image to be all of `Y`, giving surjectivity. Only preconnectedness is needed here:
-- nonemptiness comes from the nonempty compact domain. Finally invoke
-- `IsCoveringMap.isPathConnectedCoveringMap`.
theorem isPathConnectedCoveringMap_of_compact [CompactSpace X] [Nonempty X] [T2Space X]
    [PreconnectedSpace Y] [LocPathConnectedSpace Y] [T2Space Y] {f : X → Y}
    (hf : IsLocalHomeomorph f) : IsPathConnectedCoveringMap f := by
  have hRangeClosed : IsClosed (Set.range f) := (isCompact_range hf.continuous).isClosed
  have hRangeOpen : IsOpen (Set.range f) := hf.isOpenMap.isOpen_range
  have hRangeNonempty : (Set.range f).Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty X›
    exact ⟨f x, ⟨x, rfl⟩⟩
  have hsurj : Function.Surjective f := by
    rw [← Set.range_eq_univ]
    exact IsClopen.eq_univ ⟨hRangeClosed, hRangeOpen⟩ hRangeNonempty
  exact (hf.isCoveringMap_of_compact).isPathConnectedCoveringMap hsurj

end IsLocalHomeomorph
