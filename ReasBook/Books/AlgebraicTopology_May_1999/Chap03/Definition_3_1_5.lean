/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- A point of the base has a path-connected evenly covered neighborhood when the map is evenly
covered in the sense of `IsEvenlyCovered`, and the chosen evenly covered neighborhood can be taken
to be path-connected. -/
def IsPathConnectedEvenlyCovered (p : E → B) (b : B) : Prop :=
  DiscreteTopology (p ⁻¹' {b}) ∧
    ∃ V : Set B, b ∈ V ∧ IsOpen V ∧ IsPathConnected V ∧ IsOpen (p ⁻¹' V) ∧
      ∃ H : p ⁻¹' V ≃ₜ V × (p ⁻¹' {b}), ∀ e, (H e).1.1 = p e

namespace IsPathConnectedEvenlyCovered

variable {p : E → B} {b : B}

/-- Forgetting path connectedness turns a path-connected evenly covered neighborhood into an
ordinary evenly covered neighborhood. -/
theorem isEvenlyCovered (hb : IsPathConnectedEvenlyCovered p b) :
    IsEvenlyCovered p b (p ⁻¹' {b}) := by
  rcases hb with ⟨hdiscrete, V, hbV, hVOpen, _hVPathConnected, hpVOpen, H, hH⟩
  exact ⟨hdiscrete, V, hbV, hVOpen, hpVOpen, H, hH⟩

end IsPathConnectedEvenlyCovered

/-- Definition 3.1.5: a covering map is a surjective map such that every point of the base has a
path-connected evenly covered neighborhood. -/
def IsPathConnectedCoveringMap (p : E → B) : Prop :=
  Function.Surjective p ∧ ∀ b : B, IsPathConnectedEvenlyCovered p b

namespace IsPathConnectedCoveringMap

variable {p : E → B}

/-- A path-connected covering map is surjective. -/
theorem surjective (hp : IsPathConnectedCoveringMap p) : Function.Surjective p := hp.1

/-- A path-connected covering map is a covering map in the sense of `IsCoveringMap`. -/
theorem isCoveringMap (hp : IsPathConnectedCoveringMap p) : IsCoveringMap p := by
  intro b
  exact (hp.2 b).isEvenlyCovered

end IsPathConnectedCoveringMap

namespace IsCoveringMap

variable {p : E → B} [LocPathConnectedSpace B]

/-- In a locally path-connected base, a surjective covering map has path-connected evenly covered
neighborhoods, so it is a covering map in the sense of Definition 3.1.5. -/
theorem isPathConnectedCoveringMap (hp : IsCoveringMap p)
    (hsurj : Function.Surjective p) : IsPathConnectedCoveringMap p := by
  refine ⟨hsurj, fun b ↦ ?_⟩
  have hpb := hp b
  have hbFiber : Nonempty (p ⁻¹' ({b} : Set B)) := by
    rcases hsurj b with ⟨e, rfl⟩
    exact ⟨⟨e, rfl⟩⟩
  let t : Bundle.Trivialization (p ⁻¹' ({b} : Set B)) p := hpb.toTrivialization
  have hbBase : b ∈ t.baseSet := hpb.mem_toTrivialization_baseSet
  let V : Set B := pathComponentIn t.baseSet b
  have hVBase : V ⊆ t.baseSet := pathComponentIn_subset
  have hbV : b ∈ V := mem_pathComponentIn_self hbBase
  have hVOpen : IsOpen V := t.open_baseSet.pathComponentIn b
  have hVPath : IsPathConnected V := isPathConnected_pathComponentIn hbBase
  let tV : Bundle.Trivialization (p ⁻¹' ({b} : Set B)) p := t.restrOpen V hVOpen
  refine ⟨hpb.discreteTopology_fiber, V, hbV, hVOpen, hVPath, ?_, ?_, ?_⟩
  · simpa using hVOpen.preimage hp.continuous
  · exact tV.preimageHomeomorph fun y hy ↦ ⟨hVBase hy, hy⟩
  · intro e
    simp [Bundle.Trivialization.preimageHomeomorph_apply, tV, V]

end IsCoveringMap
