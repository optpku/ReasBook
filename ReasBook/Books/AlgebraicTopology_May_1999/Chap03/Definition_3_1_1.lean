/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib.Tactic.Recall
import Mathlib.Topology.Connected.LocPathConnected

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {X : Type u} [TopologicalSpace X]

/- Definition 3.1.1: a space is locally path connected when the canonical predicate
`LocPathConnectedSpace X` holds, equivalently when each point has arbitrarily small neighborhoods
whose points can be joined to the basepoint by paths staying inside a prescribed neighborhood. -/
recall LocPathConnectedSpace (X : Type u) [TopologicalSpace X] : Prop

/-- Local path connectedness means that every neighborhood of a point contains a smaller
neighborhood whose points can be joined to the basepoint by a path staying in the original
neighborhood; this witness neighborhood is therefore automatically contained in the original
neighborhood. -/
-- Proof sketch: use the path-connected neighborhood basis from `LocPathConnectedSpace` and the
-- fact that any two points in a path-connected subset are joined by a path inside that subset;
-- conversely, apply the neighborhood criterion to build a basis of path-connected neighborhoods.
theorem locPathConnectedSpace_iff_has_smaller_joinedIn_neighborhoods :
    LocPathConnectedSpace X ↔
      ∀ x : X, ∀ U : Set X, U ∈ nhds x →
        ∃ V : Set X, V ∈ nhds x ∧ ∀ ⦃y : X⦄, y ∈ V → JoinedIn U x y := by
  constructor
  · intro hX x U hU
    letI : LocPathConnectedSpace X := hX
    exact ⟨pathComponentIn U x, pathComponentIn_mem_nhds hU, fun _ hy ↦ hy⟩
  · intro h
    rw [locPathConnectedSpace_iff_pathComponentIn_mem_nhds]
    intro x u hu hxu
    rcases h x u (hu.mem_nhds hxu) with ⟨V, hV, hJoined⟩
    exact Filter.mem_of_superset hV fun _ hy ↦ hJoined hy
