/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- Definition 3.1.6: for a cover `p : E → B`, the space `E` is the total space, `B` is the base
space, the set-theoretic fiber over `b` is `p ⁻¹' {b}`, and a set `V ⊆ B` is a fundamental
neighborhood of `b` when it is a path-connected evenly covered neighborhood for `p`. -/
def IsFundamentalNeighborhood (p : E → B) (b : B) (V : Set B) : Prop :=
  DiscreteTopology (p ⁻¹' {b}) ∧
    b ∈ V ∧ IsOpen V ∧ IsPathConnected V ∧ IsOpen (p ⁻¹' V) ∧
    ∃ H : p ⁻¹' V ≃ₜ V × (p ⁻¹' {b}), ∀ e, (H e).1.1 = p e

namespace IsFundamentalNeighborhood

variable {p : E → B} {b : B} {V : Set B}

/-- A fundamental neighborhood supplies the chosen witness for
`IsPathConnectedEvenlyCovered p b`. -/
theorem isPathConnectedEvenlyCovered (hV : IsFundamentalNeighborhood p b V) :
    IsPathConnectedEvenlyCovered p b := by
  rcases hV with ⟨hdiscrete, hbV, hVOpen, hVPathConnected, hpVOpen, H, hH⟩
  exact ⟨hdiscrete, V, hbV, hVOpen, hVPathConnected, hpVOpen, H, hH⟩

/-- A fundamental neighborhood is, in particular, an evenly covered neighborhood with fiber
`p ⁻¹' {b}`. -/
theorem isEvenlyCovered (hV : IsFundamentalNeighborhood p b V) :
    IsEvenlyCovered p b (p ⁻¹' {b}) :=
  hV.isPathConnectedEvenlyCovered.isEvenlyCovered

/-- A point has a path-connected evenly covered neighborhood exactly when it admits some
fundamental neighborhood. -/
theorem exists_iff : IsPathConnectedEvenlyCovered p b ↔ ∃ V, IsFundamentalNeighborhood p b V := by
  constructor
  · rintro ⟨hdiscrete, V, hbV, hVOpen, hVPathConnected, hpVOpen, H, hH⟩
    exact ⟨V, hdiscrete, hbV, hVOpen, hVPathConnected, hpVOpen, H, hH⟩
  · rintro ⟨V, hV⟩
    exact hV.isPathConnectedEvenlyCovered

end IsFundamentalNeighborhood
