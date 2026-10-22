/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_1_2
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_1_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

set_option autoImplicit false

open Quiver.Path
open OneComplex
open scoped TwoComplex

section

variable {F : Type u} [Group F]

/-!
Primary domain: group-labelled paths and region labels in oriented `2`-complexes.

Layer triage:
- `source-facing`: multiply the edge labels along a path, then use loops representing the boundary
  cycle of a face to define the labels of that face.
- `core/canonical`: `GroupDiagram` is the owner of the edge-labelling, `Quiver.Path` is the owner
  of endpoint-aware paths, and `Loop` together with `cyclicPath` is the owner API for a
  basepoint-free boundary cycle.
- `bridge/view`: `TwoComplex.BoundaryPath` is the based closed-path representative API for a
  chosen basepoint on the face boundary, while `OneComplex.Path.edges` remains the chapter bridge
  to the textbook oriented-edge word of a path.

Domain sampling:
1. `GroupDiagram.label` is the canonical edge-labelling function attached to the diagram.
2. `Quiver.Path` is the owner path type, so path evaluation should be defined recursively on
   paths rather than through a derived edge-list wrapper.
3. `Loop` and `cyclicPath` are the owner boundary-cycle API without a preferred basepoint.
4. `TwoComplex.BoundaryPath` is the project owner for a based representative of a face boundary.
-/

namespace GroupDiagram

/-- The group element obtained by multiplying the labels of the oriented edges traversed by a path
in their path order. -/
def pathLabel (M : GroupDiagram F) {a b : M.source.skeleton} (p : Quiver.Path a b) : F :=
  match p with
  | .nil => 1
  | .cons p e => M.pathLabel p * M.label e.1

/-- The empty path has trivial label product. -/
-- Proof sketch: unfold `pathLabel`; the edge list of the empty path is empty, so the list product
-- is the empty product `1`.
@[simp]
theorem pathLabel_nil (M : GroupDiagram F) (a : M.source.skeleton) :
    M.pathLabel (nil : Quiver.Path a a) = 1 :=
  rfl

/-- Appending one oriented edge multiplies the path label by the label of that edge. -/
@[simp] theorem pathLabel_cons (M : GroupDiagram F) {a b c : M.source.skeleton}
    (p : Quiver.Path a b) (e : b ⟶ c) :
    M.pathLabel (.cons p e) = M.pathLabel p * M.label e.1 :=
  rfl

/-- Definition 5-1-4: the labels of a region `D` are the group elements obtained by applying
`pathLabel` to loops representing the boundary cycle `∂D`. -/
def regionLabels (M : GroupDiagram F) (D : M.source.Face) : Set F :=
  { g | ∃ p : Loop M.source.skeleton, cyclicPath p = (∂ D) ∧ M.pathLabel p.2 = g }

/-- A group element belongs to `regionLabels D` exactly when it is the label of some loop
representing the boundary cycle of `D`. -/
theorem mem_regionLabels_iff_exists_loop (M : GroupDiagram F) (D : M.source.Face) (g : F) :
    g ∈ M.regionLabels D ↔
      ∃ p : Loop M.source.skeleton, cyclicPath p = (∂ D) ∧ M.pathLabel p.2 = g :=
  Iff.rfl

/-- A group element belongs to `regionLabels D` exactly when it is the label of some based
boundary path of `D`. -/
theorem mem_regionLabels_iff (M : GroupDiagram F) (D : M.source.Face) (g : F) :
    g ∈ M.regionLabels D ↔
      ∃ v : M.source.skeleton, ∃ q : M.source.BoundaryPath D v, M.pathLabel q.1 = g := by
  constructor
  · rintro ⟨⟨v, p⟩, hp, rfl⟩
    exact ⟨v, ⟨p, hp⟩, rfl⟩
  · rintro ⟨v, q, rfl⟩
    exact ⟨⟨v, q.1⟩, q.2, rfl⟩

/-- The label of any loop representing the boundary cycle of `D` is one of the labels of `D`. -/
theorem boundaryCycleLabel_mem_regionLabels (M : GroupDiagram F) (D : M.source.Face)
    (p : Loop M.source.skeleton) (hp : cyclicPath p = (∂ D)) :
    M.pathLabel p.2 ∈ M.regionLabels D :=
  ⟨p, hp, rfl⟩

end GroupDiagram

end
