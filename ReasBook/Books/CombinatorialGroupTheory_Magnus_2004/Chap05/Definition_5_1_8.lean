/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_1_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

open Quiver.Path

section

variable {F : Type u} [Group F]

namespace GroupDiagram

/-!
Primary domain: Chapter `5` group-labelled diagrams whose region labels are constrained by a
fixed subset of the ambient group.

Layer triage:
- `source-facing`: an `R`-diagram is a labelled diagram whose region boundary labels all lie in
  `R`.
- `core/canonical`: `GroupDiagram.regionLabels` from Definition `5-1-4` is the owner for the set
  of labels read around a face boundary.
- `bridge/view`: `Loop` and `cyclicPath` give the basepoint-free boundary-cycle presentation used
  to read one particular region label.

Domain sampling:
1. `GroupDiagram` from Definition `5-1-3` is the owner abstraction for labelled oriented maps.
2. `GroupDiagram.regionLabels` from Definition `5-1-4` is the owner for admissible face labels.
3. `GroupDiagram.boundaryCycleLabel_mem_regionLabels` is the canonical bridge from a displayed
   boundary loop to `regionLabels`.
-/

/-- Definition 5-1-8: for a symmetrized subset `R` of `F`, an `R`-diagram is a group diagram
whose label on every boundary cycle of every region belongs to `R`. -/
def IsRDiagram (M : GroupDiagram F) (R : Set F) : Prop :=
  ∀ D : M.source.Face, M.regionLabels D ⊆ R

namespace IsRDiagram

/-- Every region label set of an `R`-diagram is contained in `R`. -/
theorem regionLabels_subset {M : GroupDiagram F} {R : Set F} (hM : M.IsRDiagram R)
    (D : M.source.Face) :
    M.regionLabels D ⊆ R :=
  hM D

/-- In an `R`-diagram, the label read around any boundary cycle of any region belongs to `R`. -/
theorem boundaryCycleLabel_mem {M : GroupDiagram F} {R : Set F} (hM : M.IsRDiagram R)
    (D : M.source.Face) (p : Loop M.source.skeleton) (hp : cyclicPath p = M.source.boundary D) :
    M.pathLabel p.2 ∈ R :=
  hM.regionLabels_subset D (M.boundaryCycleLabel_mem_regionLabels D p hp)

end IsRDiagram

end GroupDiagram

end
