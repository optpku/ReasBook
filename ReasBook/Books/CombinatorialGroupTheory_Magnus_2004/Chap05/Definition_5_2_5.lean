/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_2_7
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_1_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

open Quiver.Path

section

variable {F : Type u} [Group F]

namespace GroupDiagram

/-!
Primary domain: reduced group-labelled diagrams in small-cancellation theory.

Layer triage:
- `source-facing`: a diagram is reduced when two region boundary cycles sharing an edge cannot
  cancel across that edge.
- `core/canonical`: `GroupDiagram.pathLabel` is the owner for the label of a boundary segment,
  `TwoComplex.BoundaryPath` is the owner API for a boundary cycle based at a chosen vertex, and
  `Quiver.Path.comp` together with `Hom.toPath` is the canonical way to express that based
  boundary path as a common edge followed by the complementary boundary path.
- `bridge/view`: the textbook boundary cycles `e δ₁` and `δ₂ e⁻¹` are represented by based loops
  `⟨a, e.toPath.comp δ₁⟩` and `⟨a, δ₂.comp (Quiver.reverse e).toPath⟩`.

Domain sampling:
1. `GroupDiagram.pathLabel` from Definition `5-1-4` is the canonical label evaluator on boundary
   paths.
2. `TwoComplex.BoundaryPath` from Definition `3-2-4` is the owner for a based representative of
   a face boundary.
3. `Quiver.Path.comp` and `Quiver.Hom.toPath` are the canonical constructors for the source
   boundary decompositions `e δ₁` and `δ₂ e⁻¹`.

Primitive vs. derived:
- primitive public data: the underlying labelled diagram and the two boundary decompositions
  through a common oriented edge, packaged through the owner boundary-path API;
- derived API: the source-facing noncancellation statement on the complementary boundary labels.
-/

/-- Definition 5-2-5: a diagram over `F` is reduced when, whenever two face boundary cycles can
be written as `e δ₁` and `δ₂ e⁻¹` for a common oriented edge `e`, the complementary labels
`φ(δ₁)` and `φ(δ₂)` are not inverse to one another. -/
def IsReduced (M : GroupDiagram F) : Prop :=
  ∀ {a b : M.source.skeleton} (D₁ D₂ : M.source.Face) (e : a ⟶ b)
    (q₁ : M.source.BoundaryPath D₁ a) (q₂ : M.source.BoundaryPath D₂ a)
    (δ₁ : Quiver.Path b a) (δ₂ : Quiver.Path a b),
    q₁.1 = e.toPath.comp δ₁ →
      q₂.1 = δ₂.comp (Quiver.reverse e).toPath →
      M.pathLabel δ₂ ≠ (M.pathLabel δ₁)⁻¹

namespace IsReduced

/-- In a reduced diagram, two boundary cycles that traverse a common edge in opposite directions
cannot have inverse complementary labels after that edge is removed. -/
theorem pathLabel_ne_inv_of_boundary_cycles {M : GroupDiagram F} (hM : M.IsReduced)
    {a b : M.source.skeleton} (D₁ D₂ : M.source.Face) (e : a ⟶ b)
    (δ₁ : Quiver.Path b a) (δ₂ : Quiver.Path a b)
    (h₁ : cyclicPath ⟨a, e.toPath.comp δ₁⟩ = M.source.boundary D₁)
    (h₂ : cyclicPath ⟨a, δ₂.comp (Quiver.reverse e).toPath⟩ = M.source.boundary D₂) :
    M.pathLabel δ₂ ≠ (M.pathLabel δ₁)⁻¹ := by
  let q₁ : M.source.BoundaryPath D₁ a := ⟨e.toPath.comp δ₁, h₁⟩
  let q₂ : M.source.BoundaryPath D₂ a := ⟨δ₂.comp (Quiver.reverse e).toPath, h₂⟩
  simpa [q₁, q₂] using hM D₁ D₂ e q₁ q₂ δ₁ δ₂ rfl rfl

end IsReduced

end GroupDiagram

end
