/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_2_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

set_option autoImplicit false

section

variable {F : Type u} [Group F]

/-!
Primary domain: combinatorial group theory of group-labelled oriented maps.

Layer triage:
- `source-facing`: a diagram over a group is an oriented map together with a label on each
  oriented edge, compatible with reversal of orientation.
- `core/canonical`: `TwoComplex` is the project owner for oriented maps, while the edge-reversal
  operation on its `1`-skeleton is the canonical owner for the opposite orientation of an edge.
- `bridge/view`: a diagram is used via its underlying oriented map through a coercion to
  `TwoComplex`.

Domain sampling:
1. `TwoComplex` from Definition `3-2-4` is the existing owner abstraction for oriented maps.
2. The inverse-edge owner API on the `1`-skeleton is the notation `e⁻¹`, coming from
   `OneComplex.edgeInv`.
3. A group-valued edge-labelling is naturally a function on `source.skeleton.Edge`, and the
   textbook compatibility condition is a single structure field rather than a separate wrapper.

Primitive vs. derived:
- primitive data: the oriented map, the edge-label function, and the inverse-edge compatibility
  law;
- derived API: viewing a diagram as its underlying oriented map.
-/

/-- Definition 5-1-3: a diagram over a group `F` is an oriented map together with a label on each
oriented edge such that the label of the oppositely oriented edge is the inverse of the original
label. -/
structure GroupDiagram (F : Type u) [Group F] where
  /-- The underlying oriented map. -/
  source : TwoComplex.{v}
  /-- The label assigned to each oriented edge of the underlying map. -/
  label : source.skeleton.Edge → F
  /-- Reversing the orientation of an edge inverts its label. -/
  label_inv (e : source.skeleton.Edge) : label e⁻¹ = (label e)⁻¹

namespace GroupDiagram

attribute [simp] GroupDiagram.label_inv

/-- A group diagram is used via its underlying oriented map. -/
instance : CoeOut (GroupDiagram F) TwoComplex where
  coe := source

end GroupDiagram

end
