/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_1_5
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_2_4
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_2_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

set_option autoImplicit false

section

variable {X : Type u} {F : Type v} [Group F]

/-!
Primary domain: minimal van Kampen diagrams for relator-conjugate factorizations in a free group
with chosen basis.

Layer triage:
- `source-facing`: a minimal `R`-sequence `cs`, a Chapter `5` diagram `M : FreeGroupDiagram basis cs`,
  and the hypothesis that the diagram has exactly `cs.length` geometric regions.
- `core/canonical`: `FreeGroupDiagram basis cs` is the chapter owner for the diagram data,
  `GroupDiagram.IsReduced` is the owner predicate for reducedness, and
  `IsMinimalRelatorSequence R cs` is the owner predicate for minimal relator-conjugate
  factorizations.
- `bridge/view`: the coercion `FreeGroupDiagram basis cs → GroupDiagram F` transports the source
  diagram to the owner on which reducedness is defined, so no parallel local reducedness wrapper
  is needed.

Domain sampling:
1. `FreeGroupDiagram basis cs` from Definition `5-1-5` is the owner abstraction for the diagram.
2. `GroupDiagram.IsReduced` from Definition `5-2-5` is the owner predicate for reducedness.
3. `IsMinimalRelatorSequence R cs` from Definition `5-2-4` is the owner predicate for the
   minimality hypothesis.
4. `boundaryCycleWord_eq_list_prod_conjugates_of_regionLabels` from Lemma `5-1-7` is the chapter
   owner theorem turning a disc diagram boundary label into an ordered product of region-label
   conjugates, which is the bridge used in the proof sketch.

Primitive vs. derived:
- primitive public data: the basis `basis`, relator set `R`, minimal sequence `cs`, diagram `M`,
  and the cardinality condition `Nat.card (TwoComplex.GeometricFace M.source) = cs.length`;
- derived API: reducedness, expressed directly through the existing owner predicate `M.IsReduced`.
-/

-- Proof sketch: if the diagram were not reduced, two distinct adjacent regions could be merged
-- across a cancelling edge. The merged diagram would have the same outer boundary product as `M`
-- but one fewer region, so the Chapter `5` boundary-factorization lemma would produce a shorter
-- sequence of conjugates of elements of `R` with the same product as `cs`, contradicting the
-- minimality assumption.
/-- Lemma 5-2-6: if `M` is a diagram for a minimal `R`-sequence `cs`, with exactly one geometric
region for each term of `cs`, then the underlying group diagram of `M` is reduced. -/
theorem freeGroupDiagram_isReduced_of_isMinimalRelatorSequence
    (basis : FreeGroupBasis X F) {R : Set F} {cs : List F}
    (hcs : IsMinimalRelatorSequence R cs) (M : FreeGroupDiagram basis cs)
    (hfaces : Nat.card (TwoComplex.GeometricFace M.source) = cs.length) :
    M.IsReduced := sorry

end
