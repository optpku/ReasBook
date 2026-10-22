/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_1_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

set_option autoImplicit false

section

variable {X : Type u} {F : Type v} [Group F]

/-!
Primary domain: free-group diagrams for an ordered finite sequence of nontrivial relators in a
free group with chosen basis.

Layer triage:
- `source-facing`: a basis `basis : FreeGroupBasis X F` together with a finite ordered sequence
  `relators : List F` of nontrivial elements, and a diagram whose geometric faces are in ordered
  bijection with that full sequence.
- `core/canonical`: `FreeGroupBasis X F` is the owner abstraction for a free group with chosen
  basis, while `FreeGroupDiagram basis relators` from Definition `5-1-5` is the chapter owner for
  such diagrams.
- `bridge/view`: `GroupDiagram.pathLabel` and `GroupDiagram.pathLabelWord` are the canonical
  boundary-label evaluators used in the owner fields of `FreeGroupDiagram` and in the ordered
  face-realization conclusion asserted below.

Domain sampling:
1. `FreeGroupBasis X F` is the established owner for a free group with chosen basis.
2. `FreeGroupDiagram basis relators` from Definition `5-1-5` is the chapter owner abstraction
   for a diagram with relator list `relators`.
3. `GroupDiagram.pathLabel` is the canonical boundary-label evaluation map already built into the
   owner field `FreeGroupDiagram.outerBoundary_product`.
4. `GroupDiagram.pathLabelWord` is the canonical source-facing boundary-word API used in the
   cyclically reduced region condition from Definition `5-1-5`.
5. Chapter `2` owner-level statements such as
   `FreeGroupBasis.basisLetterOccurs_of_mem_normalClosure_singleton_of_isCyclicallyReduced` are
   organized around an arbitrary `basis : FreeGroupBasis X F`, confirming that the ambient owner
   is the free group with chosen basis rather than the concrete model `FreeGroup X`.

Primitive vs. derived:
- primitive public data: the chosen basis `basis : FreeGroupBasis X F`, the relator list
  `relators : List F`, and the pointwise nontriviality hypothesis on that ordered sequence;
- derived API: the geometric `2`-complex, boundary loop, reducedness, and conjugacy conditions
  already stored by `FreeGroupDiagram basis relators`, together with the ordered face-by-face
  realization conclusion asserted directly by Theorem `5-1-6`.
-/

namespace FreeGroupDiagram

-- Proof sketch: write each nontrivial relator `cᵢ` as a conjugate of a cyclically reduced word,
-- build the corresponding one-face lollipop diagram for each factor, and attach those diagrams in
-- the given order around a common basepoint. This gives one geometric face for each index `i`.
-- Whenever the outer boundary word has adjacent inverse letters, fold or delete the cancellable
-- boundary pair; this preserves the cyclically reduced face labels and the ordered face data while
-- strictly shortening the boundary. Iterating terminates with a reduced outer boundary word.
/-- Theorem 5-1-6: every finite ordered sequence of nontrivial elements of a free group with
chosen basis `basis` admits a chapter-`5` free-group diagram whose geometric faces are in ordered
bijective correspondence with the full relator sequence. -/
theorem exists_orderedFaceRealization (basis : FreeGroupBasis X F) (relators : List F)
    (hrelators : ∀ i : Fin relators.length, relators.get i ≠ 1) :
    ∃ D : FreeGroupDiagram basis relators,
      ∃ e : Fin relators.length ≃ D.source.GeometricFace,
        ∀ i : Fin relators.length,
          ∃ E : D.source.Face, ⟦E⟧ = e i ∧
            ∃ v : D.source.skeleton, ∃ q : D.source.BoundaryPath E v,
              FreeGroup.IsCyclicallyReduced (D.toGroupDiagram.pathLabelWord basis q.1) ∧
                IsConj (D.toGroupDiagram.pathLabel q.1) (relators.get i) := by
  sorry

end FreeGroupDiagram

end
