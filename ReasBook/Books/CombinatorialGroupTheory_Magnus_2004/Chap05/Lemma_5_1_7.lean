/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_9_1
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_1_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

set_option autoImplicit false

open Quiver.Path
open Group
open OneComplex.Hom

section

variable {F : Type u} [Group F]

/-!
Primary domain: group-labelled singular disc diagrams and boundary words as products of
region-label conjugates.

Layer triage:
- `source-facing`: a group-labelled ambient `2`-complex together with a singular disc subcomplex
  and its chosen outer boundary loop.
- `core/canonical`: `GroupDiagram` is the owner for the edge-labelling,
  `TwoComplex.Subcomplex.IsSingularDisc` is the owner for the disc-boundary data,
  `GroupDiagram.regionLabels` is the owner for oriented face labels, `TwoComplex.GeometricFace` is
  the owner for actual regions, and `Loop` is the owner for the chosen boundary loop.
- `bridge/view`: the disc boundary loop lives on the subcomplex `1`-skeleton and is compared with
  the ambient labelled diagram through `OneComplex.Hom.mapLoop` applied to
  `S.skeleton.inclusion`; finite enumeration of the geometric region set is expressed by an
  equivalence `Fin n ≃ TwoComplex.GeometricFace S.complex`.

Domain sampling:
1. `GroupDiagram` from Definition `5-1-3` is the existing owner abstraction for a diagram over a
   group.
2. `GroupDiagram.regionLabels` from Definition `5-1-4` is the existing owner for the admissible
   labels read around a region boundary.
3. `TwoComplex.Subcomplex.IsSingularDisc` from Proposition `3-9-1` is the chapter owner for a
   singular disc together with its explicit outer boundary cycle.
4. `OneComplex.Hom.mapLoop` applied to `S.skeleton.inclusion` is the canonical bridge from the
   disc boundary loop to the ambient labelled diagram.
5. `IsConj` is mathlib's canonical owner for “is a conjugate of”, so explicit conjugator data are
   derived witnesses rather than primitive public output.

Primitive vs. derived:
- primitive public data: the ambient group diagram `M`, the singular disc subcomplex `S`, and the
  chosen boundary loop `p` recorded in the owner predicate
  `TwoComplex.Subcomplex.IsSingularDisc S (cyclicPath p)`;
- derived API: an enumeration of the geometric faces of `S.complex` and an ordered `List` of
  factors whose entries lie in the canonical conjugacy owner
  `conjugatesOfSet (M.regionLabels D.1)` for corresponding oriented representatives `D` of those
  regions, and whose product is the ambient label of the chosen disc boundary loop.
-/

/-- Lemma 5-1-7: if `S` is a singular disc in a group-labelled `2`-complex `M`, then the label of
its chosen outer boundary loop is an ordered product of conjugates of labels chosen from the
regions of `S`. -/
-- Proof sketch: argue by induction on the number of geometric faces of the singular disc. When
-- there is a single face, the boundary label is itself a region label. Otherwise remove an outer
-- face along the disc boundary, apply the induction hypothesis to the remaining singular disc, and
-- reinsert one conjugate of a label read from an oriented representative of the deleted geometric
-- face.
theorem boundaryCycleWord_eq_list_prod_conjugates_of_regionLabels
    (M : GroupDiagram F) (S : M.source.Subcomplex)
    (p : Loop S.skeleton.toOneComplex)
    (hS : S.IsSingularDisc (cyclicPath p)) :
    ∃ cs : List F,
      ∃ e : Fin cs.length ≃ S.complex.GeometricFace,
        (∀ i, ∃ D : S.complex.Face, ⟦D⟧ = e i ∧ cs[i] ∈ conjugatesOfSet (M.regionLabels D.1)) ∧
          let q := mapLoop S.skeleton.inclusion p
          M.pathLabel q.2 = cs.prod := by
  sorry

end
