/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_3_5
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_5_6

universe u v w

set_option autoImplicit false

noncomputable section

open Quiver
open Quiver.Path

/-!
Primary domain: planar `2`-complexes, subcomplex boundaries, and the area measure attached to an
angle measure.

Layer triage:
- `source-facing`: an angle measure on a planar `2`-complex, the induced area of a subcomplex,
  the simple-boundary condition for a subcomplex, and the hypothesis that two subcomplexes meet
  exactly along a common boundary arc.
- `core/canonical`: `TwoComplex.Subcomplex` from Proposition `3-3-5` is the owner for carried
  subcomplexes and their union, `TwoComplex.EmbedsInPlane` from Proposition `3-5-6` is the owner
  for planarity, and `Quiver.Path.IsSimpleCycle` from Definition `3-2-4` is the owner predicate
  for simple cyclic boundaries.
- `bridge/view`: an actual common boundary arc is represented by a simple path in the ambient
  `1`-skeleton, and the intersection condition is expressed by comparing the carried vertex and
  edge data of the two subcomplexes with the support of that path.

Domain sampling:
1. `TwoComplex.Subcomplex` from Proposition `3-3-5` is the owner abstraction for the regions
   appearing in the statement, so this file should speak directly about subcomplexes and their
   canonical union.
2. `OneComplex.Subcomplex.union` and `TwoComplex.Subcomplex.union` from Proposition `3-3-5` are
   the canonical owner operations for unions of carried subcomplexes.
3. `Quiver.Path.vertices` and `Quiver.Path.edgeList` are the owner API for the support of a path,
   so the common-boundary-arc predicate should use them directly rather than duplicating a local
   support wrapper.
4. `Quiver.Path.IsSimpleCycle` from Definition `3-2-4` is already the owner predicate for a
   simple boundary cycle, so the subcomplex boundary condition should be phrased through it rather
   than by introducing a new cycle-simplicity notion.

Primitive vs. derived:
- primitive data: the ambient complex `C`, the angle measure `α`, the subcomplexes `S₁` and
  `S₂`, and the witnessing simple path for the common boundary arc;
- derived API: the associated area of a subcomplex, the source-facing predicates
  `Subcomplex.HasSimpleBoundary` and `Subcomplex.IntersectsOnlyInCommonBoundaryArc`, and the
  additivity theorem for unions under those hypotheses.
-/

namespace TwoComplex

variable {C : TwoComplex.{w}}

/-- An angle measure on a `2`-complex carries its associated area measure on subcomplexes. -/
structure AngleMeasure (C : TwoComplex.{w}) where
  /-- The associated area measure assigned to subcomplexes by the angle measure. -/
  associatedAreaMeasure : Subcomplex C → ℝ

namespace Subcomplex

/-- A subcomplex has simple boundary when its boundary is carried by a simple cyclic path in its
`1`-skeleton. -/
def HasSimpleBoundary (S : Subcomplex C) : Prop :=
  ∃ c : CyclicPath S.complex.skeleton, IsSimpleCycle c

/-- Two subcomplexes intersect only in a common boundary arc when the intersection of their
`1`-skeleta is exactly the support of a simple path in the ambient `1`-skeleton. -/
def IntersectsOnlyInCommonBoundaryArc (S₁ S₂ : Subcomplex C) : Prop :=
  ∃ (start finish : C.skeleton) (path : Quiver.Path start finish),
    IsSimple path ∧
      (∀ v : C.skeleton,
        v ∈ S₁.skeleton.vertexSet ∩ S₂.skeleton.vertexSet ↔ v ∈ path.vertices) ∧
      ∀ e : C.skeleton.Edge,
        e ∈ S₁.skeleton.edgeSet ∩ S₂.skeleton.edgeSet ↔ ∃ t ∈ edgeList path, t.hom.1 = e

end Subcomplex

namespace AngleMeasure

/-- Proposition 3-7-5: if two subcomplexes with simple boundaries in a planar complex intersect
only in a common boundary arc, then the associated area measure is additive on their union. -/
-- Proof sketch: compare the boundary-angle contributions of `S₁`, `S₂`, and `S₁ ∪ S₂`. Along the
-- common boundary arc, complementary interior angles cancel, while the two endpoints of the arc
-- contribute the missing `2π` correction. Substituting the resulting boundary-curvature identity
-- into the definition of the associated area measure yields the claimed additivity formula.
theorem associatedAreaMeasure_union_eq_add_of_intersectsOnlyInCommonBoundaryArc
    (α : AngleMeasure C) (hplanar : C.EmbedsInPlane)
    (S₁ S₂ : Subcomplex C) (hS₁ : S₁.HasSimpleBoundary) (hS₂ : S₂.HasSimpleBoundary)
    (hinter : S₁.IntersectsOnlyInCommonBoundaryArc S₂) :
    α.associatedAreaMeasure (S₁.union S₂) =
      α.associatedAreaMeasure S₁ + α.associatedAreaMeasure S₂ := sorry

end AngleMeasure

end TwoComplex
