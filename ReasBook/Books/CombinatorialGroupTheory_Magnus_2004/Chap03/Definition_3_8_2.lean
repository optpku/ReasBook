/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_8_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

noncomputable section

/-
Primary domain: Fuchsian complexes, geometric-edge actions, and reflections.

Layer triage:
- `source-facing`: a nontrivial element acting as a reflection in a geometric edge of a Fuchsian
  complex.
- `core/canonical`: `OneComplex.GeometricEdge` is the owner for geometric edges,
  `TwoComplex.AutAction.geometricEdgePerm` is the owner for the induced action on those edges, and
  `FuchsianComplex.WithoutReflections`,
  `Quiver.IsStronglyConnected (Quiver.Symmetrify _)`, `TwoComplex.IsSimplyConnected`, and
  `TwoComplex.EmbedsInPlane` are the owner predicates asserting the geometric-edge freeness and
  ambient connected/simply connected/planar hypotheses used below.
- `bridge/view`: the oriented-edge phrase “the geometric edge represented by `e`” is a companion
  representative-level view of the intrinsic fixed-geometric-edge condition.

Domain sampling:
1. `OneComplex.GeometricEdge` from Definition `3-2-1` is the canonical carrier for geometric
   edges, so a reflection should be phrased by fixing one of these quotient edges rather than by
   primitive case-splitting on an oriented representative.
2. `TwoComplex.AutAction.geometricEdgePerm` from Proposition `3-7-1` is the canonical induced
   action on geometric edges and already packages the “send `e` to `e` or `e⁻¹`” quotient
   relation.
3. `FuchsianComplex.WithoutReflections` from Proposition `3-7-1` is the project owner predicate
   for the absence of nontrivial fixed geometric edges.
4. `Quiver.IsStronglyConnected (Quiver.Symmetrify _)`, `TwoComplex.IsSimplyConnected`, and
   `TwoComplex.EmbedsInPlane` are the direct owner predicates for the geometric hypotheses imported
   from Proposition `3-7-3`.

Primitive vs. derived:
- primitive public data here: none beyond the existing `FuchsianComplex` action;
- derived API here: the reflection predicates and the representative-level equivalence for an
  oriented edge.
-/

namespace FuchsianComplex

variable {G : Type u} [Group G]
variable (K : FuchsianComplex G)

local notation "Edge" => OneComplex.Edge K.complex.skeleton
local notation "GeometricEdge" => OneComplex.GeometricEdge K.complex.skeleton

/-- Definition 3-8-2: a nontrivial element is a reflection in a geometric edge when the action
fixes that geometric edge. -/
def IsReflectionIn (g : G) (e : GeometricEdge) : Prop :=
  g ≠ 1 ∧ (K.action g).geometricEdgePerm e = e

/-- The owner-level geometric-edge formulation is equivalent to the representative-level condition
that the oriented edge is sent to itself or to its reverse. -/
theorem isReflectionIn_iff (g : G) (e : Edge) :
    K.IsReflectionIn g ⟦e⟧ ↔
      g ≠ 1 ∧ ((K.action g).edgePerm e = e ∨ (K.action g).edgePerm e = e⁻¹) := by
  constructor
  · rintro ⟨hg, hfix⟩
    refine ⟨hg, ?_⟩
    exact Quotient.exact hfix
  · rintro ⟨hg, hfix⟩
    exact ⟨hg, Quotient.sound hfix⟩

/-- An element is a reflection for the action when it preserves some geometric edge. -/
def IsReflection (g : G) : Prop :=
  ∃ e : GeometricEdge, K.IsReflectionIn g e

/-- The chapter owner predicate `WithoutReflections` is exactly the statement that no element is a
reflection in any geometric edge. -/
theorem withoutReflections_iff_forall_not_isReflectionIn :
    K.WithoutReflections ↔ ∀ g : G, ∀ e : GeometricEdge, ¬ K.IsReflectionIn g e := by
  constructor
  · intro h g e
    rintro ⟨hg, hfix⟩
    exact h hg e hfix
  · intro h g hg e hfix
    exact h g e ⟨hg, hfix⟩

/-- The intrinsic geometric-edge definition of a reflection is equivalent to the source-level
existence of an oriented edge sent to itself or to its reverse. -/
theorem isReflection_iff (g : G) :
    K.IsReflection g ↔
      ∃ e : Edge, g ≠ 1 ∧ ((K.action g).edgePerm e = e ∨ (K.action g).edgePerm e = e⁻¹) := by
  constructor
  · rintro ⟨e, he⟩
    rcases Quotient.exists_rep e with ⟨e, rfl⟩
    exact ⟨e, (K.isReflectionIn_iff g e).1 he⟩
  · rintro ⟨e, he⟩
    exact ⟨⟦e⟧, (K.isReflectionIn_iff g e).2 he⟩

/-- The owner predicate `WithoutReflections` is equivalent to the absence of reflections. -/
theorem withoutReflections_iff_forall_not_isReflection :
    K.WithoutReflections ↔ ∀ g : G, ¬ K.IsReflection g := by
  simpa [IsReflection] using K.withoutReflections_iff_forall_not_isReflectionIn

/-- A Fuchsian complex fails to be without reflections exactly when some group element is a
reflection. -/
theorem not_withoutReflections_iff_exists_isReflection :
    ¬ K.WithoutReflections ↔ ∃ g : G, K.IsReflection g := by
  rw [K.withoutReflections_iff_forall_not_isReflection]
  simp

/-- A reflection in an edge is necessarily an involution. -/
-- Proof sketch: an element fixing a geometric edge of the planar complex reverses the two local
-- sides of that edge, so its square fixes the adjacent geometric faces. Regularity on geometric
-- faces then forces that square to be the identity element.
theorem sq_eq_one_of_isReflectionIn
    (hconnected : Quiver.IsStronglyConnected (Quiver.Symmetrify K.complex.skeleton))
    (hsimply : TwoComplex.IsSimplyConnected K.complex)
    (hplanar : K.complex.EmbedsInPlane)
    (hreg : K.action.IsRegularOnGeometricFaces)
    {g : G} {e : GeometricEdge}
    (hg : K.IsReflectionIn g e) :
    g ^ 2 = 1 := sorry

end FuchsianComplex
