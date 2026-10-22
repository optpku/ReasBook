/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_7_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

set_option autoImplicit false

noncomputable section

open MulAction TwoComplex

/-!
Primary domain: NEC groups, Fuchsian complexes, and regular actions on geometric faces.

Layer triage:
- `source-facing`: a group `G` together with a planar simply connected connected Fuchsian complex
  on which `G` acts regularly on geometric faces.
- `core/canonical`: `FuchsianComplex` is the chapter owner for the actual `2`-complex together
  with the action by automorphisms, while
  `Quiver.IsStronglyConnected (Quiver.Symmetrify _)`, `TwoComplex.IsSimplyConnected`,
  `TwoComplex.EmbedsInPlane`, and `TwoComplex.AutAction.geometricFaceMulAction` are the owner
  predicates and constructions for the geometric hypotheses and the induced action on geometric
  faces; `MulAction.IsPretransitive` and `IsCancelSMul` are the standard owners for transitivity
  and freeness of that action.
- `bridge/view`: `TwoComplex.AutAction.IsRegularOnGeometricFaces` below packages the textbook
  phrase “regular on geometric faces” in terms of those canonical group-action owners.

Domain sampling:
1. `TwoComplex.AutAction` from Proposition `3-7-1` is the chapter owner for an action of `G` on
   a `2`-complex by automorphisms.
2. `FuchsianComplex` from Proposition `3-7-1` is the owner for the underlying complex together
   with that action.
3. `Quiver.IsStronglyConnected (Quiver.Symmetrify _)`, `TwoComplex.IsSimplyConnected`, and
   `TwoComplex.EmbedsInPlane` are the direct owner predicates for the connected, simply connected,
   and planar hypotheses used in Proposition `3-7-3`.
4. `MulAction.IsPretransitive`, `IsCancelSMul`, and
   `isCancelSMul_iff_stabilizer_eq_bot` are the canonical owner notions for a transitive free
   action and its stabilizer reformulation.

Primitive vs. derived:
- primitive data: the actual Fuchsian complex;
- derived API: the induced geometric-face action and the regularity property of that action.
-/

namespace TwoComplex.AutAction

variable {G : Type u} [Group G] {C : TwoComplex}

/-- The induced action on geometric faces is regular when the geometric-face set is nonempty and
the action is transitive with trivial stabilizers, equivalently transitive and free. -/
def IsRegularOnGeometricFaces (ρ : TwoComplex.AutAction G C) : Prop :=
  letI := ρ.geometricFaceMulAction
  Nonempty (GeometricFace C) ∧ IsPretransitive G (GeometricFace C) ∧
    IsCancelSMul G (GeometricFace C)

/-- The stabilizer formulation of regularity on geometric faces is a companion to the canonical
`Nonempty ∧ IsPretransitive ∧ IsCancelSMul` owner shape. -/
theorem isRegularOnGeometricFaces_iff_pretransitive_and_stabilizer_eq_bot
    (ρ : TwoComplex.AutAction G C) :
    letI := ρ.geometricFaceMulAction
    ρ.IsRegularOnGeometricFaces ↔
      Nonempty (GeometricFace C) ∧
      IsPretransitive G (GeometricFace C) ∧
        ∀ D : GeometricFace C, stabilizer G D = ⊥ := by
  letI := ρ.geometricFaceMulAction
  constructor
  · rintro ⟨hfaces, htrans, hfree⟩
    exact ⟨hfaces, htrans, fun D ↦ IsCancelSMul.stabilizer_eq_bot D⟩
  · rintro ⟨hfaces, htrans, hstab⟩
    exact ⟨hfaces, htrans, (isCancelSMul_iff_stabilizer_eq_bot).2 hstab⟩

/-- Unfolding `IsRegularOnGeometricFaces` gives transitivity on geometric faces together with
pointwise triviality of geometric-face stabilizers, and in particular a nonempty face set. -/
theorem isRegularOnGeometricFaces_iff (ρ : TwoComplex.AutAction G C) :
    letI := ρ.geometricFaceMulAction
    ρ.IsRegularOnGeometricFaces ↔
      Nonempty (GeometricFace C) ∧
      (∀ D E : GeometricFace C, ∃ g : G, g • D = E) ∧
        ∀ ⦃g : G⦄, g ≠ 1 → ∀ D : GeometricFace C, g • D ≠ D := by
  letI := ρ.geometricFaceMulAction
  constructor
  · rintro ⟨hfaces, htrans, hfree⟩
    refine ⟨hfaces, ?_, ?_⟩
    · intro D E
      simpa using (exists_smul_eq G D E)
    · intro g hg D hD
      have : g = 1 := by
        exact IsCancelSMul.eq_one_of_smul (by simpa using hD)
      exact hg this
  · rintro ⟨hfaces, htrans, hfix⟩
    refine ⟨hfaces, ⟨fun D E ↦ by simpa using htrans D E⟩, ?_⟩
    rw [isCancelSMul_iff_eq_one_of_smul_eq]
    intro g D hD
    by_contra hg
    exact hfix hg D (by simpa using hD)

end TwoComplex.AutAction

/-- Definition 3-8-1: an NEC group is a group admitting a connected simply connected planar
Fuchsian complex whose action is regular on a nonempty set of geometric faces. -/
class IsNECGroup (G : Type u) [Group G] : Prop where
  /-- An NEC group admits a planar simply connected connected Fuchsian complex with a regular
  geometric-face action of `G`. -/
  exists_fuchsianComplex :
    ∃ K : FuchsianComplex.{u, v} G,
      Quiver.IsStronglyConnected (Quiver.Symmetrify K.complex.skeleton) ∧
        TwoComplex.IsSimplyConnected K.complex ∧
        K.complex.EmbedsInPlane ∧
        K.action.IsRegularOnGeometricFaces
