/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_2_1
import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_2_8
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_3_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w uI

open Monoid
open Quiver.Path

noncomputable section

namespace OneComplex

variable (C : OneComplex.{u, v})

/-- A subcomplex of a `1`-complex is given by vertex and edge subsets closed under endpoints and
edge reversal. -/
structure Subcomplex (C : OneComplex.{u, v}) where
  /-- The vertices belonging to the subcomplex. -/
  vertexSet : Set C
  /-- The oriented edges belonging to the subcomplex. -/
  edgeSet : Set C.Edge
  /-- The initial vertex of every edge of the subcomplex again lies in the subcomplex. -/
  initial_mem {e : C.Edge} : e ∈ edgeSet → C.initial e ∈ vertexSet
  /-- The terminal vertex of every edge of the subcomplex again lies in the subcomplex. -/
  terminal_mem {e : C.Edge} : e ∈ edgeSet → C.terminal e ∈ vertexSet
  /-- The reverse of every edge of the subcomplex again lies in the subcomplex. -/
  edgeInv_mem {e : C.Edge} : e ∈ edgeSet → C.edgeInv e ∈ edgeSet

namespace Subcomplex

variable {C : OneComplex.{u, v}}

/-- A geometric edge belongs to a subcomplex when one, equivalently every, oriented
representative belongs to its oriented edge set. -/
def ContainsGeometricEdge (S : Subcomplex C) : GeometricEdge C → Prop :=
  Quotient.lift
    (fun e ↦ e ∈ S.edgeSet)
    (fun e f h ↦ by
      apply propext
      rcases h with rfl | rfl
      · rfl
      · constructor
        · intro he
          change C.edgeInv f ∈ S.edgeSet at he
          have hf : C.edgeInv (C.edgeInv f) ∈ S.edgeSet := S.edgeInv_mem he
          exact (C.edgeInv_involutive f) ▸ hf
        · intro he
          change C.edgeInv f ∈ S.edgeSet
          exact S.edgeInv_mem he)

/-- A geometric edge represented by `e` belongs to the subcomplex exactly when `e` itself belongs
to the oriented edge set. -/
@[simp] theorem containsGeometricEdge_mk_iff
    (S : Subcomplex C) (e : C.Edge) :
    S.ContainsGeometricEdge ⟦e⟧ ↔ e ∈ S.edgeSet :=
  Iff.rfl

/-- A subcomplex inherits a canonical `1`-complex structure from the ambient complex. -/
def toOneComplex (K : Subcomplex C) : OneComplex where
  Vertex := { v : C // v ∈ K.vertexSet }
  Edge := { e : C.Edge // e ∈ K.edgeSet }
  initial := fun e ↦ ⟨C.initial e.1, K.initial_mem e.2⟩
  terminal := fun e ↦ ⟨C.terminal e.1, K.terminal_mem e.2⟩
  edgeInv := fun e ↦ ⟨C.edgeInv e.1, K.edgeInv_mem e.2⟩
  edgeInv_involutive := fun e ↦ Subtype.ext (C.edgeInv_involutive e.1)
  edgeInv_ne := fun e h ↦ C.edgeInv_ne e.1 (congrArg Subtype.val h)
  initial_edgeInv := fun e ↦ by
    apply Subtype.ext
    exact C.initial_edgeInv e.1

/-- The canonical inclusion of a subcomplex into the ambient `1`-complex. -/
def inclusion (K : Subcomplex C) : OneComplex.Hom K.toOneComplex C where
  toVertex := fun v ↦ v.1
  toEdge := fun e ↦ e.1
  map_initial _ := rfl
  map_terminal _ := rfl
  map_edgeInv _ := rfl

/-- A nested subcomplex includes canonically into the larger carried `1`-complex. -/
def inclusionOfSubset {S T : Subcomplex C}
    (hvertex : S.vertexSet ⊆ T.vertexSet) (hedge : S.edgeSet ⊆ T.edgeSet) :
    OneComplex.Hom S.toOneComplex T.toOneComplex where
  toVertex := fun v ↦ ⟨v.1, hvertex v.2⟩
  toEdge := fun e ↦ ⟨e.1, hedge e.2⟩
  map_initial _ := Subtype.ext rfl
  map_terminal _ := Subtype.ext rfl
  map_edgeInv _ := Subtype.ext rfl

/-- Mapping a cyclic path through a nested subcomplex inclusion and then through the ambient
inclusion agrees with mapping it directly through the smaller ambient inclusion. -/
theorem inclusion_mapCyclicPath_inclusionOfSubset
    {S T : Subcomplex C}
    (hvertex : S.vertexSet ⊆ T.vertexSet) (hedge : S.edgeSet ⊆ T.edgeSet)
    (c : CyclicPath S.toOneComplex) :
    T.inclusion.mapCyclicPath ((inclusionOfSubset hvertex hedge).mapCyclicPath c) =
      S.inclusion.mapCyclicPath c := by
  rcases c with ⟨c, hc⟩
  apply Subtype.ext
  change Cycle.map T.inclusion.mapTotal (Cycle.map (inclusionOfSubset hvertex hedge).mapTotal c) =
    Cycle.map S.inclusion.mapTotal c
  refine Quotient.inductionOn' c ?_
  intro l
  apply Cycle.coe_eq_coe.2
  simpa [List.map_map, OneComplex.Hom.mapTotal, OneComplex.Subcomplex.inclusion,
    OneComplex.Subcomplex.inclusionOfSubset, Function.comp] using
    List.IsRotated.refl (List.map S.inclusion.mapTotal l)

/-- The intersection of a family of subcomplexes is again a subcomplex. -/
def iInter {ι : Sort uI} (K : ι → Subcomplex C) : Subcomplex C where
  vertexSet := { v | ∀ i, v ∈ (K i).vertexSet }
  edgeSet := { e | ∀ i, e ∈ (K i).edgeSet }
  initial_mem h i := (K i).initial_mem (h i)
  terminal_mem h i := (K i).terminal_mem (h i)
  edgeInv_mem h i := (K i).edgeInv_mem (h i)

@[inherit_doc iInter] scoped notation3 "⋂ " (...)", " r:60:(scoped K => iInter K) => r

@[simp] theorem mem_vertexSet_iInter {ι : Sort uI} (K : ι → Subcomplex C) {v : C} :
    v ∈ (iInter K).vertexSet ↔ ∀ i, v ∈ (K i).vertexSet :=
  Iff.rfl

@[simp] theorem mem_edgeSet_iInter {ι : Sort uI} (K : ι → Subcomplex C) {e : C.Edge} :
    e ∈ (iInter K).edgeSet ↔ ∀ i, e ∈ (K i).edgeSet :=
  Iff.rfl

/-- The common intersection of a family of subcomplexes includes canonically into each summand. -/
def iInterInclusion {ι : Sort uI} (K : ι → Subcomplex C) (i : ι) :
    OneComplex.Hom (⋂ j, K j).toOneComplex (K i).toOneComplex :=
  inclusionOfSubset
    (fun _ hv ↦ (mem_vertexSet_iInter K).1 hv i)
    (fun _ he ↦ (mem_edgeSet_iInter K).1 he i)

/-- The union of two subcomplexes is obtained by taking the unions of their vertex and edge
carriers. -/
def union (K L : Subcomplex C) : Subcomplex C where
  vertexSet := K.vertexSet ∪ L.vertexSet
  edgeSet := K.edgeSet ∪ L.edgeSet
  initial_mem h := by
    rcases h with h | h
    · exact Or.inl <| K.initial_mem h
    · exact Or.inr <| L.initial_mem h
  terminal_mem h := by
    rcases h with h | h
    · exact Or.inl <| K.terminal_mem h
    · exact Or.inr <| L.terminal_mem h
  edgeInv_mem h := by
    rcases h with h | h
    · exact Or.inl <| K.edgeInv_mem h
    · exact Or.inr <| L.edgeInv_mem h

/-- The left summand of a union is vertexwise contained in that union. -/
theorem vertexSet_subset_union_left (K L : Subcomplex C) :
    K.vertexSet ⊆ (union K L).vertexSet := fun _ hv ↦ Or.inl hv

/-- The left summand of a union is edgewise contained in that union. -/
theorem edgeSet_subset_union_left (K L : Subcomplex C) :
    K.edgeSet ⊆ (union K L).edgeSet := fun _ he ↦ Or.inl he

/-- The right summand of a union is vertexwise contained in that union. -/
theorem vertexSet_subset_union_right (K L : Subcomplex C) :
    L.vertexSet ⊆ (union K L).vertexSet := fun _ hv ↦ Or.inr hv

/-- The right summand of a union is edgewise contained in that union. -/
theorem edgeSet_subset_union_right (K L : Subcomplex C) :
    L.edgeSet ⊆ (union K L).edgeSet := fun _ he ↦ Or.inr he

end Subcomplex

end OneComplex

namespace OneComplex.Subcomplex

variable {C : OneComplex}

/-- The total-edge map induced by a subcomplex inclusion is injective. -/
theorem mapTotal_injective (K : Subcomplex C) :
    Function.Injective K.inclusion.mapTotal := by
  sorry

end OneComplex.Subcomplex

namespace TwoComplex

/-- A subcomplex of a `2`-complex is given by a subcomplex of the ambient `1`-skeleton together
with a family of ambient faces whose canonical attaching cycles already lie in that
`1`-skeleton subcomplex. -/
structure Subcomplex (C : TwoComplex.{w}) where
  /-- The underlying subcomplex of the ambient `1`-skeleton. -/
  skeleton : OneComplex.Subcomplex C.skeleton
  /-- The ambient faces belonging to the subcomplex. -/
  faceSet : Set C.Face
  /-- The face set is closed under orientation reversal. -/
  faceInv_mem {D : C.Face} : D ∈ faceSet → C.faceInv D ∈ faceSet
  /-- The boundary cycle of a face belonging to the subcomplex, regarded in the subcomplex
  `1`-skeleton. -/
  boundary (D : { D : C.Face // D ∈ faceSet }) : CyclicPath (skeleton.toOneComplex)
  /-- The subcomplex boundary cycle maps to the ambient attaching cycle. -/
  boundary_eq (D : { D : C.Face // D ∈ faceSet }) :
      skeleton.inclusion.mapCyclicPath (boundary D) = C.boundary D.1

namespace Subcomplex

variable {C : TwoComplex.{w}}

/-- A geometric face belongs to a subcomplex when one, equivalently every, oriented
representative belongs to its oriented face set. -/
def ContainsGeometricFace (S : Subcomplex C) : GeometricFace C → Prop :=
  Quotient.lift
    (fun D ↦ D ∈ S.faceSet)
    (fun D E h ↦ by
      apply propext
      rcases h with rfl | rfl
      · rfl
      · constructor
        · intro hD
          change C.faceInv E ∈ S.faceSet at hD
          have hE : C.faceInv (C.faceInv E) ∈ S.faceSet := S.faceInv_mem hD
          exact (C.faceInv_involutive E) ▸ hE
        · intro hD
          change C.faceInv E ∈ S.faceSet
          exact S.faceInv_mem hD)

/-- A geometric face represented by `D` belongs to the subcomplex exactly when `D` itself belongs
to the oriented face set. -/
@[simp] theorem containsGeometricFace_mk_iff
    (S : Subcomplex C) (D : C.Face) :
    S.ContainsGeometricFace ⟦D⟧ ↔ D ∈ S.faceSet :=
  Iff.rfl

/-- The ambient total-edge map of a `2`-complex subcomplex reflects cyclic reduction. -/
theorem isCyclicallyReducedCycle_mapCyclicPath_iff (S : Subcomplex C)
    (c : CyclicPath S.skeleton.toOneComplex) :
    IsCyclicallyReducedCycle (S.skeleton.inclusion.mapCyclicPath c) ↔
      IsCyclicallyReducedCycle c := by
  sorry

/-- Mapping the inverse of a cyclic path along the inclusion of a subcomplex agrees with taking
the inverse after mapping. -/
theorem mapCyclicPath_inverseCycle (S : Subcomplex C)
    (c : CyclicPath S.skeleton.toOneComplex) :
    S.skeleton.inclusion.mapCyclicPath (inverseCycle c) =
      inverseCycle (S.skeleton.inclusion.mapCyclicPath c) := by
  sorry

/-- The ambient cyclic-path map induced by a subcomplex inclusion is injective. -/
theorem mapCyclicPath_injective (S : Subcomplex C) :
    Function.Injective S.skeleton.inclusion.mapCyclicPath := by
  sorry

/-- The `2`-complex carried by a subcomplex of an ambient `2`-complex. -/
def complex (S : Subcomplex C) : TwoComplex where
  skeleton := S.skeleton.toOneComplex
  Face := { D : C.Face // D ∈ S.faceSet }
  boundary := S.boundary
  boundary_cyclicallyReduced := by
    intro D
    have h : IsCyclicallyReducedCycle (S.skeleton.inclusion.mapCyclicPath (S.boundary D)) := by
      simpa [S.boundary_eq D] using C.boundary_cyclicallyReduced D.1
    exact (S.isCyclicallyReducedCycle_mapCyclicPath_iff (S.boundary D)).1 h
  faceInv := fun D ↦ ⟨C.faceInv D.1, S.faceInv_mem D.2⟩
  faceInv_involutive := by
    intro D
    ext
    exact C.faceInv_involutive D.1
  faceInv_ne := by
    intro D h
    exact C.faceInv_ne D.1 (congrArg Subtype.val h)
  boundary_faceInv := by
    intro D
    apply S.mapCyclicPath_injective
    rw [S.boundary_eq ⟨C.faceInv D.1, S.faceInv_mem D.2⟩, S.mapCyclicPath_inverseCycle,
      S.boundary_eq D]
    exact C.boundary_faceInv D.1

/-- Restricting a subcomplex to an inverse-closed face subset keeps the same `1`-skeleton and
inherits the boundary data from the ambient subcomplex. -/
def restrictFaces (S : Subcomplex C) (faceSet : Set C.Face) (hfaceSet : faceSet ⊆ S.faceSet)
    (hfaceInv : ∀ ⦃D : C.Face⦄, D ∈ faceSet → D⁻¹ ∈ faceSet) : Subcomplex C where
  skeleton := S.skeleton
  faceSet := faceSet
  faceInv_mem := fun hD ↦ hfaceInv hD
  boundary := fun D ↦ S.boundary ⟨D.1, hfaceSet D.2⟩
  boundary_eq := fun D ↦ S.boundary_eq ⟨D.1, hfaceSet D.2⟩

/-- Restricting to one geometric face keeps exactly one oriented face of `S` together with its
inverse. This is the canonical one-face specialization of `restrictFaces`. -/
def restrictFace (S : Subcomplex C) (D : C.Face) (hD : D ∈ S.faceSet) : Subcomplex C :=
  S.restrictFaces
    { E | E = D ∨ E = D⁻¹ }
    (fun E hE ↦ by
      rcases hE with rfl | rfl
      · exact hD
      · exact S.faceInv_mem hD)
    (fun {E} hE ↦ by
      rcases hE with rfl | hE
      · exact Or.inr rfl
      · exact Or.inl <| by simpa [hE] using C.faceInv_involutive D)

/-- The union of two subcomplexes is obtained by taking the union of their `1`-skeleta and face
sets. -/
def union (S T : Subcomplex C) : Subcomplex C where
  skeleton := S.skeleton.union T.skeleton
  faceSet := S.faceSet ∪ T.faceSet
  faceInv_mem h := by
    rcases h with h | h
    · exact Or.inl <| S.faceInv_mem h
    · exact Or.inr <| T.faceInv_mem h
  boundary D := by
    classical
    by_cases hD : D.1 ∈ S.faceSet
    · exact
        (OneComplex.Subcomplex.inclusionOfSubset
          (OneComplex.Subcomplex.vertexSet_subset_union_left S.skeleton T.skeleton)
          (OneComplex.Subcomplex.edgeSet_subset_union_left S.skeleton T.skeleton)).mapCyclicPath
          (S.boundary ⟨D.1, hD⟩)
    · exact
        (OneComplex.Subcomplex.inclusionOfSubset
          (OneComplex.Subcomplex.vertexSet_subset_union_right S.skeleton T.skeleton)
          (OneComplex.Subcomplex.edgeSet_subset_union_right S.skeleton T.skeleton)).mapCyclicPath
          (T.boundary ⟨D.1, Or.resolve_left D.2 hD⟩)
  boundary_eq D := by
    classical
    by_cases hD : D.1 ∈ S.faceSet
    · simpa [hD] using
        (OneComplex.Subcomplex.inclusion_mapCyclicPath_inclusionOfSubset
          (OneComplex.Subcomplex.vertexSet_subset_union_left S.skeleton T.skeleton)
          (OneComplex.Subcomplex.edgeSet_subset_union_left S.skeleton T.skeleton)
          (S.boundary ⟨D.1, hD⟩)).trans
          (S.boundary_eq ⟨D.1, hD⟩)
    · simpa [hD] using
        (OneComplex.Subcomplex.inclusion_mapCyclicPath_inclusionOfSubset
          (OneComplex.Subcomplex.vertexSet_subset_union_right S.skeleton T.skeleton)
          (OneComplex.Subcomplex.edgeSet_subset_union_right S.skeleton T.skeleton)
          (T.boundary ⟨D.1, Or.resolve_left D.2 hD⟩)).trans
          (T.boundary_eq ⟨D.1, Or.resolve_left D.2 hD⟩)

/-- A face-boundary vertex of a nested subcomplex remains a face-boundary vertex in the parent
subcomplex. -/
theorem vertexOnFace_of_subset (S T : Subcomplex C)
    (hvertex : T.skeleton.vertexSet ⊆ S.skeleton.vertexSet)
    (hedge : T.skeleton.edgeSet ⊆ S.skeleton.edgeSet)
    (hface : T.faceSet ⊆ S.faceSet)
    {v : T.complex.skeleton} {D : T.complex.Face} :
    T.complex.VertexOnFace v D →
      S.complex.VertexOnFace ⟨v.1, hvertex v.2⟩ ⟨D.1, hface D.2⟩ := by
  sorry

end Subcomplex

/-- Proposition 3-3-5: if a `2`-complex `C` is the union of a family of subcomplexes indexed by
`I`, all containing the same base vertex `v`, and distinct subcomplexes meet only in that vertex,
then the fundamental group `π(C, v)` is isomorphic to the indexed free product of the
fundamental groups of the subcomplexes. -/
-- Layer triage:
-- `source-facing`: an ambient `2`-complex `C`, a family of subcomplexes `pieces i`, a common
-- base vertex `v`, and the free-product decomposition of `π(C, v)`.
-- `core/canonical`: `TwoComplex.fundamentalGroup`, written `π(C, v)`, is the chapter owner for
-- the ambient and piecewise fundamental groups, `Monoid.CoprodI` is mathlib's owner for indexed
-- free products, `OneComplex.Subcomplex` is the upstream owner for the `1`-skeleton part of
-- each subcomplex, and `Quiver.Path.CyclicPath` is the owner for canonical face-boundary data.
-- `bridge/view`: `TwoComplex.Subcomplex` adds only the ambient face subset together with the
-- internal cyclic boundary data needed to view those faces as a genuine `2`-dimensional
-- subcomplex.
-- Domain sampling:
-- 1. `OneComplex.Subcomplex` is the project owner for subcomplexes of the `1`-skeleton.
-- 2. `OneComplex.Subcomplex.toOneComplex` is the derived `1`-complex carried by such a
--    subcomplex.
-- 3. `Quiver.Path.CyclicPath` is the canonical owner for face boundaries, and
--    `OneComplex.Hom.mapCyclicPath` applied to the inclusion `skeleton.inclusion` is the bridge
--    API comparing internal boundary cycles with ambient attaching cycles.
-- 4. `TwoComplex.fundamentalGroup`, written `π(C, v)`, and `Monoid.CoprodI` are the canonical
--    owners in the conclusion.
-- Proof sketch: choose maximal trees in the pieces through the common base vertex, observe that
-- their union is a maximal tree in `C`, identify the fundamental group of the `1`-skeleton with
-- the free product of the piecewise `1`-skeleton groups, and then show that the face relations of
-- `C` are exactly the union of the face relations contributed by the subcomplexes.
theorem fundamentalGroup_nonempty_mulEquiv_coprodI_of_subcomplex_cover
    {I : Type uI} (C : TwoComplex.{w}) (pieces : I → Subcomplex C) (v : C.skeleton)
    (hv : ∀ i, v ∈ (pieces i).skeleton.vertexSet)
    (hcover_vertex : ∀ x : C.skeleton, ∃ i, x ∈ (pieces i).skeleton.vertexSet)
    (hcover_edge : ∀ e : C.skeleton.Edge, ∃ i, e ∈ (pieces i).skeleton.edgeSet)
    (hcover_face : ∀ D : C.Face, ∃ i, D ∈ (pieces i).faceSet)
    (hinter_vertex :
      ∀ {i j : I} (hij : i ≠ j) {x : C.skeleton},
        x ∈ (pieces i).skeleton.vertexSet →
        x ∈ (pieces j).skeleton.vertexSet →
        x = v)
    (hdisjoint_edge :
      ∀ {i j : I} (hij : i ≠ j) {e : C.skeleton.Edge},
        e ∈ (pieces i).skeleton.edgeSet →
        e ∈ (pieces j).skeleton.edgeSet →
        False)
    (hdisjoint_face :
      ∀ {i j : I} (hij : i ≠ j) {D : C.Face},
        D ∈ (pieces i).faceSet →
        D ∈ (pieces j).faceSet →
        False) :
    Nonempty (π(C, v) ≃* CoprodI (fun i ↦ π((pieces i).complex, ⟨v, hv i⟩))) := sorry

end TwoComplex
