/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_9_1
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_1_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open CategoryTheory Quiver.Path OneComplex OneComplex.Hom

set_option autoImplicit false

noncomputable section

section

variable {X : Type u} {F : Type v} [Group F]

local instance instDecidableEqFreeGroupDiagram : DecidableEq X := Classical.decEq X

-- Primary domain: small-cancellation diagrams over a free group with a chosen basis.
--
-- Layer triage:
-- `source-facing`: a group-labelled singular disc in the free group whose chosen outer boundary
-- loop reads the prescribed product `c₁ ⋯ cₙ` and whose region boundary words read the listed
-- relators up to conjugacy.
-- `core/canonical`: `FreeGroupBasis X F` is the owner abstraction for a free group with chosen
-- basis, `GroupDiagram F` is the owner abstraction for an oriented map labelled by group
-- elements, `TwoComplex.Subcomplex.IsSingularDisc` is the chapter owner for genuine disc-diagram
-- geometry, and `Loop` together with `cyclicPath` are the owner abstractions for boundary loops
-- and boundary cycles.
-- `bridge/view`: `TwoComplex.fullSubcomplex` turns the whole labelled map into the ambient
-- subcomplex required by `IsSingularDisc`, `basis.repr` reads an intrinsic element of `F` as a
-- reduced word in the chosen basis, and `GroupDiagram.pathLabelWord` is the source-facing
-- boundary word obtained by concatenating those reduced edge-label words along a path.
--
-- Domain sampling:
-- 1. `FreeGroupBasis X F` is the established owner for “a free group with a given basis”.
-- 2. `GroupDiagram F` from Definition `5-1-3` is the existing owner for a labelled oriented map.
-- 3. `GroupDiagram.pathLabel` from Definition `5-1-4` is the existing owner for multiplying edge
--    labels along a path.
-- 4. `TwoComplex.Subcomplex.IsSingularDisc` from Proposition `3-9-1` is the chapter owner for a
--    planar simply connected disc with explicit boundary cycle and geometric edge incidence.
-- 5. `IsConj` is mathlib's owner relation for “is a conjugate of”, while
--    `FreeGroup.IsCyclicallyReduced` is the owner predicate for cyclically reduced reduced words.
--
-- Primitive vs. derived:
-- the primitive data are the underlying `GroupDiagram`, the chosen outer boundary loop, the
-- singular-disc owner proof for its cyclic boundary, and the relator conditions. The ambient
-- connectedness and simple connectedness of the whole labelled map are derived from the
-- singular-disc owner on the full subcomplex. Finiteness is likewise derived from that owner,
-- while the reduced and cyclically reduced boundary conditions are stated directly on the
-- source-facing boundary word `pathLabelWord`; the bridge back to the intrinsic product
-- `pathLabel` is derived via `basis.repr`.

namespace TwoComplex

/-- The full `1`-skeleton subcomplex of a `2`-complex, carrying every vertex and edge. -/
def fullOneSubcomplex (C : TwoComplex) : OneComplex.Subcomplex C.skeleton where
  vertexSet := Set.univ
  edgeSet := Set.univ
  initial_mem _ := by simp
  terminal_mem _ := by simp
  edgeInv_mem _ := by simp

/-- The ambient `1`-skeleton maps canonically onto the `1`-skeleton of the full subcomplex. -/
def toFullOneSubcomplex (C : TwoComplex) :
    OneComplex.Hom C.skeleton C.fullOneSubcomplex.toOneComplex where
  toVertex v := ⟨v, by simp [fullOneSubcomplex]⟩
  toEdge e := ⟨e, by simp [fullOneSubcomplex]⟩
  map_initial _ := Subtype.ext rfl
  map_terminal _ := Subtype.ext rfl
  map_edgeInv _ := Subtype.ext rfl

/-- The full subcomplex of a `2`-complex, carrying every vertex, edge, and face. -/
def fullSubcomplex (C : TwoComplex) : Subcomplex C where
  skeleton := C.fullOneSubcomplex
  faceSet := Set.univ
  faceInv_mem _ := by simp
  boundary D := C.toFullOneSubcomplex.mapCyclicPath (C.boundary D.1)
  boundary_eq D := by
    let fullInclusion := C.fullOneSubcomplex.inclusion
    let toFull := C.toFullOneSubcomplex
    apply Subtype.ext
    change Cycle.map fullInclusion.mapTotal
        (Cycle.map toFull.mapTotal ↑(C.boundary D.1)) = ↑(C.boundary D.1)
    refine Quotient.inductionOn' (C.boundary D.1).1 ?_
    intro l
    have hmap :
        fullInclusion.mapTotal ∘ toFull.mapTotal = id := by
      funext e
      cases e
      rfl
    have hmapList :
        List.map (fullInclusion.mapTotal ∘ toFull.mapTotal) l = l := by
      simpa using congrArg (fun f ↦ List.map f l) hmap
    apply Cycle.coe_eq_coe.2
    simpa [hmapList] using List.IsRotated.refl l

end TwoComplex

namespace GroupDiagram

/-- The basis word obtained by reading the labels of the oriented edges traversed by a based path,
expanding each label into its reduced word in the chosen basis. -/
def pathLabelWord (M : GroupDiagram F) (basis : FreeGroupBasis X F)
    {a b : M.source.skeleton} : Quiver.Path a b → List (X × Bool)
  | .nil => []
  | .cons p e => M.pathLabelWord basis p ++ (basis.repr (M.label e.1)).toWord

/-- The empty path reads as the empty basis word. -/
@[simp] theorem pathLabelWord_nil (M : GroupDiagram F) (basis : FreeGroupBasis X F)
    (a : M.source.skeleton) :
    M.pathLabelWord basis (nil : Quiver.Path a a) = [] :=
  rfl

/-- Appending one oriented edge appends the reduced word of its label. -/
@[simp] theorem pathLabelWord_cons (M : GroupDiagram F) (basis : FreeGroupBasis X F)
    {a b c : M.source.skeleton} (p : Quiver.Path a b) (e : b ⟶ c) :
    M.pathLabelWord basis (.cons p e) =
      M.pathLabelWord basis p ++ (basis.repr (M.label e.1)).toWord :=
  rfl

/-- Reading a path label through the chosen basis gives the free-group word obtained by
concatenating the reduced words of the successive edge labels. -/
-- Proof sketch: expand `GroupDiagram.pathLabel` as the ordered product of the path edge labels,
-- use that `basis.repr` is a multiplicative equivalence, and rewrite each factor by
-- `FreeGroup.mk_toWord`.
theorem repr_pathLabel (M : GroupDiagram F) (basis : FreeGroupBasis X F)
    {a b : M.source.skeleton} (p : Quiver.Path a b) :
    basis.repr (M.pathLabel p) = FreeGroup.mk (M.pathLabelWord basis p) :=
  by
    induction p with
    | nil =>
        simp [FreeGroup.one_eq_mk]
    | cons p e ih =>
        have hw :
            FreeGroup.mk ((basis.repr (M.label e.1)).toWord) = basis.repr (M.label e.1) :=
          FreeGroup.mk_toWord
        rw [M.pathLabel_cons p e, map_mul, ih, ← hw]
        simp [FreeGroup.mul_mk]

end GroupDiagram

/-- Definition 5-1-5: a diagram for the finite sequence `(c₁, ..., cₙ)` in the free group with
chosen basis `basis` is a group-labelled singular disc whose oriented edges have nontrivial
labels, whose chosen outer boundary loop reads the reduced product `c₁ ⋯ cₙ`, and whose
geometric regions admit an orientation whose boundary word is cyclically reduced and whose label
product is conjugate to one of the listed relators. -/
structure FreeGroupDiagram (basis : FreeGroupBasis X F) (relators : List F) extends GroupDiagram F where
  /-- A chosen outer boundary loop of the diagram, viewed in the full subcomplex of the
  underlying map. -/
  outerBoundary :
    let S := source.fullSubcomplex
    Loop S.skeleton.toOneComplex
  /-- The whole labelled map is a genuine singular disc with boundary given by the chosen outer
  boundary loop. -/
  singularDisc :
    let S := source.fullSubcomplex
    S.IsSingularDisc (cyclicPath outerBoundary)
  /-- Every oriented edge has nontrivial label. -/
  label_ne_one (e : source.skeleton.Edge) : label e ≠ 1
  /-- The outer boundary word is reduced without cancellation. -/
  outerBoundary_reduced :
    let S := source.fullSubcomplex
    let p := mapLoop S.skeleton.inclusion outerBoundary
    FreeGroup.IsReduced (toGroupDiagram.pathLabelWord basis p.2)
  /-- The outer boundary label product is exactly `c₁ ⋯ cₙ`. -/
  outerBoundary_product :
    let S := source.fullSubcomplex
    let p := mapLoop S.skeleton.inclusion outerBoundary
    toGroupDiagram.pathLabel p.2 = relators.prod
  /-- Every geometric region admits an oriented representative together with a based boundary path
  whose boundary word is cyclically reduced and whose label product is conjugate to one of the
  listed relators. -/
  regionBoundary_condition (D : TwoComplex.GeometricFace source) :
    ∃ E : source.Face, ⟦E⟧ = D ∧
      ∃ v : source.skeleton, ∃ q : source.BoundaryPath E v,
        FreeGroup.IsCyclicallyReduced (toGroupDiagram.pathLabelWord basis q.1) ∧
          ∃ i : Fin relators.length, IsConj (toGroupDiagram.pathLabel q.1) (relators.get i)

namespace FreeGroupDiagram

variable {basis : FreeGroupBasis X F} {relators : List F}

private theorem mapPath_edgeList_eq {C D : OneComplex} (f : OneComplex.Hom C D)
    {a b : C} (p : Quiver.Path a b) :
    (f.mapPath p).edgeList = List.map f.mapTotal p.edgeList := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      change (f.toPrefunctor.mapPath (p.cons e)).edgeList =
        List.map f.mapTotal (p.cons e).edgeList
      have ih' : (f.toPrefunctor.mapPath p).edgeList = List.map f.mapTotal p.edgeList := ih
      rw [Prefunctor.mapPath_cons, Quiver.Path.edgeList, Quiver.Path.edgeList,
        List.map_append, ih']
      rfl

private theorem inclusion_toFull_mapPath {C : TwoComplex} {a b : C.skeleton} (p : Quiver.Path a b) :
    C.fullOneSubcomplex.inclusion.toPrefunctor.mapPath (C.toFullOneSubcomplex.toPrefunctor.mapPath p) = p := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      rw [Prefunctor.mapPath_cons, Prefunctor.mapPath_cons]
      have hcons :=
        congrArg
          (fun q ↦ q.cons
            (C.fullOneSubcomplex.inclusion.toPrefunctor.map
              (C.toFullOneSubcomplex.toPrefunctor.map e))) ih
      simpa [TwoComplex.toFullOneSubcomplex, OneComplex.Subcomplex.inclusion,
        OneComplex.Hom.toPrefunctor, OneComplex.Hom.mapQuiverEdge] using hcons

private def complexInclusion {C : TwoComplex} (S : TwoComplex.Subcomplex C) :
    TwoComplex.Hom S.complex C where
  toVertex := S.skeleton.inclusion.toVertex
  toEdge := S.skeleton.inclusion.toEdge
  map_initial := S.skeleton.inclusion.map_initial
  map_terminal := S.skeleton.inclusion.map_terminal
  map_edgeInv := S.skeleton.inclusion.map_edgeInv
  mapFace D := D.1
  map_faceInv D := rfl
  mapBoundary {D} {v} q := by
    have h := (congrArg S.skeleton.inclusion.mapCyclicPath q.2).trans (S.boundary_eq D)
    refine ⟨S.skeleton.inclusion.mapPath q.1, ?_⟩
    have hm :
        cyclicPath ⟨S.skeleton.inclusion.toVertex v, S.skeleton.inclusion.mapPath q.1⟩ =
          S.skeleton.inclusion.mapCyclicPath (cyclicPath ⟨v, q.1⟩) := by
      apply Subtype.ext
      apply Cycle.coe_eq_coe.2
      simpa [mapPath_edgeList_eq] using
        List.IsRotated.refl (List.map S.skeleton.inclusion.mapTotal q.1.edgeList)
    exact hm.trans h

/-- The chosen boundary loop of a free-group diagram, viewed in the ambient labelled map. -/
abbrev outerBoundaryLoop (D : FreeGroupDiagram basis relators) : Loop D.source.skeleton :=
  let S := D.source.fullSubcomplex
  mapLoop S.skeleton.inclusion D.outerBoundary

/-- A free-group diagram is used via its underlying oriented `2`-complex. -/
instance : CoeOut (FreeGroupDiagram basis relators) TwoComplex where
  coe D := D.source

/-- The underlying `1`-skeleton of a free-group diagram is finite. -/
theorem finite_vertex (D : FreeGroupDiagram basis relators) : Finite D.source.skeleton := by
  classical
  let hsingular := D.singularDisc.toIsSingularSubcomplex
  exact
    Set.finite_univ_iff.mp <| by
      simpa [TwoComplex.fullSubcomplex, TwoComplex.fullOneSubcomplex] using
        hsingular.finite_vertexSet

/-- The underlying `1`-skeleton of a free-group diagram is finite. -/
instance (D : FreeGroupDiagram basis relators) : Finite D.source.skeleton :=
  D.finite_vertex

/-- The oriented edge set of a free-group diagram is finite. -/
theorem finite_edge (D : FreeGroupDiagram basis relators) :
    Finite (OneComplex.Edge D.source.skeleton) := by
  classical
  let hsingular := D.singularDisc.toIsSingularSubcomplex
  exact
    Set.finite_univ_iff.mp <| by
      simpa [TwoComplex.fullSubcomplex, TwoComplex.fullOneSubcomplex] using
        hsingular.finite_edgeSet

/-- The oriented edge set of a free-group diagram is finite. -/
instance (D : FreeGroupDiagram basis relators) : Finite (OneComplex.Edge D.source.skeleton) :=
  D.finite_edge

/-- The oriented face set of a free-group diagram is finite. -/
theorem finite_face (D : FreeGroupDiagram basis relators) : Finite (TwoComplex.Face D.source) := by
  classical
  let hsingular := D.singularDisc.toIsSingularSubcomplex
  exact
    Set.finite_univ_iff.mp <| by
      simpa [TwoComplex.fullSubcomplex] using
        hsingular.finite_faceSet

/-- The oriented face set of a free-group diagram is finite. -/
instance (D : FreeGroupDiagram basis relators) : Finite (TwoComplex.Face D.source) := D.finite_face

/-- The chosen outer boundary loop presents a simple boundary cycle. -/
theorem outerBoundary_simpleCycle (D : FreeGroupDiagram basis relators) :
    IsSimpleCycle (cyclicPath D.outerBoundary) :=
  D.singularDisc.simpleCycle

/-- The chosen outer boundary loop is cyclically reduced as a combinatorial boundary cycle. -/
theorem outerBoundary_cyclicallyReducedCycle (D : FreeGroupDiagram basis relators) :
    IsCyclicallyReducedCycle (cyclicPath D.outerBoundary) :=
  D.singularDisc.cyclicallyReducedCycle

theorem pathClass_eq_one (D : FreeGroupDiagram basis relators) {v : D.source.skeleton}
    (p : Quiver.Path v v) :
    (Quotient.mk'' p : End (⟨v⟩ : D.source.pi)) = (𝟙 (⟨v⟩ : D.source.pi)) := by
  let S := D.source.fullSubcomplex
  let φ : TwoComplex.Hom S.complex D.source := complexInclusion S
  let v' : S.complex.skeleton := ⟨v, by
    change v ∈ (Set.univ : Set D.source.skeleton)
    exact Set.mem_univ _⟩
  let p' : Quiver.Path v' v' := D.source.toFullOneSubcomplex.mapPath p
  haveI : TwoComplex.IsSimplyConnected S.complex := D.singularDisc.simplyConnected
  have hp' : (Quotient.mk'' p' : End (⟨v'⟩ : S.complex.pi)) =
      (𝟙 (⟨v'⟩ : S.complex.pi)) :=
    TwoComplex.fundamentalGroup_eq_one v' (Quotient.mk'' p')
  have hφ := congrArg (φ.inducedFundamentalGroupHom v') hp'
  have hmap : φ.inducedFundamentalGroupHom v' (Quotient.mk'' p') = Quotient.mk'' p := by
    change Quotient.map' φ.mapPath (fun _ _ h ↦ φ.mapPath_path_two_equiv h) (Quotient.mk'' p') =
      Quotient.mk'' p
    exact congrArg Quotient.mk'' (inclusion_toFull_mapPath p)
  have hid :
      φ.inducedFundamentalGroupHom v' (𝟙 (⟨v'⟩ : S.complex.pi)) =
        𝟙 (⟨v⟩ : D.source.pi) := by
    rfl
  exact hmap.symm.trans (hφ.trans hid)

/-- The underlying `1`-skeleton of a free-group diagram is connected. -/
theorem connected (D : FreeGroupDiagram basis relators) :
    Quiver.IsStronglyConnected (Quiver.Symmetrify D.source.skeleton) := by
  intro v w
  let S := D.source.fullSubcomplex
  let v' : S.complex.skeleton := ⟨v, by
    change v ∈ (Set.univ : Set D.source.skeleton)
    exact Set.mem_univ _⟩
  let w' : S.complex.skeleton := ⟨w, by
    change w ∈ (Set.univ : Set D.source.skeleton)
    exact Set.mem_univ _⟩
  rcases D.singularDisc.connected v' w' with ⟨p⟩
  exact ⟨S.skeleton.inclusion.toPrefunctor.symmetrify.mapPath p⟩

/-- The underlying oriented map of a free-group diagram is simply connected. -/
theorem simplyConnected (D : FreeGroupDiagram basis relators) :
    TwoComplex.IsSimplyConnected D := by
  refine ⟨?_⟩
  intro v
  refine ⟨?_⟩
  intro g h
  refine Quotient.inductionOn₂ g h ?_
  intro p q
  exact (FreeGroupDiagram.pathClass_eq_one D p).trans
    (FreeGroupDiagram.pathClass_eq_one D q).symm

/-- The underlying oriented map of a free-group diagram is simply connected. -/
instance (D : FreeGroupDiagram basis relators) :
    TwoComplex.IsSimplyConnected D :=
  D.simplyConnected

end FreeGroupDiagram

end
