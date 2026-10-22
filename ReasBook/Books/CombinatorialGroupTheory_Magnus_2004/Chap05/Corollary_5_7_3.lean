/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_3_5
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_7_1
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_6_2

-- Declarations for this item will be appended below by the statement pipeline.

set_option autoImplicit false

noncomputable section

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: duality of planar maps after removing boundary layers.

Layer triage:
- `source-facing`: a map `M`, a dual map `M*`, and the maps `M₁`, `M₁*` obtained by deleting the
  boundary layers of `M` and `M*`.
- `core/canonical`: `TwoComplex.Duality` is the project owner for the underlying duality data
  between the carried `2`-complexes, while the predicates
  `TwoManifoldEmbedding.IsInteriorVertex`, `TwoManifoldEmbedding.IsInteriorRegion`, and the
  boundary-layer edge owner `TwoManifoldEmbedding.IsBoundaryLayerEdge` describe the cells that
  survive or are deleted.
- `bridge/view`: `TwoComplex.Subcomplex.IsBoundaryLayerComplement` is the chapter bridge saying
  which carried subcomplex remains after deleting the boundary layer, and
  `TwoManifoldEmbedding.restrictToSubcomplex` is the canonical induced planar embedding on that
  carried deleted map.

Domain sampling:
1. `TwoComplex.Duality` from `Proposition_3_7_1` is the existing owner abstraction for the
   underlying vertex-face-edge duality between two `2`-complexes.
2. `TwoManifoldEmbedding.IsInteriorVertex` and `TwoManifoldEmbedding.IsInteriorRegion` from
   `Definition_5_2_7` are the existing owner predicates for the surviving vertices and regions.
3. `TwoManifoldEmbedding.IsBoundaryLayerEdge` from `Definition_5_6_2` is the existing chapter
   owner predicate for the deleted geometric edges.
4. `TwoManifoldEmbedding.restrictToSubcomplex` from `Definition_5_1_1` is the canonical bridge
   from a carried subcomplex to the induced deleted planar map.

Primitive vs. derived:
- primitive public data: two planar embeddings, an explicit dual-map witness carrying the ambient
  `TwoComplex.Duality`, and explicit carried subcomplexes `S`, `SStar` with the two complement
  hypotheses;
- derived API: the statement that the ambient duality restricts to the carried deleted maps left
  after removing those boundary layers.
-/

namespace TwoComplex

private def equivSubtype
    {α β : Type*} (e : α ≃ β) (p : α → Prop) (q : β → Prop)
    (h : ∀ a, p a ↔ q (e a)) :
    {a // p a} ≃ {b // q b} where
  toFun a := ⟨e a.1, (h a.1).1 a.2⟩
  invFun b := ⟨e.symm b.1, by
    have : q (e (e.symm b.1)) := by simpa using b.2
    exact (h (e.symm b.1)).2 this⟩
  left_inv a := by
    ext
    exact e.symm_apply_apply a.1
  right_inv b := by
    ext
    exact e.apply_symm_apply b.1

namespace Subcomplex

section

variable {C : TwoComplex}

/-- A chosen carried subcomplex is a complement of the boundary layer when its carried vertices,
geometric edges, and geometric faces are exactly the interior vertices, the geometric edges not
in the boundary layer, and the interior regions of the ambient planar map. -/
def IsBoundaryLayerComplement (S : Subcomplex C) (embedding : TwoManifoldEmbedding C 𝔼²) : Prop :=
  (∀ v : C.skeleton, v ∈ S.skeleton.vertexSet ↔ embedding.IsInteriorVertex v) ∧
    (∀ e : OneComplex.GeometricEdge C.skeleton,
      S.skeleton.ContainsGeometricEdge e ↔ ¬ embedding.IsBoundaryLayerEdge e) ∧
      (∀ D : GeometricFace C, S.ContainsGeometricFace D ↔ embedding.IsInteriorRegion D)

namespace IsBoundaryLayerComplement

theorem mem_vertexSet_iff
    {S : Subcomplex C} {embedding : TwoManifoldEmbedding C 𝔼²}
    (hS : S.IsBoundaryLayerComplement embedding) (v : C.skeleton) :
    v ∈ S.skeleton.vertexSet ↔ embedding.IsInteriorVertex v := by
  rcases hS with ⟨hvertex, _, _⟩
  exact hvertex v

theorem mem_edgeSet_iff
    {S : Subcomplex C} {embedding : TwoManifoldEmbedding C 𝔼²}
    (hS : S.IsBoundaryLayerComplement embedding) (e : C.skeleton.Edge) :
    e ∈ S.skeleton.edgeSet ↔ ¬ embedding.IsBoundaryLayerEdge ⟦e⟧ := by
  rcases hS with ⟨_, hedge, _⟩
  simpa using hedge (⟦e⟧ : OneComplex.GeometricEdge C.skeleton)

theorem mem_faceSet_iff
    {S : Subcomplex C} {embedding : TwoManifoldEmbedding C 𝔼²}
    (hS : S.IsBoundaryLayerComplement embedding) (D : C.Face) :
    D ∈ S.faceSet ↔ embedding.IsInteriorRegion (⟦D⟧ : GeometricFace C) := by
  rcases hS with ⟨_, _, hface⟩
  simpa using hface (⟦D⟧ : GeometricFace C)

theorem mem_geometricEdge_iff
    {S : Subcomplex C} {embedding : TwoManifoldEmbedding C 𝔼²}
    (hS : S.IsBoundaryLayerComplement embedding)
    (e : OneComplex.GeometricEdge C.skeleton) :
    S.skeleton.ContainsGeometricEdge e ↔ ¬ embedding.IsBoundaryLayerEdge e := by
  rcases hS with ⟨_, hedge, _⟩
  exact hedge e

theorem mem_geometricFace_iff
    {S : Subcomplex C} {embedding : TwoManifoldEmbedding C 𝔼²}
    (hS : S.IsBoundaryLayerComplement embedding) (D : GeometricFace C) :
    S.ContainsGeometricFace D ↔ embedding.IsInteriorRegion D := by
  rcases hS with ⟨_, _, hface⟩
  exact hface D

end IsBoundaryLayerComplement

private noncomputable def ambientGeometricFaceEquiv (S : Subcomplex C) :
    GeometricFace S.complex ≃ {D : GeometricFace C // S.ContainsGeometricFace D} where
  toFun :=
    Quotient.lift
      (fun D : S.complex.Face ↦
        ⟨(⟦D.1⟧ : GeometricFace C), by
          exact (S.containsGeometricFace_mk_iff D.1).2 D.2⟩)
      (fun D E h ↦ by
        apply Subtype.ext
        apply Quotient.sound
        rcases h with h | h
        · left
          exact congrArg Subtype.val h
        · right
          simpa using congrArg Subtype.val h)
  invFun D := by
    let E : C.Face := Quotient.out D.1
    have hE : S.ContainsGeometricFace (⟦E⟧ : GeometricFace C) := by
      simpa [E] using D.2
    exact ⟦⟨E, (S.containsGeometricFace_mk_iff E).1 hE⟩⟧
  left_inv := by
    sorry
  right_inv := by
    sorry

private noncomputable def ambientGeometricEdgeEquiv (S : Subcomplex C) :
    OneComplex.GeometricEdge S.complex.skeleton ≃
      {e : OneComplex.GeometricEdge C.skeleton // S.skeleton.ContainsGeometricEdge e} where
  toFun :=
    Quotient.lift
      (fun e ↦
        ⟨(⟦e.1⟧ : OneComplex.GeometricEdge C.skeleton), by
          exact (S.skeleton.containsGeometricEdge_mk_iff e.1).2 e.2⟩)
      (fun e f h ↦ by
        apply Subtype.ext
        apply Quotient.sound
        rcases h with h | h
        · left
          exact congrArg Subtype.val h
        · right
          simpa using congrArg Subtype.val h)
  invFun e := by
    let f : C.skeleton.Edge := Quotient.out e.1
    have hf : S.skeleton.ContainsGeometricEdge (⟦f⟧ : OneComplex.GeometricEdge C.skeleton) := by
      simpa [f] using e.2
    exact ⟦⟨f, (S.skeleton.containsGeometricEdge_mk_iff f).1 hf⟩⟧
  left_inv := by
    sorry
  right_inv := by
    sorry

end

end Subcomplex

namespace TwoManifoldEmbedding

section

variable {C K : TwoComplex}

/-- A planar map `dualEmbedding` is a dual of `embedding` when it comes equipped with a
`TwoComplex.Duality` whose vertex-face, face-vertex, and edge correspondences exchange the two
boundary layers. -/
structure IsDualMap
    (embedding : TwoManifoldEmbedding C 𝔼²) (dualEmbedding : TwoManifoldEmbedding K 𝔼²) where
  /-- The underlying duality between the carried `2`-complexes. -/
  duality : TwoComplex.Duality C K
  /-- Boundary vertices correspond to boundary regions under the duality. -/
  vertex_boundary_iff (v : C.skeleton) :
      embedding.IsBoundaryVertex v ↔
        dualEmbedding.IsBoundaryRegion (duality.vertexToFace v)
  /-- Boundary regions correspond to boundary vertices under the duality. -/
  region_boundary_iff (D : GeometricFace C) :
      embedding.IsBoundaryRegion D ↔
        dualEmbedding.IsBoundaryVertex (duality.faceToVertex D)
  /-- Boundary-layer edges correspond to boundary-layer edges under the duality. -/
  edge_boundary_iff (e : OneComplex.GeometricEdge C.skeleton) :
      embedding.IsBoundaryLayerEdge e ↔
        dualEmbedding.IsBoundaryLayerEdge (duality.edgeToEdge e)

namespace IsDualMap

theorem interiorVertex_iff
    {embedding : TwoManifoldEmbedding C 𝔼²} {dualEmbedding : TwoManifoldEmbedding K 𝔼²}
    (hdual : embedding.IsDualMap dualEmbedding) (v : C.skeleton) :
    embedding.IsInteriorVertex v ↔
      dualEmbedding.IsInteriorRegion (hdual.duality.vertexToFace v) := by
  simpa [IsInteriorVertex, IsInteriorRegion] using
    not_congr (hdual.vertex_boundary_iff v)

theorem interiorRegion_iff
    {embedding : TwoManifoldEmbedding C 𝔼²} {dualEmbedding : TwoManifoldEmbedding K 𝔼²}
    (hdual : embedding.IsDualMap dualEmbedding) (D : GeometricFace C) :
    embedding.IsInteriorRegion D ↔
      dualEmbedding.IsInteriorVertex (hdual.duality.faceToVertex D) := by
  simpa [IsInteriorRegion, IsInteriorVertex] using
    not_congr (hdual.region_boundary_iff D)

theorem not_isBoundaryLayerEdge_iff
    {embedding : TwoManifoldEmbedding C 𝔼²} {dualEmbedding : TwoManifoldEmbedding K 𝔼²}
    (hdual : embedding.IsDualMap dualEmbedding)
    (e : OneComplex.GeometricEdge C.skeleton) :
    ¬ embedding.IsBoundaryLayerEdge e ↔
      ¬ dualEmbedding.IsBoundaryLayerEdge (hdual.duality.edgeToEdge e) := by
  simpa using not_congr (hdual.edge_boundary_iff e)

end IsDualMap

-- Proof sketch: restrict the ambient duality carried by `hdual` to the surviving vertices,
-- geometric edges, and geometric faces singled out by the carried boundary-layer complements. The
-- boundary-layer correspondence in `hdual` identifies those surviving cells on the two sides, and
-- the incidence-compatibility axiom of the ambient duality descends to the carried deleted maps.
/-- Corollary 5-7-3: if `embedding` is a map, `dualEmbedding` is a dual of it, and `S`, `SStar`
are the carried complements of the boundary layers of `embedding` and `dualEmbedding`, then the
induced deleted maps on `S` and `SStar` are themselves dual. The restricted ambient
`TwoComplex.Duality` is the underlying field of this source-facing dual-map witness. -/
def boundaryLayerRemoval_preservesDuality
    (embedding : TwoManifoldEmbedding C 𝔼²) (dualEmbedding : TwoManifoldEmbedding K 𝔼²)
    (hdual : embedding.IsDualMap dualEmbedding)
    (S : Subcomplex C) (hS : S.IsBoundaryLayerComplement embedding)
    (SStar : Subcomplex K) (hSStar : SStar.IsBoundaryLayerComplement dualEmbedding)
    : (embedding.restrictToSubcomplex S).IsDualMap
        (dualEmbedding.restrictToSubcomplex SStar) :=
  let Γ := S.skeleton
  let ΓStar := SStar.skeleton
  let faceEquiv := S.ambientGeometricFaceEquiv
  let faceEquivStar := SStar.ambientGeometricFaceEquiv
  let edgeEquiv := S.ambientGeometricEdgeEquiv
  let edgeEquivStar := SStar.ambientGeometricEdgeEquiv
  let restrictedDuality : TwoComplex.Duality S.complex SStar.complex :=
    { vertexToFace :=
        (equivSubtype hdual.duality.vertexToFace
          (fun v ↦ v ∈ Γ.vertexSet)
          (fun D ↦ SStar.ContainsGeometricFace D)
          fun v ↦ by
            simpa [Γ] using
              (hS.mem_vertexSet_iff v).trans
                ((hdual.interiorVertex_iff v).trans
                  (hSStar.mem_geometricFace_iff (hdual.duality.vertexToFace v)).symm)).trans
          faceEquivStar.symm
      faceToVertex :=
        faceEquiv.trans <|
          equivSubtype hdual.duality.faceToVertex
            (fun D ↦ S.ContainsGeometricFace D)
            (fun v ↦ v ∈ ΓStar.vertexSet)
            fun D ↦ by
              simpa [ΓStar] using
                (hS.mem_geometricFace_iff D).trans
                  ((hdual.interiorRegion_iff D).trans
                    (hSStar.mem_vertexSet_iff (hdual.duality.faceToVertex D)).symm)
      edgeToEdge :=
        edgeEquiv.trans <|
          (equivSubtype hdual.duality.edgeToEdge
            (fun e ↦ Γ.ContainsGeometricEdge e)
            (fun e ↦ ΓStar.ContainsGeometricEdge e)
            fun e ↦ by
              simpa [Γ, ΓStar] using
                (hS.mem_geometricEdge_iff e).trans
                  ((hdual.not_isBoundaryLayerEdge_iff e).trans
                    (hSStar.mem_geometricEdge_iff (hdual.duality.edgeToEdge e)).symm)).trans
            edgeEquivStar.symm
      vertexOnFace_iff := by
        sorry }
  { duality := restrictedDuality
    vertex_boundary_iff := by
      sorry
    region_boundary_iff := by
      sorry
    edge_boundary_iff := by
      sorry }

end

end TwoManifoldEmbedding
end TwoComplex
