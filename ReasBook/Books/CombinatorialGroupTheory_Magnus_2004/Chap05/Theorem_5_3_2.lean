/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_2_8

-- Declarations for this item will be appended below by the statement pipeline.

set_option autoImplicit false

noncomputable section

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: Euler-characteristic and degree-counting formulas for finite planar maps.

Layer triage:
- `source-facing`: a finite planar map together with positive integers `p` and `q` satisfying
  `1 / p + 1 / q = 1 / 2`, and the degree sums over boundary vertices, interior vertices, and
  regions that appear in the basic formulas of Section `5.3`.
- `core/canonical`: `TwoComplex.TwoManifoldEmbedding C 𝔼²` together with
  `TwoComplex.TwoManifoldEmbedding.IsPlanarMap` is the owner for a planar map,
  `TwoComplex.TwoManifoldEmbedding.IsBoundaryVertex` / `IsInteriorVertex` and
  `IsBoundaryEdge` are the owner predicates for the boundary/interior decomposition, and
  `OneComplex.vertexDegree` / `TwoComplex.regionDegree` / `boundaryInteriorEdgeCount`
  are the owner degree-counting functions.
- `bridge/view`: the textbook counts `V`, `E`, `F`, `V^•`, `E^•`, and the degree-defect sums are
  realized here as cardinalities and finite sums built from those owner predicates and degree
  functions.

Domain sampling:
1. `TwoComplex.TwoManifoldEmbedding C 𝔼²` from Definition `5-1-1` is the established owner for the
   planar realization of a map.
2. `TwoComplex.TwoManifoldEmbedding.IsPlanarMap` is the owner hypothesis supplying finiteness of the
   vertex, edge, and face types.
3. `TwoComplex.TwoManifoldEmbedding.IsBoundaryVertex`, `IsInteriorVertex`, and `IsBoundaryEdge` from
   Definition `5-2-7` are the owner predicates for the boundary/interior language used in the
   formulas.
4. `OneComplex.vertexDegree`, `TwoComplex.regionDegree`, and
   `TwoComplex.TwoManifoldEmbedding.boundaryInteriorEdgeCount` from Definition `5-2-8`
   are the owner degree-counting maps whose total sums enter the theorem and its later
   boundary-region corollaries.
5. `positive_integral_reciprocal_sum_eq_half_iff` from Definition `5-3-1` is the chapter owner
   for the positive-integral reciprocal relation, so the source-facing theorem should keep
   explicit positivity on both parameters rather than relying on totalized division in `ℚ`.

Primitive vs. derived:
- primitive public data: a finite planar map `embedding` together with positive integers `p` and
  `q` satisfying `1 / p + 1 / q = 1 / 2`;
- derived API: the rationalized counts `V`, `E`, `F`, `V^•`, `E^•`, the Euler term `V - E + F`,
  the four defect sums used to state the two formulas in `ℚ`, and the selected-region
  curvature sum used later for boundary-region curvature estimates.
-/

namespace TwoComplex
namespace TwoManifoldEmbedding

section

open OneComplex

variable {C : TwoComplex}

/-- The number `V` of vertices of a finite planar map, viewed in `ℚ`. -/
abbrev vertexCount (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap] : ℚ :=
  Nat.card C.skeleton

/-- The number `E` of geometric edges of a finite planar map, viewed in `ℚ`. -/
abbrev edgeCount (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap] : ℚ :=
  Nat.card (OneComplex.GeometricEdge C.skeleton)

/-- The number `F` of geometric regions of a finite planar map, viewed in `ℚ`. -/
abbrev regionCount (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap] : ℚ :=
  Nat.card (GeometricFace C)

/-- The number `V^•` of boundary vertices of a finite planar map, viewed in `ℚ`. -/
abbrev boundaryVertexCount (embedding : TwoManifoldEmbedding C 𝔼²)
    [embedding.IsPlanarMap] : ℚ :=
  Nat.card { v : C.skeleton // embedding.IsBoundaryVertex v }

/-- The number `E^•` of boundary edges of a finite planar map, viewed in `ℚ`. -/
abbrev boundaryEdgeCount (embedding : TwoManifoldEmbedding C 𝔼²)
    [embedding.IsPlanarMap] : ℚ :=
  Nat.card { e : OneComplex.GeometricEdge C.skeleton // embedding.IsBoundaryEdge e }

/-- The boundary-vertex defect sum `∑^• [p - d(v)]`. -/
abbrev boundaryVertexDefectSum (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap]
    (p : ℚ) : ℚ :=
  let _ : Finite C.skeleton := (inferInstance : embedding.IsPlanarMap).finite_vertex
  let _ : Finite C.skeleton.Edge := finite_orientedEdge embedding
  let _ : Fintype { v : C.skeleton // embedding.IsBoundaryVertex v } := Fintype.ofFinite _
  ∑ v : { v : C.skeleton // embedding.IsBoundaryVertex v }, (p - (C.skeleton.vertexDegree v : ℚ))

/-- The interior-vertex defect sum `∑^∘ [p - d(v)]`. -/
abbrev interiorVertexDefectSum (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap]
    (p : ℚ) : ℚ :=
  let _ : Finite C.skeleton := (inferInstance : embedding.IsPlanarMap).finite_vertex
  let _ : Finite C.skeleton.Edge := finite_orientedEdge embedding
  let _ : Fintype { v : C.skeleton // embedding.IsInteriorVertex v } := Fintype.ofFinite _
  ∑ v : { v : C.skeleton // embedding.IsInteriorVertex v }, (p - (C.skeleton.vertexDegree v : ℚ))

/-- The region-degree defect sum `∑ [q - d(D)]`. -/
abbrev regionDegreeDefectSum (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap]
    (q : ℚ) : ℚ :=
  let _ : Finite (GeometricFace C) := (inferInstance : embedding.IsPlanarMap).finite_face
  let _ : Fintype (GeometricFace C) := Fintype.ofFinite (GeometricFace C)
  ∑ D : GeometricFace C, (q - (C.regionDegree D : ℚ))

/-- The adjusted boundary-vertex defect sum `∑^• [p / q + 2 - d(v)]` from formula `(3.2)`. -/
abbrev boundaryVertexAdjustedDefectSum (embedding : TwoManifoldEmbedding C 𝔼²)
    [embedding.IsPlanarMap] (p q : ℚ) : ℚ :=
  let _ : Finite C.skeleton := (inferInstance : embedding.IsPlanarMap).finite_vertex
  let _ : Finite C.skeleton.Edge := finite_orientedEdge embedding
  let _ : Fintype { v : C.skeleton // embedding.IsBoundaryVertex v } := Fintype.ofFinite _
  ∑ v : { v : C.skeleton // embedding.IsBoundaryVertex v },
    (p / q + 2 - (C.skeleton.vertexDegree v : ℚ))

/-- The curvature sum `∑ [p / q + 2 - i(D)]` attached to a selected family of regions in a planar
map. -/
abbrev adjustedInteriorEdgeDefectSum
    (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap]
    (P : GeometricFace C → Prop) (p q : ℚ) : ℚ :=
  let _ : Finite (GeometricFace C) := (inferInstance : embedding.IsPlanarMap).finite_face
  let _ : Fintype { D : GeometricFace C // P D } := Fintype.ofFinite _
  let _ : DecidableEq { D : GeometricFace C // P D } := Classical.decEq _
  ∑ D : { D : GeometricFace C // P D },
    (p / q + 2 - (embedding.boundaryInteriorEdgeCount D : ℚ))

-- Proof sketch: expand the canonical Euler term `V - E + F`, use the standard degree-counting
-- identities `2E = ∑ d(v)` and `2E = ∑ d(D) + E^•`, rewrite `V` and `F` as sums of constant
-- terms over vertices and regions, and use `1 / p + 1 / q = 1 / 2` for positive integers `p`
-- and `q` to cancel the remaining edge contribution. Then split the vertex sum into boundary and
-- interior parts, and finally separate the constant `p / q` over the boundary vertices to obtain
-- formula `(3.2)`.
variable (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap]

/-- Theorem 5-3-2: for a finite planar map, the two basic curvature formulas are the identities
obtained by expanding the canonical Euler term `V - E + F` for positive integers `p` and `q`
satisfying `1 / p + 1 / q = 1 / 2`. -/
theorem basic_formulas_of_planar_map
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hReciprocal : (1 : ℚ) / p + 1 / q = (1 : ℚ) / 2) :
    (p : ℚ) * (embedding.vertexCount - embedding.edgeCount + embedding.regionCount) =
        embedding.boundaryVertexDefectSum p + embedding.interiorVertexDefectSum p +
          ((p : ℚ) / q) * embedding.regionDegreeDefectSum q -
            ((p : ℚ) / q) * embedding.boundaryEdgeCount ∧
      (p : ℚ) * (embedding.vertexCount - embedding.edgeCount + embedding.regionCount) =
        embedding.boundaryVertexAdjustedDefectSum p q + embedding.interiorVertexDefectSum p +
          ((p : ℚ) / q) * embedding.regionDegreeDefectSum q +
            ((p : ℚ) / q) * (embedding.boundaryVertexCount - embedding.boundaryEdgeCount) := by
  sorry

/-- Formula `(3.1)` from `basic_formulas_of_planar_map`. -/
theorem basic_formula_3_1_of_planar_map
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hReciprocal : (1 : ℚ) / p + 1 / q = (1 : ℚ) / 2) :
    (p : ℚ) * (embedding.vertexCount - embedding.edgeCount + embedding.regionCount) =
      embedding.boundaryVertexDefectSum p + embedding.interiorVertexDefectSum p +
        ((p : ℚ) / q) * embedding.regionDegreeDefectSum q -
          ((p : ℚ) / q) * embedding.boundaryEdgeCount :=
  (basic_formulas_of_planar_map embedding p q hp hq hReciprocal).1

/-- Formula `(3.2)` from `basic_formulas_of_planar_map`. -/
theorem basic_formula_3_2_of_planar_map
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (hReciprocal : (1 : ℚ) / p + 1 / q = (1 : ℚ) / 2) :
    (p : ℚ) * (embedding.vertexCount - embedding.edgeCount + embedding.regionCount) =
      embedding.boundaryVertexAdjustedDefectSum p q + embedding.interiorVertexDefectSum p +
        ((p : ℚ) / q) * embedding.regionDegreeDefectSum q +
          ((p : ℚ) / q) * (embedding.boundaryVertexCount - embedding.boundaryEdgeCount) :=
  (basic_formulas_of_planar_map embedding p q hp hq hReciprocal).2

end

end TwoManifoldEmbedding
end TwoComplex
