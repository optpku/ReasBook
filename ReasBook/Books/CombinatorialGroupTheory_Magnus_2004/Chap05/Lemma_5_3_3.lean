/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_2_7
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_2_8

-- Declarations for this item will be appended below by the statement pipeline.

set_option autoImplicit false

noncomputable section

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: basic combinatorial inequalities for interior cells of a planar map.

Layer triage:
- `source-facing`: the inequality comparing the numbers of interior vertices and interior edges
  under the hypothesis that each interior vertex has degree at least `2`.
- `core/canonical`: `TwoComplex.TwoManifoldEmbedding.IsInteriorVertex` and
  `TwoComplex.TwoManifoldEmbedding.IsInteriorEdge` from Definition `5-2-7` are the owner predicates
  for interior cells, while `OneComplex.vertexDegree` from Definition `5-2-8`
  is the owner for vertex degree.
- `bridge/view`: the interior-cell counts are realized as finite-cardinality counts of the
  subtypes of interior vertices and interior geometric edges of the chosen planar embedding.

Domain sampling:
1. `TwoComplex.TwoManifoldEmbedding.IsInteriorVertex` is the chapter owner for interior vertices.
2. `TwoComplex.TwoManifoldEmbedding.IsInteriorEdge` is the chapter owner for interior
   geometric edges.
3. `OneComplex.vertexDegree` is the canonical degree attached to a vertex of a
   finite planar map.
4. `Nat.card` is the canonical finite-cardinality owner for counting subtype-defined finite sets.

Primitive vs. derived:
- primitive public data: a planar embedding `embedding : TwoComplex.TwoManifoldEmbedding C 𝔼²`;
- derived API: the interior-vertex and interior-edge counts are best expressed directly as
  `Nat.card` of the corresponding interior subtypes, while the hypothesis is the direct owner-side
  lower bound `2 ≤ C.skeleton.vertexDegree v` on each interior vertex.
-/

namespace TwoComplex
namespace TwoManifoldEmbedding

section

open OneComplex

variable {C : TwoComplex}
variable (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap]

-- Proof sketch: sum the degrees of the interior vertices. The hypothesis gives a lower bound `2`
-- on each summand, while each interior geometric edge contributes at most two incident interior
-- endpoints, yielding twice the interior-vertex count `≤` twice the interior-edge count and hence
-- the desired inequality.
/-- Lemma 5-3-3: if every interior vertex of a planar map has degree at least `2`, then the
number of interior vertices is at most the number of interior edges. -/
theorem interiorVertexCount_le_interiorEdgeCount_of_interiorVertexDegree_ge_two
    (hdegree : embedding.HasInteriorVertexDegreeAtLeast 2) :
    Nat.card { v : C.skeleton // embedding.IsInteriorVertex v } ≤
      Nat.card { e : GeometricEdge C.skeleton // embedding.IsInteriorEdge e } := sorry

end

end TwoManifoldEmbedding
end TwoComplex
