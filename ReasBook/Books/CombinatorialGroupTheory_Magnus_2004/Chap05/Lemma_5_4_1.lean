/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Definition_3_2_4
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_4_2
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_3_1

-- Declarations for this item will be appended below by the statement pipeline.

set_option autoImplicit false

noncomputable section

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: simple boundary cycles for regions in simply connected planar small-cancellation
maps.

Layer triage:
- `source-facing`: Lemma `5-4-1`, which asserts that every region of a simply connected `(q, p)`
  map satisfying the stated region-degree hypothesis has simple boundary.
- `core/canonical`: `TwoComplex.TwoManifoldEmbedding C 𝔼²` with
  `TwoComplex.TwoManifoldEmbedding.IsPlanarMap` is the owner for the planar map,
  `TwoComplex.IsSimplyConnected` is the owner for simply connectedness,
  `TwoComplex.TwoManifoldEmbedding.IsRoundBracketPQMap` is the owner for the `(q, p)` condition,
  and `TwoComplex.HasSimpleBoundary` is the owner predicate expressing that a face boundary is a
  simple closed path.
- `bridge/view`: the source condition that `∂D` contains no edge of `∂M` is the inclusion
  `C.boundaryGeometricEdges D ⊆ {e | embedding.IsInteriorEdge e}` built from
  `TwoComplex.boundaryGeometricEdges D` and `TwoComplex.TwoManifoldEmbedding.IsInteriorEdge`.

Domain sampling:
1. `TwoComplex.TwoManifoldEmbedding.IsRoundBracketPQMap` from Definition `5-3-1` is the chapter owner
   for the source `(q, p)` hypothesis.
2. `TwoComplex.boundaryGeometricEdges` from Definition `5-1-1` is the owner API for the
   geometric edges occurring in a region boundary.
3. `TwoComplex.TwoManifoldEmbedding.IsInteriorEdge` from Definition `5-2-7` is the owner
   predicate for the ambient-map interior edges used in the source hypothesis that a region
   boundary contains no boundary edge of the ambient map.
4. `TwoComplex.HasSimpleBoundary` from Definition `3-2-4` is the owner predicate matching the
   conclusion that a region boundary is a simple closed path.

Primitive vs. derived:
- primitive public data: the planar embedding `embedding`, the simply connectedness hypothesis,
  the `(q, p)` hypothesis, the explicit classification of `(q, p)`, and the extra degree bound on
  regions whose boundaries contain no boundary edge of `M`;
- derived API: the conclusion that every oriented face, hence every region, has simple boundary.
-/

namespace TwoComplex

namespace TwoManifoldEmbedding

section

variable {C : TwoComplex}

-- Proof sketch: argue by contradiction using a minimal submap cut off by a non-simple boundary
-- loop in the boundary of `D`. That submap inherits simple connectedness, all of its vertices
-- except possibly one boundary vertex have degree at least `q`, and every region in it has degree
-- at least `p` by the no-boundary-edge hypothesis. Corollary `3.3` then gives a curvature
-- inequality contradicting `(q, p) ∈ {(3, 6), (4, 4), (6, 3)}`.
/-- Lemma 5-4-1: in a simply connected `(q, p)` map with `(q, p)` equal to `(3, 6)`, `(4, 4)`,
or `(6, 3)`, if every region whose boundary contains no boundary edge of the ambient map has
degree at least `p`, then every oriented face, equivalently every region, has simple boundary. -/
theorem face_hasSimpleBoundary_of_simplyConnected_roundBracketQPMap
    (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap] [TwoComplex.IsSimplyConnected C]
    (q p : ℕ) (hQP : embedding Is(q, p))
    (hPair : (q, p) = (3, 6) ∨ (q, p) = (4, 4) ∨ (q, p) = (6, 3))
    (hRegionDegree :
      ∀ D : GeometricFace C,
        C.boundaryGeometricEdges D ⊆ {e | embedding.IsInteriorEdge e} →
          p ≤ C.regionDegree D)
    (D : C.Face) :
    C.HasSimpleBoundary D := sorry

end

end TwoManifoldEmbedding
end TwoComplex
