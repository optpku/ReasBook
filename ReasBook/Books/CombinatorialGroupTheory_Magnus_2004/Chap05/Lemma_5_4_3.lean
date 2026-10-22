/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_4_2
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_2_8

set_option autoImplicit false

noncomputable section

open Quiver.Path

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: simple closed boundaries and extremal discs of planar maps.

Layer triage:
- `source-facing`: Lemma `5-4-3`, which concludes the existence of two extremal discs from the
  failure of the whole-boundary simple-cycle condition on the whole map.
- `core/canonical`: `TwoComplex.TwoManifoldEmbedding.HasSimpleBoundary` from Definition `5-4-2`
  is the chapter owner for the actual boundary of a planar map being carried by one simple ambient
  boundary cycle.
- `bridge/view`: `TwoComplex.TwoManifoldEmbedding.IsBoundaryCycle` remains the chosen-cycle API
  used to witness map-level simple boundary and to state extremality of subdiscs.

Domain sampling:
1. `TwoComplex.TwoManifoldEmbedding.IsBoundaryCycle` from Definition `5-4-2` is the owner
   predicate for an individual simple ambient boundary cycle.
2. `TwoComplex.TwoManifoldEmbedding.HasSimpleBoundary` from Definition `5-4-2` is the owner
   predicate for the whole boundary of the map being one simple closed path.
3. `TwoComplex.TwoManifoldEmbedding.IsExtremalDisk` from Definition `5-4-2` is the owner
   predicate in the conclusion.
4. `TwoComplex.TwoManifoldEmbedding.IsBoundaryEdge` from Definition `5-2-7` is the canonical
   boundary-edge API used to tie a chosen boundary cycle to the actual ambient boundary.

Primitive vs. derived:
- primitive public data: the planar embedding, connectedness and simple-connectedness
  hypotheses, the no-degree-one assumption, and the canonical whole-boundary hypothesis
  `TwoManifoldEmbedding.HasSimpleBoundary embedding`;
- derived API: particular ambient boundary cycles witnessing `embedding.IsBoundaryCycle c` inside
  the owner `TwoManifoldEmbedding.HasSimpleBoundary embedding` and inside
  `embedding.IsExtremalDisk`.
-/

namespace TwoComplex
namespace TwoManifoldEmbedding

section

variable {C : TwoComplex}

-- Proof sketch: induct on the number of regions. Choose a shortest closed subpath of a boundary
-- cycle of `M`; the degree-one hypothesis makes this subpath simple, so it bounds an extremal
-- singular-disc submap. Delete the vertices of degree one from the complementary submap and
-- apply the induction hypothesis there; either the complement is itself extremal or it contains
-- another extremal disk that remains extremal in the ambient map, yielding an injective
-- `Fin 2`-indexed family of extremal disks.
/-- Lemma 5-4-3: if a connected simply connected planar map has no vertices of degree `1` and its
boundary is not a simple closed path, then the map
contains at least two distinct extremal disks. -/
theorem exists_two_extremalDisks_of_not_boundary_simpleClosedPath
    (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap]
    (hconnected : Quiver.IsStronglyConnected (Quiver.Symmetrify C.skeleton))
    [TwoComplex.IsSimplyConnected C]
    (hnoDegreeOne :
      let _ : Finite C.skeleton.Edge := finite_orientedEdge embedding
      ∀ v : C.skeleton, C.skeleton.vertexDegree v ≠ 1)
    (hboundary : ¬ TwoManifoldEmbedding.HasSimpleBoundary embedding) :
    ∃ disks : Fin 2 → Subcomplex C,
      Function.Injective disks ∧ ∀ i : Fin 2, embedding.IsExtremalDisk (disks i) := sorry

end

end TwoManifoldEmbedding
end TwoComplex
