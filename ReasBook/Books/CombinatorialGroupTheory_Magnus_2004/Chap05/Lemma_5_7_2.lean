/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap05.Corollary_5_7_3

-- Declarations for this item will be appended below by the statement pipeline.

set_option autoImplicit false

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: duality of planar maps after deleting boundary layers.

Layer triage:
- `source-facing`: a planar map `embedding`, a dual planar map `dualEmbedding`, and the induced
  deleted maps obtained by restricting both embeddings to chosen boundary-layer complements.
- `core/canonical`: `TwoComplex.TwoManifoldEmbedding.IsDualMap` is the chapter owner for dual
  planar maps, while `TwoComplex.Duality` is the underlying owner for the ambient vertex-face-edge
  duality data.
- `bridge/view`: `TwoComplex.Subcomplex.IsBoundaryLayerComplement` records that `S` is exactly the
  carried complement of the deleted boundary layer, while
  `TwoComplex.TwoManifoldEmbedding.restrictToSubcomplex` is the canonical bridge to the induced
  submap, and `TwoComplex.TwoManifoldEmbedding.boundaryLayerRemoval_preservesDuality` is the
  canonical restricted-duality construction on the deleted maps.

Domain sampling:
1. `TwoComplex.TwoManifoldEmbedding.IsDualMap` from `Corollary_5_7_3` is the best owner
   abstraction for the source claim that one planar map is dual to another.
2. `TwoComplex.Subcomplex.IsBoundaryLayerComplement` from `Corollary_5_7_3` is the chapter owner
   for the carried subcomplex left after deleting the boundary layer.
3. `TwoComplex.TwoManifoldEmbedding.restrictToSubcomplex` from `Definition_5_1_1` is the canonical
   bridge from a chosen carried subcomplex to the induced planar embedding on that submap.
4. `TwoComplex.TwoManifoldEmbedding.boundaryLayerRemoval_preservesDuality` from
   `Corollary_5_7_3` is the upstream owner construction for the restricted duality on the two
   deleted maps, so this file should reuse that data instead of keeping an existential wrapper.

Primitive vs. derived:
- primitive public data: the planar embeddings `embedding` and `dualEmbedding`, the chosen
  boundary-layer complements `S` and `SStar`, and the source duality/removal hypotheses;
- derived API: the direct `IsDualMap` witness for the two induced deleted maps, built from the
  canonical restricted `TwoComplex.Duality`.
-/

namespace TwoComplex
namespace TwoManifoldEmbedding

section

variable {C K : TwoComplex}
variable (embedding : TwoManifoldEmbedding C 𝔼²) (dualEmbedding : TwoManifoldEmbedding K 𝔼²)
variable (hdual : embedding.IsDualMap dualEmbedding)
variable (S : Subcomplex C) (hS : S.IsBoundaryLayerComplement embedding)
variable (SStar : Subcomplex K) (hSStar : SStar.IsBoundaryLayerComplement dualEmbedding)

/- Lemma 5-7-2: deleting the boundary layers on both sides of a dual pair yields deleted maps
that are again dual.

`Corollary_5_7_3` already provides the exact source-facing deleted-map witness with the canonical
owner abstraction and without an existential wrapper, so this file keeps only a direct recall of
that declaration instead of a parallel local copy. -/
#check
  (boundaryLayerRemoval_preservesDuality embedding dualEmbedding hdual S hS SStar hSStar :
    (embedding.restrictToSubcomplex S).IsDualMap
      (dualEmbedding.restrictToSubcomplex SStar))

end

end TwoManifoldEmbedding
end TwoComplex
