/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_2_1
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_2_2
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_2_3
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_2_5
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_2_7
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_2_8
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_1_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

set_option autoImplicit false

noncomputable section

open FreeGroupBasis OneComplex

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

section

variable {X : Type u} {F : Type v} [Group F]

local instance instDecidableEqX_5_2_9 : DecidableEq X := Classical.decEq X

/-!
Primary domain: small-cancellation estimates for region degrees and interior vertex degrees in a
reduced planar `R`-diagram.

Layer triage:
- `source-facing`: a relator set `R`, a reduced `R`-diagram `M`, and the region and
  interior-vertex degree bounds implied by the small-cancellation hypotheses `C(k)` and `T(m)`.
- `core/canonical`: `GroupDiagram.IsRDiagram` and `GroupDiagram.IsReduced` are the chapter owners
  for the two parts of “reduced `R`-diagram”, `FreeGroupBasis.condition_c` and
  `FreeGroupBasis.condition_t` are the owners for the small-cancellation hypotheses,
  `GroupPresentation.symmetrizedRelatorFamily` is the owner for the symmetrized relator family
  already built into `C(k)[basis, R]`, and `TwoComplex.regionDegree` /
  `OneComplex.vertexDegree` are the owners for the degrees.
- `bridge/view`: `TwoComplex.boundaryGeometricEdges` is the source-facing boundary-edge incidence
  API for a region, while `TwoComplex.TwoManifoldEmbedding.IsInteriorEdge` and
  `TwoComplex.TwoManifoldEmbedding.IsInteriorVertex` express the textbook boundary/interior language
  in the planar realization.

Domain sampling:
1. `GroupDiagram.IsRDiagram` from Definition `5-1-8` is the owner predicate for an `R`-diagram.
2. `GroupDiagram.IsReduced` from Definition `5-2-5` is the owner predicate for reducedness.
3. `FreeGroupBasis.condition_c` and `FreeGroupBasis.condition_t` from Definitions `5-2-2` and
   `5-2-3` are the owner predicates for the hypotheses `C(k)` and `T(m)`.
4. `TwoComplex.boundaryGeometricEdges`,
   `TwoComplex.TwoManifoldEmbedding.IsInteriorEdge` / `IsInteriorVertex`, and
   `TwoComplex.regionDegree` / `OneComplex.vertexDegree` from Definitions `5-2-7` and `5-2-8`
   are the owner APIs for the boundary/interior combinatorics and degrees used in the lemma.

Primitive vs. derived:
- primitive public data: a chosen basis `basis`, a relator set `R`, a diagram `M`, and a planar
  realization `embedding` of `M.source`;
- derived API: the chapter-owner predicates `M.IsRDiagram R` and `M.IsReduced`, the source-facing
  condition that a region boundary contains no boundary edge of the planar map, and the resulting
  lower bounds on region degree and interior vertex degree.
-/

section

variable (basis : FreeGroupBasis X F) {R : Set F} {M : GroupDiagram F}
variable (embedding : TwoComplex.TwoManifoldEmbedding M.source 𝔼²)
variable [embedding.IsPlanarMap]

-- Proof sketch: every edge in the boundary of `D` is interior, so reducedness forces the label on
-- each oriented boundary edge to be a piece. The boundary label of `D` is therefore a product of
-- `M.source.regionDegree D` pieces, and `C(k)` forbids such a factorization with fewer than `k`
-- pieces.
/-- Lemma 5-2-9 (1): if `R` satisfies `C(k)`, then every region of a
reduced `R`-diagram whose boundary contains no boundary edge of the ambient planar map has degree
at least `k`. -/
theorem regionDegree_ge_of_condition_c
    (hRDiagram : M.IsRDiagram R) (hReduced : M.IsReduced)
    {k : ℕ} (hck : C(k)[basis, R]) {D : TwoComplex.GeometricFace M.source}
    (hD :
      M.source.boundaryGeometricEdges D ⊆
        { e : OneComplex.GeometricEdge M.source.skeleton | embedding.IsInteriorEdge e }) :
    k ≤ M.source.regionDegree D := sorry

-- Proof sketch: read the region labels of the faces incident around the interior vertex `v` in
-- cyclic order. Reducedness prevents successive inverse pairs, so if `v` had degree `< m`, this
-- cyclic relator list would contradict `T(m)`.
/-- Lemma 5-2-9 (2): if `R` satisfies `T(m)`, then every interior vertex of a reduced
`R`-diagram has degree at least `m`. -/
theorem interiorVertexDegree_ge_of_condition_t
    (hRDiagram : M.IsRDiagram R) (hReduced : M.IsReduced)
    {m : ℕ} (htm : T(m)[basis, R]) {v : M.source.skeleton}
    (hv : embedding.IsInteriorVertex v) :
    m ≤
      @OneComplex.vertexDegree M.source.skeleton
        (TwoComplex.TwoManifoldEmbedding.finite_orientedEdge embedding) v := sorry

end

end
