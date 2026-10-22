/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap05.Corollary_5_3_5
import CombinatorialGroupTheory_Magnus_2004.Chap05.Corollary_5_7_3
import CombinatorialGroupTheory_Magnus_2004.Chap05.Lemma_5_6_1

set_option autoImplicit false

noncomputable section

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: boundary-layer peeling for planar small-cancellation maps.

Layer triage:
- `source-facing`: a `(q, p)` map `M`, the iterated sequence obtained by repeatedly deleting the
  boundary layer, and the resulting bound on the largest boundary complexity `β(Mᵢ)`.
- `core/canonical`: `TwoComplex.TwoManifoldEmbedding.IsRoundBracketPQMap` is the owner for `(q, p)`
  maps, `TwoComplex.TwoManifoldEmbedding.IsBoundaryLayerEdge` together with the interior predicates
  from Definition `5-2-7` are the owners for deleting a boundary layer, and
  `TwoComplex.TwoManifoldEmbedding.boundaryRegionAdjustedInteriorEdgeDefectSum`, with source-facing
  notation `σ'(M)[p, q]`, is the existing owner for the starred sum `σ'(M)`. The disc-or-annulus
  component hypothesis is owned by
  `TwoComplex.TwoManifoldEmbedding.HasSimplyConnectedOrAnnularComponents` from Lemma `5-6-1`.
- `bridge/view`: the source quantity `β(M)` is realized as the number of boundary regions, while
  the successive maps `M₀, ..., M_k` are represented by an inductive boundary-layer deletion
  sequence built from carried subcomplexes and their induced planar embeddings; the relation
  `TwoComplex.Subcomplex.IsBoundaryLayerComplement` is the thin bridge saying which subcomplex is
  kept at each step.

Domain sampling:
1. `TwoComplex.TwoManifoldEmbedding.boundaryRegionAdjustedInteriorEdgeDefectSum` from
   `Corollary_5_3_5`, with notation `σ'(M)[p, q]`, is the established owner for the source sum
   `σ'(M)`.
2. `TwoComplex.Subcomplex.IsBoundaryLayerComplement` from `Corollary_5_7_3` is the bridge/view
   predicate expressing that a chosen subcomplex is the complement of the boundary layer.
3. `TwoComplex.TwoManifoldEmbedding.HasSimplyConnectedOrAnnularComponents` from Lemma `5-6-1` is
   the chapter owner for the disc-or-annulus component hypothesis.
4. `TwoComplex.TwoManifoldEmbedding.IsRoundBracketPQMap` from `Definition_5_3_1` is the owner for
   the source `(q, p)` hypothesis.
-/

namespace TwoComplex
namespace TwoManifoldEmbedding

section

variable {C : TwoComplex}

/-- The source quantity `β(M)`, realized as the number of boundary regions of a finite planar
map and viewed in `ℚ`. -/
abbrev boundaryRegionCount (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap] : ℚ :=
  Nat.card { D : GeometricFace C // embedding.IsBoundaryRegion D }

/-- Source-facing notation for the textbook quantity `β(M)`. -/
syntax:max "β(" term:max ")" : term

macro_rules
  | `(β($embedding)) => `(TwoComplex.TwoManifoldEmbedding.boundaryRegionCount $embedding)

/-- A planar map is equal to its boundary layer when every vertex, geometric edge, and region is
already part of that boundary layer. -/
def BoundaryLayerEqualsMap (embedding : TwoManifoldEmbedding C 𝔼²) : Prop :=
  (∀ v : C.skeleton, ¬ embedding.IsInteriorVertex v) ∧
    (∀ e : OneComplex.GeometricEdge C.skeleton, embedding.IsBoundaryLayerEdge e) ∧
      ∀ D : GeometricFace C, ¬ embedding.IsInteriorRegion D

/-- A boundary-layer deletion sequence starts from a planar map and repeatedly replaces the
current map by the carried subcomplex obtained from it by deleting the boundary layer, stopping
when the final map is equal to its own boundary layer. -/
inductive BoundaryLayerDeletionSequence :
    {C : TwoComplex} → TwoManifoldEmbedding C 𝔼² → ℕ → Type _
  | terminal {C : TwoComplex} {embedding : TwoManifoldEmbedding C 𝔼²}
      (hterminal : embedding.BoundaryLayerEqualsMap) :
      BoundaryLayerDeletionSequence embedding 0
  | step {C : TwoComplex} {embedding : TwoManifoldEmbedding C 𝔼²} {k : ℕ}
      (S : Subcomplex C) (hS : S.IsBoundaryLayerComplement embedding)
      (tail : BoundaryLayerDeletionSequence (embedding.restrictToSubcomplex S) k) :
      BoundaryLayerDeletionSequence embedding (k + 1)

namespace BoundaryLayerDeletionSequence

/-- The maximum of the source quantities `β(Mᵢ)` along a boundary-layer deletion sequence,
realized as the maximum boundary-region count among its stages. -/
def maxBoundaryRegionCount
    {C : TwoComplex} {embedding : TwoManifoldEmbedding C 𝔼²} [embedding.IsPlanarMap] :
    {k : ℕ} → BoundaryLayerDeletionSequence embedding k → ℚ
  | _, .terminal _ => β(embedding)
  | _, .step _ _ tail => max (β(embedding)) tail.maxBoundaryRegionCount

end BoundaryLayerDeletionSequence

-- Proof sketch: first pass to a dual boundary-layer deletion sequence and use Corollary `5-7-3`
-- to keep duality after each peeling step. Lemma `5-7-1` gives monotonicity of the corresponding
-- dual boundary-vertex sum under each deletion, so the initial starred sum `σ'(M)` dominates the
-- starred sums of all later stages. Duality identifies `β(Mᵢ)` with the boundary-vertex count of
-- the dual stage, and the boundary-count estimate from Lemma `5-6-1` then yields the stated
-- factor `q / p`.
/-- Theorem 5-7-4: if `M` is a `(q, p)` map whose connected components are each simply connected
or annular, and `M = M₀, M₁, ..., M_k` is a sequence obtained by repeatedly deleting the boundary
layer until the last map is equal to its own boundary layer, then the maximum of the source
quantities `β(Mᵢ)` is bounded by `(q / p) σ'(M)`, represented here by
`((q : ℚ) / p) * σ'(embedding)[p, q]` for the initial map and by
`maxBoundaryRegionCount` for the boundary-layer deletion sequence. -/
theorem maxBoundaryRegionCount_le_scaled_sigmaPrime_of_boundaryLayerDeletionSequence
    (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap]
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hQP : embedding Is(q, p))
    (hreciprocal : (1 : ℚ) / p + 1 / q = 1 / 2)
    (hcomponents : embedding.HasSimplyConnectedOrAnnularComponents)
    {k : ℕ} (sequence : BoundaryLayerDeletionSequence embedding k) :
    sequence.maxBoundaryRegionCount ≤
      ((q : ℚ) / p) * σ'(embedding)[p, q] := sorry

end

end TwoManifoldEmbedding
end TwoComplex
