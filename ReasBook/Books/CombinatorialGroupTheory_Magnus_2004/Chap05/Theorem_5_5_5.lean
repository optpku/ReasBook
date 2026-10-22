/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap05.Theorem_5_5_3

universe u v

set_option autoImplicit false

noncomputable section

open Quiver.Path FreeGroupBasis

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

section

variable {X : Type u} {F : Type v} [Group F]

/-!
Primary domain: annular small-cancellation `R`-diagrams in the conjugacy theorem.

Layer triage:
- `source-facing`: a reduced annular `R`-diagram with chosen outer and inner boundary cycles, the
  boundary-arc exclusion hypotheses on both boundary components, and the existence of one region
  meeting both boundary components.
- `core/canonical`: `GroupDiagram F` is the owner of the labelled diagram,
  `TwoComplex.TwoManifoldEmbedding M.source 𝔼²` with `IsPlanarMap` is the owner of the planar
  realization, `GroupDiagram.IsRDiagram` and `GroupDiagram.IsReduced` are the diagram hypotheses,
  `IsBoundaryCycle` is the owner of the chosen outer and inner boundary cycles,
  `BoundaryCycleIntersectionLongerThanHalfRelator`, `RegionMeetsBothBoundaryCycles`, and
  `HasAnnularBoundaryCycles` from Lemma `5-5-1` are the owner APIs for the boundary-arc
  exclusion, crossing-region, and annular-boundary data, and `boundaryInteriorEdgeCount` is the
  owner of the source quantity `i(D)`.
- `bridge/view`: `GroupDiagram.AnnularRDiagram` from Lemma `5-5-1` is the concrete `FreeGroup X`
  specialization of this owner package, so at the present basis-general level `F` the theorem
  should stay on the intrinsic owner data `embedding.HasAnnularBoundaryCycles σ τ` rather than
  introduce a second annular wrapper.
  No additional owner is needed here; the theorem should expose its two
  source conclusions directly in the owner APIs `RegionMeetsBothBoundaryCycles` and
  `boundaryInteriorEdgeCount`.

Domain sampling:
1. `TwoComplex.TwoManifoldEmbedding.IsBoundaryCycle` from Definition `5-4-2` is the chapter owner for
   the chosen boundary components `σ` and `τ`.
2. `GroupPresentation.HasLongSymmetrizedRelatorPart` from Proposition `3-11-2` is the canonical
   owner of the source phrase “`> 1 / 2 R`”.
3. `TwoComplex.TwoManifoldEmbedding.boundaryInteriorEdgeCount` from Definition `5-2-8` is the
   chapter owner for the interior-edge count `i(D)`.
4. `BoundaryCycleIntersectionLongerThanHalfRelator` and
   `RegionMeetsBothBoundaryCycles` from Theorem `5-5-3`, together with
   `HasAnnularBoundaryCycles` from Lemma `5-5-1`, already package the annular-boundary geometry
   needed here, so this file should reuse them rather than restating the same segment-level data.

Primitive vs. derived:
- primitive public data: the basis `basis`, relator set `R`, diagram `M`, planar embedding
  `embedding`, chosen boundary cycles `σ` and `τ`, the small-cancellation case, reducedness and
  `R`-diagram hypotheses, the two boundary-arc exclusion hypotheses, and one crossing region;
- derived API: the two atomic theorem-level consequences asserting that every region meets both
  boundary cycles and that every region has interior-edge count at most two.
-/

namespace TwoComplex
namespace TwoManifoldEmbedding

section

variable {M : GroupDiagram F}
variable (basis : FreeGroupBasis X F) (R : Set F) (embedding : TwoManifoldEmbedding M.source 𝔼²)
variable [embedding.IsPlanarMap] (σ τ : CyclicPath M.source.skeleton)
variable (hcase : C'((1 / 6 : ℝ))[basis, R] ∨ (C'((1 / 4 : ℝ))[basis, R] ∧ T(4)[basis, R]))
variable (hRDiagram : M.IsRDiagram R) (hReduced : M.IsReduced)
variable (hannular : embedding.HasAnnularBoundaryCycles σ τ)
variable
  (houter :
    ∀ D : GeometricFace M.source,
      ¬ embedding.BoundaryCycleIntersectionLongerThanHalfRelator basis R σ D)
  (hinner :
    ∀ D : GeometricFace M.source,
      ¬ embedding.BoundaryCycleIntersectionLongerThanHalfRelator basis R τ D)
  (hexists :
    ∃ E : GeometricFace M.source, RegionMeetsBothBoundaryCycles σ τ E)

-- Proof sketch: start with a region meeting both boundary components, cut the annular diagram
-- along a boundary-to-boundary segment of that region, and apply the curvature estimate from
-- Theorem `4-3` to the resulting disc. Greendlinger's lemma rules out the exceptional case, and
-- the remaining degree computation propagates outward through adjacent regions; if islands remain,
-- remove one and conclude by induction on the number of regions.
/-- Theorem 5-5-5: if `R` satisfies either `C'(1 / 6)` or `C'(1 / 4)` together with `T(4)`, and
`M` is a reduced annular `R`-diagram whose outer and inner boundary cycles satisfy the source
boundary-arc exclusion hypotheses, then the existence of one region meeting both boundary
components forces every region to meet both boundary cycles. -/
theorem all_regions_meet_both_boundary_cycles_of_exists_crossing_region
    (D : GeometricFace M.source) : RegionMeetsBothBoundaryCycles σ τ D := sorry

/-- Under the same hypotheses as Theorem `5-5-5`, every region of the annular diagram satisfies
`i(D) ≤ 2`. -/
theorem boundaryInteriorEdgeCount_le_two_of_exists_crossing_region
    (D : GeometricFace M.source) : embedding.boundaryInteriorEdgeCount D ≤ 2 := sorry

end

end TwoManifoldEmbedding
end TwoComplex

end
