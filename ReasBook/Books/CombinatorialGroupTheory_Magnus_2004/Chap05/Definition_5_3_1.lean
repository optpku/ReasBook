/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap05.Definition_5_2_8

-- Declarations for this item will be appended below by the statement pipeline.

set_option autoImplicit false

noncomputable section

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: planar `(p, q)`-type degree conditions on finite planar maps.

Layer triage:
- `source-facing`: the textbook notions `[p, q]` and `(p, q)` for a planar map.
- `core/canonical`: `TwoComplex.TwoManifoldEmbedding.IsPlanarMap`,
  `TwoComplex.TwoManifoldEmbedding.IsInteriorVertex`,
  `TwoComplex.TwoManifoldEmbedding.IsInteriorRegion`,
  `OneComplex.vertexDegree`, and `TwoComplex.regionDegree`.
- `bridge/view`: the square-bracket notion implies the round-bracket notion by restricting the
  region lower bound from all regions to interior regions.

Domain sampling:
1. `TwoComplex.TwoManifoldEmbedding.IsPlanarMap` is the owner hypothesis for finite planar maps.
2. `TwoComplex.TwoManifoldEmbedding.IsInteriorVertex` is the owner predicate for interior vertices.
3. `TwoComplex.TwoManifoldEmbedding.IsInteriorRegion` is the owner predicate for interior regions.
4. `OneComplex.vertexDegree` and `TwoComplex.regionDegree` are nat-valued owner
   degree maps, so the `[p, q]` and `(p, q)` bounds should be stated directly in `ℕ`.

Primitive vs. derived:
- primitive data for a `[p, q]` map: nonempty support, an interior-vertex degree lower bound, and
  an all-region degree lower bound;
- primitive data for a `(p, q)` map: nonempty support, an interior-vertex degree lower bound, and
  an interior-region degree lower bound;
- derived API: every `[p, q]` map is canonically a `(p, q)` map.
-/

/-- Definition 5-3-1 (1): the positive integral solutions of `1 / p + 1 / q = 1 / 2` are exactly
`(3, 6)`, `(4, 4)`, and `(6, 3)`. -/
-- Proof sketch: clear denominators to rewrite the equation as `(p - 2) * (q - 2) = 4`, then
-- inspect the positive factorisations of `4`.
theorem positive_integral_reciprocal_sum_eq_half_iff
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    (1 : ℚ) / p + 1 / q = 1 / 2 ↔
      (p, q) = (3, 6) ∨ (p, q) = (4, 4) ∨ (p, q) = (6, 3) := sorry

namespace TwoComplex
namespace TwoManifoldEmbedding

section

variable {C : TwoComplex}

/-- Definition 5-3-1 (2): a `[p, q]` map is a nonempty planar map whose interior vertices have
degree at least `p` and whose regions all have degree at least `q`. -/
def IsSquareBracketPQMap (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap]
    (p q : ℕ) : Prop :=
  embedding.support.Nonempty ∧
    embedding.HasInteriorVertexDegreeAtLeast p ∧
    ∀ D : GeometricFace C, q ≤ C.regionDegree D

/-- Definition 5-3-1 (3): a `(p, q)` map is a nonempty planar map whose interior vertices have
degree at least `p` and whose interior regions have degree at least `q`. -/
def IsRoundBracketPQMap (embedding : TwoManifoldEmbedding C 𝔼²) [embedding.IsPlanarMap]
    (p q : ℕ) : Prop :=
  embedding.support.Nonempty ∧
    embedding.HasInteriorVertexDegreeAtLeast p ∧
    ∀ D : GeometricFace C, embedding.IsInteriorRegion D → q ≤ C.regionDegree D

end

end TwoManifoldEmbedding
end TwoComplex

/-- Source-facing notation for the textbook notion that `embedding` is a `[p, q]` map. -/
syntax:max term:max " Is[" term:max ", " term:max "]" : term

/-- Source-facing notation for the textbook notion that `embedding` is a `(p, q)` map. -/
syntax:max term:max " Is(" term:max ", " term:max ")" : term

macro_rules
  | `($embedding Is[$p, $q]) =>
      `(TwoComplex.TwoManifoldEmbedding.IsSquareBracketPQMap $embedding $p $q)
  | `($embedding Is($p, $q)) =>
      `(TwoComplex.TwoManifoldEmbedding.IsRoundBracketPQMap $embedding $p $q)

namespace TwoComplex
namespace TwoManifoldEmbedding

section

variable {C : TwoComplex}

namespace IsSquareBracketPQMap

/-- A `[p, q]` map has nonempty support. -/
theorem nonempty_support {embedding : TwoManifoldEmbedding C 𝔼²} [embedding.IsPlanarMap]
    {p q : ℕ} (h : embedding Is[p, q]) :
    embedding.support.Nonempty := by
  rcases h with ⟨hnonempty, -, -⟩
  exact hnonempty

/-- Every `[p, q]` map is a `(p, q)` map, since the square-bracket condition bounds the degree of
all regions in particular. -/
-- Proof sketch: reuse the nonemptiness and interior-vertex bounds, then restrict the region bound
-- from all regions to interior regions.
theorem toIsRoundBracketPQMap {embedding : TwoManifoldEmbedding C 𝔼²} [embedding.IsPlanarMap]
    {p q : ℕ} (h : embedding Is[p, q]) :
    embedding Is(p, q) := by
  rcases h with ⟨hnonempty, hvertex, hregion⟩
  exact ⟨hnonempty, hvertex, fun D _ ↦ hregion D⟩

end IsSquareBracketPQMap

namespace IsRoundBracketPQMap

/-- A `(p, q)` map has nonempty support. -/
theorem nonempty_support {embedding : TwoManifoldEmbedding C 𝔼²} [embedding.IsPlanarMap]
    {p q : ℕ} (h : embedding Is(p, q)) :
    embedding.support.Nonempty := by
  rcases h with ⟨hnonempty, -, -⟩
  exact hnonempty

end IsRoundBracketPQMap

/-- A `[p, q]` map has nonempty support. -/
instance {embedding : TwoManifoldEmbedding C 𝔼²} [embedding.IsPlanarMap] {p q : ℕ}
    (h : embedding Is[p, q]) : embedding.support.Nonempty :=
  h.nonempty_support

/-- A `(p, q)` map has nonempty support. -/
instance {embedding : TwoManifoldEmbedding C 𝔼²} [embedding.IsPlanarMap] {p q : ℕ}
    (h : embedding Is(p, q)) : embedding.support.Nonempty :=
  h.nonempty_support

/-- A `[p, q]` map is canonically a `(p, q)` map. -/
instance {embedding : TwoManifoldEmbedding C 𝔼²} [embedding.IsPlanarMap] {p q : ℕ}
    (h : embedding Is[p, q]) : embedding Is(p, q) :=
  h.toIsRoundBracketPQMap

end

end TwoManifoldEmbedding
end TwoComplex
