/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_7_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

set_option autoImplicit false

noncomputable section

namespace TwoComplex

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)
local notation "𝕊¹" => Metric.sphere (0 : 𝔼²) 1

/-!
Primary domain: planar embeddings of `2`-complexes and the area measure attached to an angle
measure.

Layer triage:
- `source-facing`: an ordered family of oriented faces whose nonempty prefix unions bound simple
  closed curves in a fixed planar embedding, together with the resulting area formula for the
  covered subcomplex.
- `core/canonical`: `TwoComplex.Subcomplex` is the owner for intrinsic subcomplex data,
  `TwoComplex.AngleMeasure` together with `AngleMeasure.associatedAreaMeasure` is the owner for
  area attached to subcomplexes, `Subcomplex.ContainsGeometricFace` is the canonical geometric-face
  view of a subcomplex, and `TwoComplex.TwoManifoldEmbedding.geometricFaceUnion` is the owner for
  the corresponding ambient planar image.
- `bridge/view`: the ordered list contributes canonical prefix subcomplexes inside `S`, while
  `TwoManifoldEmbedding.IsBoundedBySimpleClosedCurve` below is the source-facing simple-closed-
  curve predicate for the planar image of a subcomplex.

Domain sampling:
1. `TwoComplex.Subcomplex` from Proposition `3-3-5` is the chapter owner for the intrinsic
   `2`-dimensional object; this corollary should talk about `S : Subcomplex K`, not a local
   wrapper around its face data.
2. `TwoComplex.AngleMeasure.associatedAreaMeasure` from Proposition `3-7-5` is already the owner
   for the area of a subcomplex, so the main statement should use it directly.
3. `TwoComplex.TwoManifoldEmbedding.geometricFaceUnion` from Proposition `3-5-5`, together with
   `Subcomplex.ContainsGeometricFace` from Proposition `3-3-5`, is already the owner for the
   planar image of a subcomplex, so this file should not keep a parallel `subcomplexImage`
   definition.
4. `TwoComplex.GeometricFace` from Definition `3-2-4` is the owner for orientation-free faces,
   so the summand expression should use the canonical quotient notation rather than a verbose raw
   constructor term.

Primitive vs. derived:
- primitive data: the ambient complex `K`, its planar embedding `embedding`, the angle measure
  `α`, the target subcomplex `S`, and the ordered face list `faces`;
- derived API: the inverse-closed membership relation attached to `faces`, the canonical prefix
  subcomplexes inside `S`, their planar images in the embedding, and the resulting
  simple-closed-curve predicate.
-/

private def listedFaces {K : TwoComplex.{u}} (faces : List K.Face) : Set K.Face :=
  { D | ∃ E ∈ faces, D = E ∨ D = E⁻¹ }

private theorem listedFaces_inv_mem {K : TwoComplex.{u}} (faces : List K.Face) {D : K.Face} :
    D ∈ listedFaces faces → D⁻¹ ∈ listedFaces faces := by
  rintro ⟨E, hE, hD | hD⟩
  · refine ⟨E, hE, Or.inr ?_⟩
    simp [hD]
  · refine ⟨E, hE, Or.inl ?_⟩
    simpa [hD] using K.faceInv_involutive E

private theorem listedFaces_take_subset {K : TwoComplex.{u}} (faces : List K.Face) (i : ℕ) :
    listedFaces (faces.take i) ⊆ listedFaces faces := by
  intro D hD
  rcases hD with ⟨E, hE, hE'⟩
  exact ⟨E, List.mem_of_mem_take hE, hE'⟩

private theorem mem_faceSet_of_mem_list {K : TwoComplex.{u}} {S : Subcomplex K} {faces : List K.Face}
    (hfaces : ∀ D : K.Face, D ∈ S.faceSet ↔ ∃ E ∈ faces, D = E ∨ D = E⁻¹)
    {D : K.Face} (hD : D ∈ faces) :
    D ∈ S.faceSet :=
  (hfaces D).2 ⟨D, hD, Or.inl rfl⟩

namespace Subcomplex

/-- The prefix union of a listed family of faces, viewed as the canonical face-restriction of the
ambient subcomplex `S`. -/
def listedPrefixSubcomplex {K : TwoComplex.{u}} (S : Subcomplex K) (faces : List K.Face)
    (hfaces : ∀ D : K.Face, D ∈ S.faceSet ↔ ∃ E ∈ faces, D = E ∨ D = E⁻¹)
    (i : ℕ) : Subcomplex K :=
  S.restrictFaces
    (listedFaces (faces.take i))
    (fun D hD ↦
      (hfaces D).2 <| by
        simpa [listedFaces] using listedFaces_take_subset faces i hD)
    (fun {_} hD ↦ listedFaces_inv_mem (faces.take i) hD)

end Subcomplex

namespace TwoManifoldEmbedding

/-- A subcomplex is bounded by a simple closed curve when the frontier of its planar image is the
range of an injective continuous parametrization of the standard circle. The planar image is taken
through the canonical owner `embedding.geometricFaceUnion S.ContainsGeometricFace`. -/
def IsBoundedBySimpleClosedCurve
    {K : TwoComplex.{u}}
    (embedding : TwoManifoldEmbedding K 𝔼²) (S : Subcomplex K) : Prop :=
  ∃ γ : 𝕊¹ → 𝔼²,
    Continuous γ ∧ Function.Injective γ ∧
      frontier (embedding.geometricFaceUnion S.ContainsGeometricFace) = Set.range γ

end TwoManifoldEmbedding

/-- Corollary 3-7-6: if a subcomplex `S` of a planar complex `K` is the union of an ordered list
of faces `D₁, …, Dₙ`, every nonempty initial union `D₁ ∪ ⋯ ∪ Dᵢ` is bounded by a simple closed
curve in a chosen planar embedding, and `faceArea` records the associated area of each listed
geometric face via the canonical one-face subcomplexes of `S`, then `α(S)` is the sum of the
areas of the listed faces. -/
-- Proof sketch: induct on the list of faces. The simple-closed-boundary hypothesis identifies
-- each nonempty prefix union as a planar disc-like region, so adjoining the last face changes the
-- area by exactly the area of that face as identified by `hfaceArea`; iterating yields the
-- required finite sum formula.
theorem associatedAreaMeasure_subcomplex_eq_sum_faceAreas_of_prefix_simpleClosedBoundary
    (K : TwoComplex.{u})
    (embedding : TwoManifoldEmbedding K 𝔼²)
    (α : AngleMeasure K)
    (faceArea : GeometricFace K → ℝ)
    (S : Subcomplex K)
    (faces : List K.Face)
    (hcover : ∀ D : K.Face, D ∈ S.faceSet ↔ ∃ E ∈ faces, D = E ∨ D = E⁻¹)
    (hpairwise : faces.Pairwise fun D E ↦ D ≠ E ∧ D ≠ E⁻¹)
    (hprefix :
      ∀ i : ℕ, 1 ≤ i → i ≤ faces.length →
        embedding.IsBoundedBySimpleClosedCurve (S.listedPrefixSubcomplex faces hcover i))
    (hfaceArea :
      ∀ (D : K.Face) (hD : D ∈ faces),
        α.associatedAreaMeasure (S.restrictFace D (mem_faceSet_of_mem_list hcover hD)) =
          faceArea (⟦D⟧ : GeometricFace K)) :
    α.associatedAreaMeasure S =
      (faces.map fun D ↦ faceArea (⟦D⟧ : GeometricFace K)).sum := sorry

end TwoComplex
