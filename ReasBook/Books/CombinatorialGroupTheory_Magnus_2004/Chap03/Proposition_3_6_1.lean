/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_5_6

universe u v w

set_option autoImplicit false

noncomputable section

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

/-!
Primary domain: planar Cayley complexes and their left-translation automorphisms.

Layer triage:
- `source-facing`: a planar Cayley complex `C(X; R)` realized as an actual `TwoComplex`, together
  with the nontrivial automorphism induced by left multiplication by `g ≠ 1`; for the fixed-point
  part, also a chosen planar embedding together with an ambient homeomorphism of `ℝ²`
  realizing that automorphism on geometric face images.
- `core/canonical`: `CayleyComplex.Coordinates` is the chapter owner for the Cayley-complex
  realization, `OneComplex.GeometricEdge` and `TwoComplex.GeometricFace` are the owners for
  unoriented cells, `TwoComplex.Aut` is the owner for automorphisms together with their induced
  geometric-edge and geometric-face permutations, while `TwoComplex.TwoManifoldEmbedding` is the
  owner for a chosen planar realization.
- `bridge/view`: `TwoComplex.TwoManifoldEmbedding.geometricFaceSet`,
  `TwoComplex.TwoManifoldEmbedding.geometricFaceUnion`, and
  `TwoComplex.TwoManifoldEmbedding.RealizesAutomorphism` express the passage from the
  combinatorial automorphism to the ambient plane homeomorphism acting on the geometric images of
  faces.

Domain sampling:
1. `CayleyComplex.Coordinates` from Proposition `3-4-1` is the owner abstraction for actual
   Cayley complexes with their canonical left translations.
2. `OneComplex.GeometricEdge` from Definition `3-2-1` is the owner abstraction for actual edges
   modulo reversal.
3. `TwoComplex.GeometricFace` from Definition `3-2-4` is the owner abstraction for geometric
   faces modulo reversal.
4. `TwoComplex.Aut` from Proposition `3-4-1` is the owner abstraction for genuine automorphisms
   of a `2`-complex and their induced geometric-edge and geometric-face permutations.
5. `TwoComplex.TwoManifoldEmbedding` from Proposition `3-5-5`, specialized to `𝔼²` through
   Proposition `3-5-6`, is the owner abstraction for a chosen planar geometric realization.
6. `Homeomorph 𝔼² 𝔼²` is mathlib's canonical owner for the ambient planar self-map needed by the
   fixed-point clause.

Primitive vs. derived:
- primitive data: the actual Cayley complex `C`, its Cayley coordinates, the chosen nontrivial
  left translation, the chosen planar embedding, and the ambient plane homeomorphism realizing the
  automorphism on geometric face images;
- derived API: the induced action on oriented edges, the induced action on geometric faces, the
  geometric images of geometric faces in the plane, and the fixed-point conclusion for an
  invariant finite geometric-face union.
-/

namespace CayleyComplex.Coordinates

variable {G : Type u} [Group G]
variable {Y : Type v} {Rel : Type w}
variable {C : TwoComplex} {edgeLabel : Y → G}

local notation "GeometricEdge" => OneComplex.GeometricEdge C.skeleton

/-- Proposition 3-6-1 (1): a nontrivial left-translation automorphism of a Cayley complex fixes
no vertex. -/
-- Proof sketch: in Cayley coordinates, left translation by `g` sends the vertex `h` to `g * h`.
-- If this were equal to `h`, left cancellation would force `g = 1`, contradicting the
-- hypothesis.
theorem leftTranslation_fixes_no_vertex
    (coords : Coordinates C edgeLabel Rel) {g : G} (hg : g ≠ 1)
    (v : C.skeleton) :
    (coords.leftTranslation g).vertexPerm v ≠ v := by
  intro hfix
  have hcoord : g * coords.vertexEquiv v = coords.vertexEquiv v := by
    simpa [coords.vertexPerm_apply, hfix] using
      (coords.leftTranslation_vertexPerm_apply g (coords.vertexEquiv v)).symm
  have hg' : g = 1 := by
    have hcoord' : g * coords.vertexEquiv v = 1 * coords.vertexEquiv v := by
      simpa using hcoord
    exact mul_right_cancel hcoord'
  exact hg hg'

/-- A nontrivial left-translation automorphism of a Cayley complex fixes no oriented edge. -/
-- Proof sketch: in Cayley coordinates, left translation sends the oriented edge `(h, y)` to
-- `(g * h, y)`. Equality with the original oriented edge therefore forces `g * h = h`, and left
-- cancellation gives `g = 1`, contradicting the hypothesis.
theorem leftTranslation_fixes_no_orientedEdge
    (coords : Coordinates C edgeLabel Rel) {g : G} (hg : g ≠ 1)
    (e : C.skeleton.Edge) :
    (coords.leftTranslation g).edgePerm e ≠ e := by
  intro hfix
  have hcoord : (g * (coords.edgeEquiv e).1, (coords.edgeEquiv e).2) = coords.edgeEquiv e := by
    simpa [coords.edgePerm_apply, hfix] using
      (coords.leftTranslation_edgePerm_apply g (coords.edgeEquiv e)).symm
  have hfst : g * (coords.edgeEquiv e).1 = (coords.edgeEquiv e).1 :=
    congrArg Prod.fst hcoord
  have hg' : g = 1 := by
    have hfst' : g * (coords.edgeEquiv e).1 = 1 * (coords.edgeEquiv e).1 := by
      simpa using hfst
    exact mul_right_cancel hfst'
  exact hg hg'

/-- Proposition 3-6-1 (2): if the edge-label involution has no fixed points, then a nontrivial
left-translation automorphism of a Cayley complex fixes no geometric edge. -/
-- Proof sketch: if a geometric edge were fixed, some oriented representative would be sent either
-- to itself or to its reverse. The first case is impossible by the oriented-edge argument above.
-- In the second case, the coordinate formula for edge reversal forces the label coordinate `y` to
-- satisfy `labelInv y = y`, contradicting the fixed-point-free label-involution hypothesis.
theorem leftTranslation_fixes_no_edge
    (coords : Coordinates C edgeLabel Rel)
    (hlabelInv : ∀ y : Y, coords.labelInv y ≠ y)
    {g : G} (hg : g ≠ 1)
    (e : GeometricEdge) :
    (coords.leftTranslation g).geometricEdgePerm e ≠ e := by
  refine Quotient.inductionOn e ?_
  intro e hfix
  rcases Quotient.exact hfix with hfix | hfix
  · exact (coords.leftTranslation_fixes_no_orientedEdge hg e) hfix
  · have hcoord : (g * (coords.edgeEquiv e).1, (coords.edgeEquiv e).2) = coords.edgeEquiv e⁻¹ := by
      simpa [coords.edgePerm_apply, hfix] using
        (coords.leftTranslation_edgePerm_apply g (coords.edgeEquiv e)).symm
    have hy : (coords.edgeEquiv e).2 = coords.labelInv (coords.edgeEquiv e).2 := by
      simpa [coords.edgeInv_apply] using congrArg Prod.snd hcoord
    exact hlabelInv _ hy.symm

/-- Proposition 3-6-1 (3): if a nontrivial left-translation automorphism of a planar Cayley
complex fixes no geometric edge, is realized by an ambient homeomorphism of `ℝ²`, and leaves
invariant a nonempty finite union of geometric-face images, then that ambient homeomorphism has a
unique fixed point in that union. -/
-- Proof sketch: pass to an invariant finite planar disc containing the given union of face
-- images and argue by induction on the number of faces. The boundary analysis in the textbook
-- either removes a full orbit of boundary faces or cuts out a smaller invariant disc, eventually
-- forcing a unique fixed point of the ambient planar homeomorphism; the no-fixed-geometric-edge
-- hypothesis rules out boundary fixed segments during the induction.
theorem existsUnique_fixedPoint_of_invariant_finite_geometricFaceUnion
    (coords : Coordinates C edgeLabel Rel)
    (embedding : TwoComplex.TwoManifoldEmbedding C 𝔼²)
    {g : G} (hg : g ≠ 1)
    (hedge : ∀ e : GeometricEdge, (coords.leftTranslation g).geometricEdgePerm e ≠ e)
    (φ : Homeomorph 𝔼² 𝔼²)
    (hφ : embedding.RealizesAutomorphism (coords.leftTranslation g) φ)
    (faceUnion : Set (TwoComplex.GeometricFace C))
    (hnonempty : faceUnion.Nonempty) (hfinite : faceUnion.Finite)
    (hinv : φ '' embedding.geometricFaceUnion faceUnion = embedding.geometricFaceUnion faceUnion) :
    ∃! x : 𝔼², x ∈ embedding.geometricFaceUnion faceUnion ∧ φ x = x := sorry

end CayleyComplex.Coordinates
