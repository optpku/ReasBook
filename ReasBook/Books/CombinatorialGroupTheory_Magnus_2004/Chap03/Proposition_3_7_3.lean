/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_5_6
import CombinatorialGroupTheory_Magnus_2004.Chap03.Proposition_3_7_1

universe u v

set_option autoImplicit false

noncomputable section

local notation "𝔼²" => EuclideanSpace ℝ (Fin 2)

open TwoComplex

/-!
Primary domain: Fuchsian complexes and subgroup inheritance.

Layer triage:
- `source-facing`: a planar simply connected `2`-complex equipped with an action of the ambient
  group by complex automorphisms, and the statement that every subgroup admits a new Fuchsian
  complex whose faces are unions of faces of the original one.
- `core/canonical`: `FuchsianComplex` from Proposition `3-7-1` is the existing owner for the
  action of a group on a `2`-complex by automorphisms, while
  `Quiver.IsStronglyConnected (Quiver.Symmetrify _)`, `IsSimplyConnected`,
  `GeometricFace`, and `TwoManifoldEmbedding` are the owner predicates and constructions for the
  extra geometric hypotheses and geometric face images.
- `bridge/view`: the face-union conclusion is expressed directly by a chosen planar embedding of
  the fine complex and a compatible planar embedding of the coarse complex, together with the
  owner construction
  `TwoManifoldEmbedding.geometricFaceUnion`.

Domain sampling:
1. `FuchsianComplex` from Proposition `3-7-1` is the chapter owner for a group action on an
   actual `2`-complex by automorphisms.
2. `Quiver.IsStronglyConnected (Quiver.Symmetrify _)` and `IsSimplyConnected` are the owner
   predicates for the connectedness assumptions on the underlying complex.
3. `TwoManifoldEmbedding` from Proposition `3-5-6` is the owner abstraction for geometric
   realizations of faces in the plane, and `TwoManifoldEmbedding.geometricFaceUnion` is the owner
   for unions of geometric face images, so the face-union comparison should be stated in terms of
   actual embeddings rather than only the existential predicate `EmbedsInPlane`.
4. `Subgroup G` is mathlib's owner for the subgroup `H ≤ G`, and the subgroup type `H` inherits
   its canonical group structure automatically.

Primitive vs. derived:
- primitive data: the underlying `2`-complex and its action by automorphisms, already owned by
  `FuchsianComplex`, together with the chosen planar embedding of the original complex needed to
  state unions of geometric faces;
- derived API: the connected and simply connected hypotheses on that owner and the coarse complex,
  together with the compatible coarse planar embedding witnessing that each coarse geometric face
  is a union of geometric faces of the original complex.
-/

section

variable {G : Type u} [Group G]

/-- Proposition 3-7-3: if `K` is a Fuchsian complex for a group `G` and `H` is a subgroup of
`G`, then every chosen planar realization of `K` induces a Fuchsian complex `L` for `H` whose
geometric faces are unions of geometric faces of `K` in that realization. -/
-- Proof sketch: choose a maximal connected union `E` of faces of `K` that contains no two
-- distinct `H`-congruent faces. The standard Zorn-lemma argument in the text shows that every
-- geometric face of `K` is `H`-congruent to one in `E` and that `E` is simply connected. Taking
-- the translates `hE` as the faces of a new planar complex yields a Fuchsian complex for the
-- subgroup `H`, and each new geometric face is by construction a union of geometric faces of `K`.
theorem exists_faceUnionRefinement_fuchsianComplex_of_subgroup
    (K : FuchsianComplex G)
    (hconnected : Quiver.IsStronglyConnected (Quiver.Symmetrify K.complex.skeleton))
    (hsimply : IsSimplyConnected K.complex)
    (fineEmbedding : TwoManifoldEmbedding K.complex 𝔼²)
    (H : Subgroup G) :
    ∃ L : FuchsianComplex H,
      Quiver.IsStronglyConnected (Quiver.Symmetrify L.complex.skeleton) ∧
        IsSimplyConnected L.complex ∧
        ∃ coarseEmbedding : TwoManifoldEmbedding L.complex 𝔼²,
          ∀ D : GeometricFace L.complex,
            ∃ facePieces : Set (GeometricFace K.complex),
              coarseEmbedding.geometricFaceSet D =
                fineEmbedding.geometricFaceUnion facePieces :=
  sorry

end
