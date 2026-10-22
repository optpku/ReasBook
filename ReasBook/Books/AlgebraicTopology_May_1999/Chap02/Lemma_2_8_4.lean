/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap02.Lemma_2_4_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped FundamentalGroupoid

noncomputable section

/-- Helper for Lemma 2.8.4: the unit equality for the reversed product equivalence of
fundamental groupoids. -/
theorem product_fundamental_groupoid_equivalence_unit_eq (X Y : Under (⊤_ TopCat)) :
    𝟭 (πₓ (TopCat.of (X.right × Y.right))) =
      (FundamentalGroupoidFunctor.prodIso X.right Y.right).inv ⋙
        (FundamentalGroupoidFunctor.prodIso X.right Y.right).hom := by
  -- Reverse the original triangle identity so it matches the swapped equivalence data.
  simpa using
    (FundamentalGroupoidFunctor.prodIso X.right Y.right).inv_hom_id.symm

/-- Helper for Lemma 2.8.4: the counit equality for the reversed product equivalence of
fundamental groupoids. -/
theorem product_fundamental_groupoid_equivalence_counit_eq (X Y : Under (⊤_ TopCat)) :
    (FundamentalGroupoidFunctor.prodIso X.right Y.right).hom ⋙
        (FundamentalGroupoidFunctor.prodIso X.right Y.right).inv =
      𝟭 (Grpd.of (πₓ X.right × πₓ Y.right)) := by
  -- The second triangle identity is already oriented correctly for the reversed equivalence.
  simpa using
    (FundamentalGroupoidFunctor.prodIso X.right Y.right).hom_inv_id

/-- Helper for Lemma 2.8.4: the product groupoid isomorphism viewed in the direction needed for
the projection-induced map on fundamental groups. -/
noncomputable def product_fundamental_groupoid_equivalence (X Y : Under (⊤_ TopCat)) :
    πₓ (TopCat.of (X.right × Y.right)) ≌ Grpd.of (πₓ X.right × πₓ Y.right) :=
  CategoryTheory.Equivalence.mk
    (FundamentalGroupoidFunctor.prodIso X.right Y.right).inv
    (FundamentalGroupoidFunctor.prodIso X.right Y.right).hom
    (eqToIso (product_fundamental_groupoid_equivalence_unit_eq X Y))
    (eqToIso (product_fundamental_groupoid_equivalence_counit_eq X Y))

/-- Helper for Lemma 2.8.4: the projection maps induce the canonical product isomorphism on
fundamental groups. -/
-- Proof sketch: apply the canonical product isomorphism of fundamental groupoids
-- `FundamentalGroupoidFunctor.prodIso` at the object `(underTopBasepoint X, underTopBasepoint Y)`.
-- Its inverse is induced by the two projections, while its forward map pairs loops in `X` and `Y`
-- to a loop in `X × Y`, yielding inverse homomorphisms on automorphism groups.
noncomputable def fundamentalGroupMulEquivProd (X Y : Under (⊤_ TopCat)) :
    FundamentalGroup (TopCat.of (X.right × Y.right))
        (underTopBasepoint X, underTopBasepoint Y) ≃*
      (FundamentalGroup X.right (underTopBasepoint X) ×
        FundamentalGroup Y.right (underTopBasepoint Y)) :=
  let E : πₓ (TopCat.of (X.right × Y.right)) ≌ Grpd.of (πₓ X.right × πₓ Y.right) :=
    product_fundamental_groupoid_equivalence X Y
  -- Evaluate the reversed product equivalence on the chosen product basepoint.
  E.fullyFaithfulFunctor.mulEquivEnd
    (FundamentalGroupoid.mk (underTopBasepoint X, underTopBasepoint Y))

/-- Helper for Lemma 2.8.4: the underlying homomorphism of `fundamentalGroupMulEquivProd` is the
map induced by the two projections from `X × Y`. -/
@[simp] theorem fundamentalGroupMulEquivProd_toMonoidHom (X Y : Under (⊤_ TopCat)) :
    (fundamentalGroupMulEquivProd X Y).toMonoidHom =
      MonoidHom.prod
        (FundamentalGroup.map ContinuousMap.fst (underTopBasepoint X, underTopBasepoint Y))
        (FundamentalGroup.map ContinuousMap.snd (underTopBasepoint X, underTopBasepoint Y)) :=
  rfl

/-- Lemma 2.8.4: for based spaces `X` and `Y`, the projection-induced homomorphism
`π₁(X × Y) → π₁(X) × π₁(Y)` is an isomorphism. -/
theorem fundamental_group_product_isIso (X Y : Under (⊤_ TopCat)) :
    IsIso
      (GrpCat.ofHom
        (MonoidHom.prod
          (FundamentalGroup.map
            ContinuousMap.fst
            (underTopBasepoint X, underTopBasepoint Y))
          (FundamentalGroup.map
            ContinuousMap.snd
            (underTopBasepoint X, underTopBasepoint Y)))) := by
  -- Convert the multiplicative equivalence on vertex groups into an isomorphism in `GrpCat`.
  let i :
      GrpCat.of
          (FundamentalGroup (TopCat.of (X.right × Y.right))
            (underTopBasepoint X, underTopBasepoint Y)) ≅
        GrpCat.of
          (FundamentalGroup X.right (underTopBasepoint X) ×
            FundamentalGroup Y.right (underTopBasepoint Y)) :=
    (fundamentalGroupMulEquivProd X Y).toGrpIso
  -- The target map is exactly the hom underlying this canonical product isomorphism.
  simpa [MulEquiv.toGrpIso, fundamentalGroupMulEquivProd_toMonoidHom] using
    (i.isIso_hom : IsIso i.hom)
