/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap01.Proposition_1_4_4
import AlgebraicTopology_May_1999.Chap02.Lemma_2_4_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory ContinuousMap CategoryTheory.Quotient

/-- Based homotopy relation on morphisms of based spaces, i.e. homotopy relative to the chosen
basepoint. -/
def basedHomotopyRel : HomRel (Under (⊤_ TopCat)) := fun X _ f g ↦
  Nonempty (HomotopyRel f.right.hom g.right.hom ({underTopBasepoint X} : Set X.right))

/-- Helper for Lemma 2.4.4: a homotopy relative to a singleton moves that point along the constant
path after transporting the endpoints to a common basepoint. -/
theorem homotopyRel_evalAt_singleton_cast_eq_refl
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} {x : X} {y : Y}
    (H : f.HomotopyRel g ({x} : Set X)) (hf : f x = y) (hg : g x = y) :
    (H.evalAt x).cast hf.symm hg.symm = Path.refl y := by
  -- The relative condition says the entire track of `x` stays at the initial endpoint.
  have hx : x ∈ ({x} : Set X) := by
    simp
  ext t
  simp [ContinuousMap.HomotopyRel.eq_fst, hx, hf]

/-- Helper for Lemma 2.4.4: if a homotopy is relative to a singleton, then the induced maps on
fundamental groups agree after identifying both endpoints with a common basepoint. -/
theorem fundamentalGroup_mapOfEq_eq_of_homotopyRel_singleton
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} {x : X} {y : Y}
    (H : f.HomotopyRel g ({x} : Set X)) (hf : f x = y) (hg : g x = y) :
    FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg := by
  -- First identify the track of the fixed point with the constant path at the chosen basepoint.
  have htrack : (H.evalAt x).cast hf.symm hg.symm = Path.refl y :=
    homotopyRel_evalAt_singleton_cast_eq_refl H hf hg
  let eP : FundamentalGroupoid.mk (f x) ≅ FundamentalGroupoid.mk (g x) :=
    (Groupoid.isoEquivHom _ _).symm ⟦H.evalAt x⟧
  let eHf : FundamentalGroupoid.mk (f x) ≅ FundamentalGroupoid.mk y :=
    eqToIso (congr_arg FundamentalGroupoid.mk hf)
  let eHg : FundamentalGroupoid.mk (g x) ≅ FundamentalGroupoid.mk y :=
    eqToIso (congr_arg FundamentalGroupoid.mk hg)
  -- The casted track is trivial, so composing the track with the endpoint identifications gives
  -- exactly the equality isomorphism from `f x` to `y`.
  have htrans_hom : eP.hom ≫ eHg.hom = eHf.hom := by
    have hcast_hom :
        eqToHom (congr_arg FundamentalGroupoid.mk hf.symm) ≫ eP.hom ≫ eHg.hom = 𝟙 _ := by
      simpa [eP, eHg, htrack] using
        (FundamentalGroupoid.conj_eqToHom (p := H.evalAt x) hf.symm hg.symm)
    simpa [eHf, Category.assoc] using
      congrArg (fun k ↦ eHf.hom ≫ k) hcast_hom
  have htrans_iso : eP ≪≫ eHg = eHf := by
    ext
    exact htrans_hom
  ext α
  -- Proposition 1.4.4 gives the homotopy-commutation relation before the endpoint transport.
  have hcomm : eP.conj (FundamentalGroup.map f x α) = FundamentalGroup.map g x α := by
    simpa [eP] using
      congrArg (fun k ↦ k α) (fundamental_group_map_homotopy_commutes f g H.toHomotopy x)
  -- Transporting that relation to the common basepoint turns it into equality of `mapOfEq`.
  have hconj :
      eHg.conj (eP.conj (FundamentalGroup.map f x α)) =
        eHf.conj (FundamentalGroup.map f x α) := by
    simpa [htrans_iso] using
      (eP.trans_conj eHg (FundamentalGroup.map f x α)).symm
  change eHf.conj (FundamentalGroup.map f x α) = eHg.conj (FundamentalGroup.map g x α)
  rw [← hconj, hcomm]

/-- Helper for Lemma 2.4.4: a based homotopy induces the same basepoint-preserving map on
fundamental groups. -/
theorem based_homotopy_mapOfEq_eq
    {X Y : Under (⊤_ TopCat)} {f g : X ⟶ Y} (H : basedHomotopyRel f g) :
    FundamentalGroup.mapOfEq f.right.hom (fundamentalGroupFunctorMap_basepoint f) =
      FundamentalGroup.mapOfEq g.right.hom (fundamentalGroupFunctorMap_basepoint g) := by
  -- Unpack the based homotopy and specialize the singleton-relative statement at the chosen
  -- basepoint.
  obtain ⟨Hfg⟩ := H
  exact fundamentalGroup_mapOfEq_eq_of_homotopyRel_singleton Hfg
    (fundamentalGroupFunctorMap_basepoint f) (fundamentalGroupFunctorMap_basepoint g)

/-- The fundamental-group functor sends based-homotopic maps to the same homomorphism. -/
-- Proof sketch: a based homotopy is fixed on the chosen basepoint, so the basepoint track in
-- Proposition 1.4.4 is the constant path. The resulting basepoint-change automorphism is the
-- identity, and the induced maps on fundamental groups therefore agree.
theorem fundamentalGroupFunctor_map_eq_of_based_homotopy
    {X Y : Under (⊤_ TopCat)} {f g : X ⟶ Y} (H : basedHomotopyRel f g) :
    fundamentalGroupFunctor.map f = fundamentalGroupFunctor.map g := by
  -- Rewrite the functorial morphisms into their `mapOfEq` descriptions and use the based-homotopy
  -- equality proved above.
  simpa [fundamentalGroupFunctor_map_eq] using
    congrArg GrpCat.ofHom (based_homotopy_mapOfEq_eq H)

/-- Lemma 2.4.4: the fundamental-group functor on based spaces is homotopy invariant and therefore
factors through the homotopy category of based spaces, realized as the quotient by based
homotopy. -/
def fundamentalGroupFunctorDesc : CategoryTheory.Quotient basedHomotopyRel ⥤ GrpCat :=
  lift basedHomotopyRel fundamentalGroupFunctor
    (fun _ _ _ _ h ↦ fundamentalGroupFunctor_map_eq_of_based_homotopy h)
